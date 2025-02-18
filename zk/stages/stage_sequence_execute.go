package stages

import (
	"context"
	"errors"
	"fmt"
	"strconv"
	"time"

	"github.com/ledgerwatch/erigon-lib/common"
	"github.com/ledgerwatch/log/v3"

	"github.com/ledgerwatch/erigon/core"
	"github.com/ledgerwatch/erigon/core/rawdb"
	"github.com/ledgerwatch/erigon/core/state"
	"github.com/ledgerwatch/erigon/core/types"
	"github.com/ledgerwatch/erigon/eth/stagedsync"
	"github.com/ledgerwatch/erigon/eth/stagedsync/stages"
	"github.com/ledgerwatch/erigon/zk"
	"github.com/ledgerwatch/erigon/zk/metrics"
	zktx "github.com/ledgerwatch/erigon/zk/tx"
	"github.com/ledgerwatch/erigon/zk/utils"
)

var shouldCheckForExecutionAndDataStreamAlignment = true

func SpawnSequencingStage(
	s *stagedsync.StageState,
	u stagedsync.Unwinder,
	ctx context.Context,
	cfg SequenceBlockCfg,
	historyCfg stagedsync.HistoryCfg,
	quiet bool,
) (err error) {
	roTx, err := cfg.db.BeginRo(ctx)
	if err != nil {
		return err
	}
	defer roTx.Rollback()

	lastBatch, err := stages.GetStageProgress(roTx, stages.HighestSeenBatchNumber)
	if err != nil {
		return err
	}

	highestBatchInDs, err := cfg.dataStreamServer.GetHighestBatchNumber()
	if err != nil {
		return err
	}

	if lastBatch < highestBatchInDs {
		return resequence(s, u, ctx, cfg, historyCfg, lastBatch, highestBatchInDs)
	}

	if cfg.zk.SequencerResequence {
		log.Info(fmt.Sprintf("[%s] Resequencing completed. Please restart sequencer without resequence flag.", s.LogPrefix()))
		time.Sleep(10 * time.Minute)
		return nil
	}

	return sequencingBatchStep(s, u, ctx, cfg, historyCfg, nil)
}

func sequencingBatchStep(
	s *stagedsync.StageState,
	u stagedsync.Unwinder,
	ctx context.Context,
	cfg SequenceBlockCfg,
	historyCfg stagedsync.HistoryCfg,
	resequenceBatchJob *ResequenceBatchJob,
) (err error) {
	logPrefix := s.LogPrefix()
	log.Info(fmt.Sprintf("[%s] Starting sequencing stage", logPrefix))
	defer log.Info(fmt.Sprintf("[%s] Finished sequencing stage", logPrefix))

	// For X Layer metrics
	log.Info("[PoolTxCount] Starting Getting Pending Tx Count")
	pending, basefee, queued := cfg.txPool.CountContent()
	metrics.AddPoolTxCount(pending, basefee, queued)

	// at this point of time the datastream could not be ahead of the executor
	if err = validateIfDatastreamIsAheadOfExecution(s, ctx, cfg); err != nil {
		return err
	}

	sdb, err := newStageDb(ctx, cfg.db)
	if err != nil {
		return err
	}
	defer sdb.tx.Rollback()

	if err = cfg.infoTreeUpdater.WarmUp(sdb.tx); err != nil {
		return err
	}

	executionAt, err := s.ExecutionAt(sdb.tx)
	if err != nil {
		return err
	}

	lastBatch, err := stages.GetStageProgress(sdb.tx, stages.HighestSeenBatchNumber)
	if err != nil {
		return err
	}

	forkId, err := prepareForkId(lastBatch, executionAt, sdb.hermezDb)
	if err != nil {
		return err
	}

	// stage loop should continue until we get the forkid from the L1 in a finalised block
	if forkId == 0 {
		log.Warn(fmt.Sprintf("[%s] ForkId is 0. Waiting for L1 to finalise a block...", logPrefix))
		time.Sleep(10 * time.Second)
		return nil
	}

	batchNumberForStateInitialization, err := prepareBatchNumber(sdb, forkId, lastBatch, cfg.zk.L1SyncStartBlock > 0)
	if err != nil {
		return err
	}

	var block *types.Block
	runLoopBlocks := true
	batchContext := newBatchContext(ctx, &cfg, &historyCfg, s, sdb)
	batchState := newBatchState(forkId, batchNumberForStateInitialization, executionAt+1, cfg.zk.HasExecutors(), cfg.zk.L1SyncStartBlock > 0, cfg.txPool, resequenceBatchJob)
	blockDataSizeChecker := NewBlockDataChecker(cfg.zk.ShouldCountersBeUnlimited(batchState.isL1Recovery()))
	streamWriter := newSequencerBatchStreamWriter(batchContext, batchState)

	// injected batch
	if executionAt == 0 {
		if err = processInjectedInitialBatch(batchContext, batchState); err != nil {
			return err
		}

		if err = cfg.dataStreamServer.WriteWholeBatchToStream(logPrefix, sdb.tx, sdb.hermezDb.HermezDbReader, lastBatch, injectedBatchBatchNumber); err != nil {
			return err
		}
		if err = stages.SaveStageProgress(sdb.tx, stages.DataStream, 1); err != nil {
			return err
		}

		return sdb.tx.Commit()
	}

	if shouldCheckForExecutionAndDataStreamAlignment {
		// handle cases where the last batch wasn't committed to the data stream.
		// this could occur because we're migrating from an RPC node to a sequencer
		// or because the sequencer was restarted and not all processes completed (like waiting from remote executor)
		// we consider the data stream as verified by the executor so treat it as "safe" and unwind blocks beyond there
		// if we identify any.  During normal operation this function will simply check and move on without performing
		// any action.
		if !batchState.isAnyRecovery() {
			isUnwinding, err := alignExecutionToDatastream(batchContext, executionAt, u)
			if err != nil {
				// do not set shouldCheckForExecutionAndDataStreamAlighment=false because of the error
				return err
			}
			if isUnwinding {
				err = sdb.tx.Commit()
				if err != nil {
					// do not set shouldCheckForExecutionAndDataStreamAlighment=false because of the error
					return err
				}
				shouldCheckForExecutionAndDataStreamAlignment = false
				return nil
			}
		}
		shouldCheckForExecutionAndDataStreamAlignment = false
	}

	needsUnwind, err := tryHaltSequencer(batchContext, batchState, streamWriter, u, executionAt)
	if needsUnwind || err != nil {
		return err
	}

	if err := utils.UpdateZkEVMBlockCfg(cfg.chainConfig, sdb.hermezDb, logPrefix); err != nil {
		return err
	}

	batchCounters, err := prepareBatchCounters(batchContext, batchState)
	if err != nil {
		return err
	}

	if batchState.isL1Recovery() {
		if cfg.zk.L1SyncStopBatch > 0 && batchState.batchNumber > cfg.zk.L1SyncStopBatch {
			log.Info(fmt.Sprintf("[%s] L1 recovery has completed!", logPrefix), "batch", batchState.batchNumber)
			time.Sleep(1 * time.Second)
			return nil
		}

		log.Info(fmt.Sprintf("[%s] L1 recovery beginning for batch", logPrefix), "batch", batchState.batchNumber)

		// let's check if we have any L1 data to recover
		if err = batchState.batchL1RecoveryData.loadBatchData(sdb); err != nil {
			return err
		}

		if !batchState.batchL1RecoveryData.hasAnyDecodedBlocks() {
			log.Info(fmt.Sprintf("[%s] L1 recovery has completed!", logPrefix), "batch", batchState.batchNumber)
			time.Sleep(1 * time.Second)
			return nil
		}

		bad := false
		for _, batch := range cfg.zk.BadBatches {
			if batch == batchState.batchNumber {
				bad = true
				break
			}
		}

		// if we aren't forcing a bad batch then check it
		if !bad {
			bad, err = doCheckForBadBatch(batchContext, batchState, executionAt)
			if err != nil {
				return err
			}
		}

		if bad {
			return writeBadBatchDetails(batchContext, batchState, executionAt)
		}
	}

	batchTicker, logTicker, blockTicker, infoTreeTicker := prepareTickers(batchContext.cfg)
	defer batchTicker.Stop()
	defer logTicker.Stop()
	defer blockTicker.Stop()
	defer infoTreeTicker.Stop()

	log.Info(fmt.Sprintf("[%s] Starting batch %d...", logPrefix, batchState.batchNumber))

	// For X Layer
	var batchCloseReason metrics.BatchFinalizeType
	batchStart := time.Now()

	// once the batch ticker has ticked we need a signal to close the batch after the next block is done
	batchTimedOut := false

	for blockNumber := executionAt + 1; runLoopBlocks; blockNumber++ {
		// For X Layer
		metrics.GetLogStatistics().CumulativeCounting(metrics.BlockCounter)
		if batchTimedOut {
			log.Debug(fmt.Sprintf("[%s] Closing batch due to timeout", logPrefix))
			break
		}
		log.Info(fmt.Sprintf("[%s] Starting block %d (forkid %v)...", logPrefix, blockNumber, batchState.forkId))
		logTicker.Reset(10 * time.Second)
		blockTicker.Reset(cfg.zk.SequencerBlockSealTime)

		if batchState.isL1Recovery() {
			blockNumbersInBatchSoFar, err := batchContext.sdb.hermezDb.GetL2BlockNosByBatch(batchState.batchNumber)
			if err != nil {
				return err
			}

			didLoadedAnyDataForRecovery := batchState.loadBlockL1RecoveryData(uint64(len(blockNumbersInBatchSoFar)))
			if !didLoadedAnyDataForRecovery {
				log.Info(fmt.Sprintf("[%s] Block %d is not part of batch %d. Stopping blocks loop", logPrefix, blockNumber, batchState.batchNumber))
				break
			}
		}

		if batchState.isResequence() {
			if !batchState.resequenceBatchJob.HasMoreBlockToProcess() {
				for {
					if pending, _ := streamWriter.legacyVerifier.HasPendingVerifications(); pending {
						streamWriter.CommitNewUpdates()
						time.Sleep(1 * time.Second)
					} else {
						break
					}
				}

				runLoopBlocks = false
				break
			}
		}

		header, parentBlock, err := prepareHeader(sdb.tx, blockNumber-1, batchState.blockState.getDeltaTimestamp(), batchState.getBlockHeaderForcedTimestamp(), batchState.forkId, batchState.getCoinbase(&cfg), cfg.chainConfig, cfg.miningConfig)
		if err != nil {
			return err
		}

		if batchDataOverflow := blockDataSizeChecker.AddBlockStartData(); batchDataOverflow {
			log.Info(fmt.Sprintf("[%s] BatchL2Data limit reached. Stopping.", logPrefix), "blockNumber", blockNumber)
			break
		}

		// timer: evm + smt
		t := utils.StartTimer("stage_sequence_execute", "evm", "smt")

		infoTreeIndexProgress, l1TreeUpdate, l1TreeUpdateIndex, l1BlockHash, ger, shouldWriteGerToContract, err := prepareL1AndInfoTreeRelatedStuff(sdb, batchState, header.Time, cfg.zk.SequencerResequenceReuseL1InfoIndex)
		if err != nil {
			return err
		}

		overflowOnNewBlock, err := batchCounters.StartNewBlock(l1TreeUpdateIndex != 0)
		if err != nil {
			return err
		}
		if (!batchState.isAnyRecovery() || batchState.isResequence()) && overflowOnNewBlock {
			// For X Layer
			batchCloseReason = metrics.BatchCounterOverflow
			break
		}

		ibs := state.New(sdb.stateReader)
		getHashFn := core.GetHashFn(header, func(hash common.Hash, number uint64) *types.Header { return rawdb.ReadHeader(sdb.tx, hash, number) })
		coinbase := batchState.getCoinbase(&cfg)
		blockContext := core.NewEVMBlockContext(header, getHashFn, cfg.engine, &coinbase)
		batchState.blockState.builtBlockElements.resetBlockBuildingArrays()

		parentRoot := parentBlock.Root()
		if err = handleStateForNewBlockStarting(batchContext, ibs, blockNumber, batchState.batchNumber, header.Time, &parentRoot, l1TreeUpdate, shouldWriteGerToContract); err != nil {
			return err
		}

		// start waiting for a new transaction to arrive
		if !batchState.isAnyRecovery() {
			log.Info(fmt.Sprintf("[%s] Waiting for txs from the pool...", logPrefix))
		}

		innerBreak := false
		emptyBlockOverflow := false

	OuterLoopTransactions:
		for {
			if innerBreak {
				break
			}
			select {
			case <-logTicker.C:
				if !batchState.isAnyRecovery() {
					log.Info(fmt.Sprintf("[%s] Waiting some more for txs from the pool...", logPrefix))
				}
			case <-blockTicker.C:
				if !batchState.isAnyRecovery() {
					break OuterLoopTransactions
				}
			case <-batchTicker.C:
				if !batchState.isAnyRecovery() {
					log.Debug(fmt.Sprintf("[%s] Batch timeout reached", logPrefix))
					batchTimedOut = true
				}
			case <-infoTreeTicker.C:
				newLogs, err := cfg.infoTreeUpdater.CheckForInfoTreeUpdates(logPrefix, sdb.tx)
				if err != nil {
					return err
				}
				var latestIndex uint64
				latest := cfg.infoTreeUpdater.GetLatestUpdate()
				if latest != nil {
					latestIndex = latest.Index
				}
				log.Info(fmt.Sprintf("[%s] Info tree updates", logPrefix), "count", len(newLogs), "latestIndex", latestIndex)
			default:
				if batchState.isLimboRecovery() {
					batchState.blockState.transactionsForInclusion, err = getLimboTransaction(ctx, cfg, batchState.limboRecoveryData.limboTxHash, executionAt)
					if err != nil {
						return err
					}
				} else if batchState.isResequence() {
					batchState.blockState.transactionsForInclusion, err = batchState.resequenceBatchJob.YieldNextBlockTransactions(zktx.DecodeTx)
					if err != nil {
						return err
					}
				} else if !batchState.isL1Recovery() {

					var allConditionsOK bool
					var newTransactions []types.Transaction
					var newIds []common.Hash

					newTransactions, newIds, allConditionsOK, err = getNextPoolTransactions(ctx, cfg, executionAt, batchState.forkId, batchState.yieldedTransactions)
					if err != nil {
						return err
					}

					batchState.blockState.transactionsForInclusion = append(batchState.blockState.transactionsForInclusion, newTransactions...)
					for idx, tx := range newTransactions {
						batchState.blockState.transactionHashesToSlots[tx.Hash()] = newIds[idx]
					}

					if len(batchState.blockState.transactionsForInclusion) == 0 {
						if allConditionsOK {
							time.Sleep(batchContext.cfg.zk.SequencerTimeoutOnEmptyTxPool)
						} else {
							time.Sleep(batchContext.cfg.zk.SequencerTimeoutOnEmptyTxPool / 5) // we do not need to sleep too long for txpool not ready
						}
					} else {
						log.Trace(fmt.Sprintf("[%s] Yielded transactions from the pool", logPrefix), "txCount", len(batchState.blockState.transactionsForInclusion))
					}
				}

				start := time.Now()
				if len(batchState.blockState.transactionsForInclusion) == 0 {
					time.Sleep(batchContext.cfg.zk.SequencerTimeoutOnEmptyTxPool)
				} else {
					log.Trace(fmt.Sprintf("[%s] Yielded transactions from the pool", logPrefix), "txCount", len(batchState.blockState.transactionsForInclusion))
				}

				badTxHashes := make([]common.Hash, 0)
				minedTxHashes := make([]common.Hash, 0)

			InnerLoopTransactions:
				for i, transaction := range batchState.blockState.transactionsForInclusion {
					// quick check if we should stop handling transactions
					select {
					case <-blockTicker.C:
						if !batchState.isAnyRecovery() {
							innerBreak = true
							break InnerLoopTransactions
						}
					default:
					}

					txHash := transaction.Hash()
					effectiveGas := batchState.blockState.getL1EffectiveGases(cfg, i)

					// The copying of this structure is intentional
					backupDataSizeChecker := *blockDataSizeChecker
					receipt, execResult, anyOverflow, err := attemptAddTransaction(cfg, sdb, ibs, batchCounters, &blockContext, header, transaction, effectiveGas, batchState.isL1Recovery(), batchState.forkId, l1TreeUpdateIndex, &backupDataSizeChecker)
					if err != nil {
						if batchState.isLimboRecovery() {
							panic("limbo transaction has already been executed once so they must not fail while re-executing")
						}

						if batchState.isResequence() {
							if cfg.zk.SequencerResequenceStrict {
								return fmt.Errorf("strict mode enabled, but resequenced batch %d failed to add transaction %s: %v", batchState.batchNumber, txHash, err)
							} else {
								log.Warn(fmt.Sprintf("[%s] error adding transaction to batch during resequence: %v", logPrefix, err),
									"hash", txHash,
									"to", transaction.GetTo(),
								)
								continue
							}
						}

						// if we are in recovery just log the error as a warning.  If the data is on the L1 then we should consider it as confirmed.
						// The executor/prover would simply skip a TX with an invalid nonce for example so we don't need to worry about that here.
						if batchState.isL1Recovery() {
							log.Warn(fmt.Sprintf("[%s] error adding transaction to batch during recovery: %v", logPrefix, err),
								"hash", txHash,
								"to", transaction.GetTo(),
							)
							continue
						}

						if isOkKnownError(err) {
							// if this is a known error that could be caused by some edge case coming from the pool we want to warn
							// about it and continue on as normal but ensure we don't continue to keep trying to add this transaction
							// to the block
							log.Warn(fmt.Sprintf("[%s] known error adding transaction to block, skipping for now: %v", logPrefix, err),
								"hash", txHash)
							badTxHashes = append(badTxHashes, txHash)
						} else {
							// if we have an error at this point something has gone wrong, either in the pool or otherwise
							// to stop the pool growing and hampering further processing of good transactions here
							// we mark it for being discarded
							log.Warn(fmt.Sprintf("[%s] error adding transaction to batch, discarding from pool", logPrefix), "hash", txHash, "err", err)
							badTxHashes = append(badTxHashes, txHash)
							batchState.blockState.transactionsToDiscard = append(batchState.blockState.transactionsToDiscard, batchState.blockState.transactionHashesToSlots[txHash])
						}
					}

					switch anyOverflow {
					case overflowCounters:
						// remove the last attempted counters as we may want to continue processing this batch with other transactions
						batchCounters.RemovePreviousTransactionCounters()

						if batchState.isLimboRecovery() {
							panic("limbo transaction has already been executed once so they must not overflow counters while re-executing")
						}

						if !batchState.isL1Recovery() {
							/*
								There are two cases when overflow could occur.
								1. The block DOES not contain any transactions.
									In this case it means that a single tx overflow entire zk-counters.
									In this case we mark it so. Once marked it will be discarded from the tx-pool async (once the tx-pool process the creation of a new batch)
									Block production then continues as normal looking for more suitable transactions
									NB: The tx SHOULD not be removed from yielded set, because if removed, it will be picked again on next block. That's why there is i++. It ensures that removing from yielded will start after the problematic tx
								2. The block contains transactions.
									In this case we make note that we have had a transaction that overflowed and continue attempting to process transactions
									Once we reach the cap for these attempts we will stop producing blocks and consider the batch done
							*/
							if !batchState.hasAnyTransactionsInThisBatch && len(batchState.builtBlocks) == 0 {
								// mark the transaction to be removed from the pool
								cfg.txPool.MarkForDiscardFromPendingBest(txHash)
								log.Info(fmt.Sprintf("[%s] single transaction %s cannot fit into batch", logPrefix, txHash))
							} else {
								batchState.newOverflowTransaction()
								// batchCounters.
								transactionNotAddedText := fmt.Sprintf("[%s] transaction %s was not included in this batch because it overflowed.", logPrefix, txHash)
								ocs, _ := batchCounters.CounterStats(l1TreeUpdateIndex != 0)
								// was not included in this batch because it overflowed: counter x, counter y
								log.Info(transactionNotAddedText, "Counters context:", ocs, "overflow transactions", batchState.overflowTransactions)
								if batchState.reachedOverflowTransactionLimit() || cfg.zk.SealBatchImmediatelyOnOverflow {
									// For X Layer
									metrics.GetLogStatistics().CumulativeCounting(metrics.ZKOverflowBlockCounter)
									metrics.SeqZKOverflowBlockCounter.Inc()
									log.Info(fmt.Sprintf("[%s] closing batch due to counters", logPrefix), "counters: ", batchState.overflowTransactions, "immediate", cfg.zk.SealBatchImmediatelyOnOverflow)
									runLoopBlocks = false
									if len(batchState.blockState.builtBlockElements.transactions) == 0 {
										emptyBlockOverflow = true
									}
									break OuterLoopTransactions
								}
							}

							// continue on processing other transactions and skip this one
							continue
						}

						if batchState.isResequence() && cfg.zk.SequencerResequenceStrict {
							return fmt.Errorf("strict mode enabled, but resequenced batch %d overflowed counters on block %d", batchState.batchNumber, blockNumber)
						}
					case overflowGas:
						if batchState.isAnyRecovery() {
							panic(fmt.Sprintf("block gas limit overflow in recovery block: %d", blockNumber))
						}
						log.Info(fmt.Sprintf("[%s] gas overflowed adding transaction to block", logPrefix), "block", blockNumber, "tx-hash", txHash)
						runLoopBlocks = false
						break OuterLoopTransactions
					case overflowNone:
					}

					if err == nil {
						// For X Layer
						metrics.GetLogStatistics().CumulativeValue(metrics.BatchGas, int64(execResult.UsedGas))
						blockDataSizeChecker = &backupDataSizeChecker
						batchState.onAddedTransaction(transaction, receipt, execResult, effectiveGas)
						minedTxHashes = append(minedTxHashes, txHash)
					}

					// We will only update the processed index in resequence job if there isn't overflow
					if batchState.isResequence() {
						batchState.resequenceBatchJob.UpdateLastProcessedTx(txHash)
					}
				}

				if batchState.isResequence() {
					if len(batchState.blockState.transactionsForInclusion) == 0 {
						// We need to jump to the next block here if there are no transactions in current block
						batchState.resequenceBatchJob.UpdateLastProcessedTx(batchState.resequenceBatchJob.CurrentBlock().L2Blockhash)
						break OuterLoopTransactions
					}

					if batchState.resequenceBatchJob.AtNewBlockBoundary() {
						// We need to jump to the next block here if we are at the end of the current block
						break OuterLoopTransactions
					} else {
						if cfg.zk.SequencerResequenceStrict {
							return fmt.Errorf("strict mode enabled, but resequenced batch %d has transactions that overflowed counters or failed transactions", batchState.batchNumber)
						}
					}
				}

				// For X Layer
				metrics.GetLogStatistics().CumulativeTiming(metrics.ProcessingTxTiming, time.Since(start))
				metrics.SeqTxDuration.Observe(float64(time.Since(start).Milliseconds()))

				// remove bad and mined transactions from the list for inclusion
				for i := len(batchState.blockState.transactionsForInclusion) - 1; i >= 0; i-- {
					tx := batchState.blockState.transactionsForInclusion[i]
					hash := tx.Hash()
					for _, badHash := range badTxHashes {
						if badHash == hash {
							batchState.blockState.transactionsForInclusion = removeInclusionTransaction(batchState.blockState.transactionsForInclusion, i)
							break
						}
					}

					for _, minedHash := range minedTxHashes {
						if minedHash == hash {
							batchState.blockState.transactionsForInclusion = removeInclusionTransaction(batchState.blockState.transactionsForInclusion, i)
							break
						}
					}
				}

				if batchState.isL1Recovery() {
					// just go into the normal loop waiting for new transactions to signal that the recovery
					// has finished as far as it can go
					if !batchState.isThereAnyTransactionsToRecover() {
						log.Info(fmt.Sprintf("[%s] L1 recovery no more transactions to recover", logPrefix))
					}

					break OuterLoopTransactions
				}

				if batchState.isLimboRecovery() {
					batchCloseReason = metrics.BatchLimboRecovery
					runLoopBlocks = false
					break OuterLoopTransactions
				}
			}
		}

		// we do not want to commit this block if it has no transactions and we detected an overflow - essentially the batch is too
		// full to get any more transactions in it and we don't want to commit an empty block
		if emptyBlockOverflow {
			log.Info(fmt.Sprintf("[%s] Block %d overflow detected with no transactions added, skipping block for next batch", logPrefix, blockNumber))
			break
		}

		if block, err = doFinishBlockAndUpdateState(batchContext, ibs, header, parentBlock, batchState, ger, l1BlockHash, l1TreeUpdateIndex, infoTreeIndexProgress, batchCounters); err != nil {
			return err
		}

		if err := cfg.txPool.RemoveMinedTransactions(ctx, sdb.tx, header.GasLimit, batchState.blockState.builtBlockElements.txSlots); err != nil {
			return err
		}
		if err := cfg.txPool.RemoveMinedTransactions(ctx, sdb.tx, header.GasLimit, batchState.blockState.transactionsToDiscard); err != nil {
			return err
		}

		if batchState.isLimboRecovery() {
			stateRoot := block.Root()
			cfg.txPool.UpdateLimboRootByTxHash(batchState.limboRecoveryData.limboTxHash, &stateRoot)
			return fmt.Errorf("[%s] %w: %s = %s", s.LogPrefix(), zk.ErrLimboState, batchState.limboRecoveryData.limboTxHash.Hex(), stateRoot.Hex())
		}

		t.LogTimer()
		gasPerSecond := float64(0)
		elapsedSeconds := t.Elapsed().Seconds()
		if elapsedSeconds != 0 {
			gasPerSecond = float64(block.GasUsed()) / elapsedSeconds
		}
		metrics.SeqBlockGasUsed.Set(float64(block.GasUsed()))

		if gasPerSecond != 0 {
			log.Info(fmt.Sprintf("[%s] Finish block %d with %d transactions... (%d gas/s)", logPrefix, blockNumber, len(batchState.blockState.builtBlockElements.transactions), int(gasPerSecond)), "info-tree-index", infoTreeIndexProgress)
		} else {
			log.Info(fmt.Sprintf("[%s] Finish block %d with %d transactions...", logPrefix, blockNumber, len(batchState.blockState.builtBlockElements.transactions)), "info-tree-index", infoTreeIndexProgress)
		}

		// For X Layer
		// Count successful transactions
		metrics.SeqTxCount.Add(float64(len(batchState.blockState.builtBlockElements.transactions)))
		metrics.GetLogStatistics().CumulativeValue(metrics.TxCounter, int64(len(batchState.blockState.builtBlockElements.transactions)))

		// add a check to the verifier and also check for responses
		batchState.onBuiltBlock(blockNumber)

		start := time.Now()
		if !batchState.isL1Recovery() {
			// commit block data here so it is accessible in other threads
			if errCommitAndStart := sdb.CommitAndStart(); errCommitAndStart != nil {
				return errCommitAndStart
			}
			defer sdb.tx.Rollback()
		}
		metrics.GetLogStatistics().CumulativeTiming(metrics.BatchCommitDBTiming, time.Since(start))

		// do not use remote executor in l1recovery mode
		// if we need remote executor in l1 recovery then we must allow commit/start DB transactions
		useExecutorForVerification := !batchState.isL1Recovery() && batchState.hasExecutorForThisBatch
		counters, err := batchCounters.CombineCollectors(l1TreeUpdateIndex != 0)
		if err != nil {
			return err
		}
		cfg.legacyVerifier.StartAsyncVerification(batchContext.s.LogPrefix(), batchState.forkId, batchState.batchNumber, block.Root(), counters.UsedAsMap(), batchState.builtBlocks, useExecutorForVerification, batchContext.cfg.zk.SequencerBatchVerificationTimeout, batchContext.cfg.zk.SequencerBatchVerificationRetries)

		// check for new responses from the verifier
		needsUnwind, err := updateStreamAndCheckRollback(batchContext, batchState, streamWriter, u)

		// lets commit everything after updateStreamAndCheckRollback no matter of its result unless
		// we're in L1 recovery where losing some blocks on restart doesn't matter

		start = time.Now()
		if !batchState.isL1Recovery() {
			if errCommitAndStart := sdb.CommitAndStart(); errCommitAndStart != nil {
				return errCommitAndStart
			}
			defer sdb.tx.Rollback()
		}
		metrics.GetLogStatistics().CumulativeTiming(metrics.BatchCommitDBTiming, time.Since(start))

		// check the return values of updateStreamAndCheckRollback
		if err != nil || needsUnwind {
			return err
		}
	}

	/*
		if adding something below that line we must ensure
		- it is also handled property in processInjectedInitialBatch
		- it is also handled property in alignExecutionToDatastream
		- it is also handled property in doCheckForBadBatch
		- it is unwound correctly
	*/

	// TODO: It is 99% sure that there is no need to write this in any of processInjectedInitialBatch, alignExecutionToDatastream, doCheckForBadBatch but it is worth double checknig
	// the unwind of this value is handed by UnwindExecutionStageDbWrites
	if _, err := rawdb.IncrementStateVersionByBlockNumberIfNeeded(batchContext.sdb.tx, block.NumberU64()); err != nil {
		return fmt.Errorf("writing plain state version: %w", err)
	}

	log.Info(fmt.Sprintf("[%s] Finish batch %d...", batchContext.s.LogPrefix(), batchState.batchNumber))

	// For X Layer
	metrics.GetLogStatistics().SetTag(metrics.BatchCloseReason, string(batchCloseReason))
	metrics.GetLogStatistics().SetTag(metrics.FinalizeBatchNumber, strconv.Itoa(int(batchState.batchNumber)))
	tryToSleepSequencer(cfg.zk.XLayer.SequencerBatchSleepDuration, logPrefix)
	start := time.Now()
	err = sdb.tx.Commit()
	metrics.GetLogStatistics().CumulativeTiming(metrics.BatchCommitDBTiming, time.Since(start))

	batchTime := time.Since(batchStart)
	metrics.BatchExecuteTime(string(batchCloseReason), batchTime)
	metrics.GetLogStatistics().Summary()

	return err
}

func removeInclusionTransaction(orig []types.Transaction, index int) []types.Transaction {
	if index < 0 || index >= len(orig) {
		return orig
	}
	return append(orig[:index], orig[index+1:]...)
}

func isOkKnownError(err error) bool {
	return err == nil ||
		errors.Is(err, core.ErrNonceTooHigh)
}
