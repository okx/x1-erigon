package metrics

import (
	"time"
)

type logTag string

const (
	BlockCounter                  logTag = "BlockCounter"
	TxCounter                     logTag = "TxCounter"
	GetTxTiming                   logTag = "GetTxTiming"
	GetTxPauseCounter             logTag = "GetTxPauseCounter"
	GetTxPauseTiming              logTag = "GetTxPauseTiming"
	BatchCloseReason              logTag = "BatchCloseReason"
	ReprocessingTxCounter         logTag = "ReProcessingTxCounter"
	ZKOverflowBlockCounter        logTag = "ZKOverflowBlockCounter"
	FailTxGasOverCounter          logTag = "FailTxGasOverCounter"
	BatchGas                      logTag = "BatchGas"
	SequencingBatchTiming         logTag = "SequencingBatchTiming"
	ProcessingTxTiming            logTag = "ProcessingTxTiming"
	ProcessingInvalidTxCounter    logTag = "ProcessingInvalidTxCounter"
	FinalizeBatchNumber           logTag = "FinalizeBatchNumber"
	BatchCommitDBTiming           logTag = "BatchCommitDBTiming"
	PbStateTiming                 logTag = "PbStateTiming"
	ZkIncIntermediateHashesTiming logTag = "ZkIncIntermediateHashesTiming"
	FinaliseBlockWriteTiming      logTag = "FinaliseBlockWriteTiming"

	ZKHashAccountCount logTag = "ZKHashAccountCount"
	ZKHashStoreCount   logTag = "ZKHashStoreCount"
	ZKHashCodeCount    logTag = "ZKHashCodeCount"

	ZKHashSMTDeleteByNodeKey logTag = "ZKHashSMTDeleteByNodeKey"
	ZKHashSMTDeleteHashKey   logTag = "ZKHashSMTDeleteHashKey"
	ZKHashSMTInsertKey       logTag = "ZKHashSMTInsertKey"
	ZKHashSMTGetKey          logTag = "ZKHashSMTGetKey"

	ZKHashSMTDeleteByNodeKeyTiming logTag = "ZKHashSMTDeleteByNodeKeyTiming"
	ZKHashSMTDeleteHashKeyTiming   logTag = "ZKHashSMTDeleteHashKeyTiming"
	ZKHashSMTInsertKeyTiming       logTag = "ZKHashSMTInsertKeyTiming"
	ZKHashSMTGetKeyTiming          logTag = "ZKHashSMTGetKeyTiming"
)

type Statistics interface {
	CumulativeCounting(tag logTag)
	CumulativeValue(tag logTag, value int64)
	CumulativeTiming(tag logTag, duration time.Duration)
	CumulativeMicroTiming(tag logTag, duration time.Duration)
	SetTag(tag logTag, value string)
	GetTag(tag logTag) string
	GetStatistics(tag logTag) int64
	Summary() string
}
