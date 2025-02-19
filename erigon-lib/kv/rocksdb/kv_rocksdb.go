package rocksdb

import (
	"context"
	"fmt"
	"github.com/ledgerwatch/erigon-lib/common/dbg"
	"github.com/ledgerwatch/erigon-lib/kv"
	"github.com/ledgerwatch/log/v3"
	"github.com/linxGnu/grocksdb"
	"golang.org/x/sync/semaphore"
	"sync"
	"sync/atomic"
	"time"
	"unsafe"
)

var pathDbMap = map[string]kv.RoDB{}
var pathDbMapLock sync.Mutex

type RocksKV struct {
	db  *grocksdb.DB
	log log.Logger

	readTxLimiter  *semaphore.Weighted // does limit amount of concurrent Ro transactions - in most casess runtime.NumCPU() is good value for this channel capacity - this channel can be shared with other components (like Decompressor)
	writeTxLimiter *semaphore.Weighted
	opts           RocksDBOpts
	txSize         uint64
	closed         atomic.Bool
	path           string

	txsCount              uint
	txsCountMutex         *sync.Mutex
	txsAllDoneOnCloseCond *sync.Cond

	leakDetector *dbg.LeakDetector

	MaxBatchSize int

	MaxBatchDelay time.Duration

	batchMu sync.Mutex

	cfHandles map[string]*grocksdb.ColumnFamilyHandle
	tableCfg  kv.TableCfg
}

func (kv *RocksKV) Close() {
	if ok := kv.closed.CompareAndSwap(false, true); !ok {
		return
	}
	kv.db.Close()

	removeFromPathDbMap(kv.path)
}

func (kv *RocksKV) ReadOnly() bool {
	return kv.opts.readOnly
}

func (kv *RocksKV) View(ctx context.Context, f func(tx kv.Tx) error) (err error) {
	tx, err := kv.BeginRo(ctx)
	if err != nil {
		return err
	}
	defer tx.Rollback()

	return f(tx)
}

func (kv *RocksKV) BeginRo(ctx context.Context) (txn kv.Tx, err error) {
	if !kv.trackTxBegin() {
		return nil, fmt.Errorf("db is closed")
	}

	//if semErr := kv.readTxLimiter.Acquire(ctx, 1); semErr != nil {
	//	return nil, fmt.Errorf("rocksdb.RocksKV.BeginRo: roTxsLimiter error %w", semErr)
	//}

	defer func() {
		if txn == nil {
			//kv.readTxLimiter.Release(1)
			kv.trackTxEnd()
		}
	}()
	ro := grocksdb.NewDefaultReadOptions()
	fo := grocksdb.NewDefaultFlushOptions()
	return &RocksTx{
		ctx:      ctx,
		kv:       kv,
		readOnly: true,
		id:       kv.leakDetector.Add(),
		ro:       ro,
		wo:       nil,
		complete: false,
		fo:       fo,
	}, nil
}

func (kv *RocksKV) BeginRoNosync(ctx context.Context) (kv.Tx, error) {
	panic("implement me")
}

func (kv *RocksKV) AllTables() kv.TableCfg {
	//TODO implement me
	panic("implement me")
}

func (kv *RocksKV) PageSize() uint64 {
	//TODO implement me
	panic("implement me")
}

func (kv *RocksKV) CHandle() unsafe.Pointer {
	//TODO implement me
	panic("implement me")
}

func (kv *RocksKV) Update(ctx context.Context, f func(tx kv.RwTx) error) error {
	tx, err := kv.BeginRw(ctx)
	if err != nil {
		return err
	}
	defer tx.Rollback()
	err = f(tx)
	if err != nil {
		return err
	}
	err = tx.Commit()
	if err != nil {
		return err
	}
	return nil
}

func (kv *RocksKV) UpdateNosync(ctx context.Context, f func(tx kv.RwTx) error) error {
	//TODO implement me
	panic("implement me")
}

func (kv *RocksKV) BeginRwNosync(ctx context.Context) (kv.RwTx, error) {
	//TODO implement me
	panic("implement me")
}

func (kv *RocksKV) BeginRw(ctx context.Context) (txn kv.RwTx, err error) {
	if !kv.trackTxBegin() {
		return nil, fmt.Errorf("db closed")
	}
	return &RocksTx{
		kv:       kv,
		ctx:      ctx,
		id:       kv.leakDetector.Add(),
		readOnly: false,
		complete: false,
		wo:       grocksdb.NewDefaultWriteOptions(),
		ro:       grocksdb.NewDefaultReadOptions(),
		fo:       grocksdb.NewDefaultFlushOptions(),
	}, nil
}

func (kv *RocksKV) trackTxBegin() bool {
	kv.txsCountMutex.Lock()
	defer kv.txsCountMutex.Unlock()

	isOpen := !kv.closed.Load()

	if isOpen {
		kv.txsCount++
	}

	return isOpen
}

func (kv *RocksKV) trackTxEnd() {
	kv.txsCountMutex.Lock()
	defer kv.txsCountMutex.Unlock()

	if kv.txsCount > 0 {
		kv.txsCount--
	} else {
		panic("RocksKV: unmatched trackTxEnd")
	}

	if (kv.txsCount == 0) && kv.closed.Load() {
		kv.txsAllDoneOnCloseCond.Signal()
	}
}

func (kv *RocksKV) OpenDbColumnFamilies(cfNames []string, path string) error {

	cfOpts := make([]*grocksdb.Options, len(cfNames)+1)
	cfNames = append(cfNames, "default")
	opts := grocksdb.NewDefaultOptions()
	opts.SetCreateIfMissing(true)
	opts.SetCreateIfMissingColumnFamilies(true)
	for i := range cfOpts {
		cfOpts[i] = opts
	}
	db, cfHandlers, err := grocksdb.OpenDbColumnFamilies(opts, path, cfNames, cfOpts)
	if err != nil {
		return err
	}

	if len(cfHandlers) != len(cfNames) {
		return fmt.Errorf("failed to open db column families: expected %d, got %d", len(cfNames), len(cfHandlers))
	}

	kv.cfHandles = make(map[string]*grocksdb.ColumnFamilyHandle)
	for i, cfName := range cfNames {
		kv.cfHandles[cfName] = cfHandlers[i]
	}
	kv.db = db
	kv.path = path
	return nil
}

func removeFromPathDbMap(path string) {
	pathDbMapLock.Lock()
	defer pathDbMapLock.Unlock()
	delete(pathDbMap, path)
}

func addToPathDbMap(path string, db kv.RoDB) {
	pathDbMapLock.Lock()
	defer pathDbMapLock.Unlock()
	pathDbMap[path] = db
}
