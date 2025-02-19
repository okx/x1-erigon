package rocksdb

import (
	"context"
	"github.com/ledgerwatch/erigon-lib/common/dbg"
	"github.com/ledgerwatch/erigon-lib/kv"
	"github.com/ledgerwatch/log/v3"
	"github.com/linxGnu/grocksdb"
	"golang.org/x/sync/semaphore"
	"runtime"
	"sort"
	"strings"
	"sync"
)

type TableCfgFunc func(defaultCF kv.TableCfg) kv.TableCfg

func WithChaindataTables(defaultBuckets kv.TableCfg) kv.TableCfg {
	return defaultBuckets
}

type RocksDBOpts struct {
	log            log.Logger
	label          kv.Label
	verbosity      kv.DBVerbosityLvl
	readTxLimiter  *semaphore.Weighted
	writeTxLimiter *semaphore.Weighted
	readOnly       bool
	exclusive      bool
	path           string
	cfConfig       TableCfgFunc
}

func NewRocksDBOpts(log log.Logger) *RocksDBOpts {
	return &RocksDBOpts{
		log:      log,
		cfConfig: WithChaindataTables,
		label:    kv.InMem,
	}
}

func (opts RocksDBOpts) Open(ctx context.Context) (kv.RwDB, error) {
	rocksDBOptions := grocksdb.NewDefaultOptions()
	rocksDBOptions.SetCreateIfMissing(true)
	rocksDBOptions.SetCreateIfMissingColumnFamilies(true)
	rocksDBOptions.SetInfoLogLevel(grocksdb.InfoLogLevel(opts.verbosity))

	if opts.readTxLimiter == nil {
		targetSemCount := int64(runtime.GOMAXPROCS(-1) * 16)
		opts.readTxLimiter = semaphore.NewWeighted(targetSemCount) // 1 less than max to allow unlocking to happen
	}

	if opts.writeTxLimiter == nil {
		targetSemCount := int64(runtime.GOMAXPROCS(-1)) - 1
		opts.writeTxLimiter = semaphore.NewWeighted(targetSemCount) // 1 less than max to allow unlocking to happen
	}
	txsCountMutex := &sync.Mutex{}

	kvStore := &RocksKV{
		opts:                  opts,
		log:                   opts.log,
		readTxLimiter:         opts.readTxLimiter,
		writeTxLimiter:        opts.writeTxLimiter,
		txsCountMutex:         txsCountMutex,
		txsAllDoneOnCloseCond: sync.NewCond(txsCountMutex),
		leakDetector:          dbg.NewLeakDetector("db."+opts.label.String(), dbg.SlowTx()),
		tableCfg:              kv.TableCfg{},
	}

	customCf := opts.cfConfig(kv.ChaindataTablesCfg)
	for name, cfg := range customCf {
		kvStore.tableCfg[name] = cfg
	}
	cf := cfSlice(kvStore.tableCfg)

	if err := kvStore.OpenDbColumnFamilies(cf, opts.path); err != nil {
		return nil, err
	}

	addToPathDbMap(opts.path, kvStore)

	return kvStore, nil
}

func cfSlice(b kv.TableCfg) []string {
	buckets := make([]string, 0, len(b))
	for name := range b {
		buckets = append(buckets, name)
	}
	sort.Slice(buckets, func(i, j int) bool {
		return strings.Compare(buckets[i], buckets[j]) < 0
	})
	return buckets
}

func (opts RocksDBOpts) GetLabel() kv.Label { return opts.label }

func (opts RocksDBOpts) RoTxsLimiter(l *semaphore.Weighted) RocksDBOpts {
	opts.readTxLimiter = l
	return opts
}

func (opts RocksDBOpts) DBVerbosity(v kv.DBVerbosityLvl) RocksDBOpts {
	opts.verbosity = v
	return opts
}

func (opts RocksDBOpts) Readonly() RocksDBOpts {
	opts.readOnly = true
	return opts
}

func (opts RocksDBOpts) Exclusive() RocksDBOpts {
	opts.exclusive = true
	return opts
}

func (opts RocksDBOpts) Label(label kv.Label) RocksDBOpts {
	opts.label = label
	return opts
}

func (opts RocksDBOpts) Path(path string) RocksDBOpts {
	opts.path = path
	return opts
}
