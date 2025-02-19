package membatch

import (
	"context"
	"encoding/binary"
	"errors"
	"fmt"
	"github.com/ledgerwatch/erigon-lib/etl"
	"sort"
	"strings"
	"sync"
	"time"
	"unsafe"

	"github.com/ledgerwatch/erigon-lib/kv"
	"github.com/ledgerwatch/log/v3"
)

type Mapmutation struct {
	puts   map[string]map[string][]byte // table -> key -> value ie. blocks -> hash -> blockBod
	db     kv.Tx
	quit   <-chan struct{}
	clean  func()
	mu     sync.RWMutex
	size   int
	count  uint64
	tmpdir string
	logger log.Logger
}

// NewBatch - starts in-mem batch
//
// Common pattern:
//
// batch := db.NewBatch()
// defer batch.Close()
// ... some calculations on `batch`
// batch.Commit()
func NewHashBatch(tx kv.Tx, quit <-chan struct{}, tmpdir string, logger log.Logger) *Mapmutation {
	clean := func() {}
	if quit == nil {
		ch := make(chan struct{})
		clean = func() { close(ch) }
		quit = ch
	}

	return &Mapmutation{
		db:     tx,
		puts:   make(map[string]map[string][]byte),
		quit:   quit,
		clean:  clean,
		tmpdir: tmpdir,
		logger: logger,
	}
}

func (m *Mapmutation) getMem(table string, key []byte) ([]byte, bool) {
	m.mu.RLock()
	defer m.mu.RUnlock()
	if _, ok := m.puts[table]; !ok {
		return nil, false
	}
	if value, ok := m.puts[table][*(*string)(unsafe.Pointer(&key))]; ok {
		return value, ok
	}

	return nil, false
}

func (m *Mapmutation) IncrementSequence(bucket string, amount uint64) (res uint64, err error) {
	v, ok := m.getMem(kv.Sequence, []byte(bucket))
	if !ok && m.db != nil {
		v, err = m.db.GetOne(kv.Sequence, []byte(bucket))
		if err != nil {
			return 0, err
		}
	}

	var currentV uint64 = 0
	if len(v) > 0 {
		currentV = binary.BigEndian.Uint64(v)
	}

	newVBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(newVBytes, currentV+amount)
	if err = m.Put(kv.Sequence, []byte(bucket), newVBytes); err != nil {
		return 0, err
	}

	return currentV, nil
}
func (m *Mapmutation) ReadSequence(bucket string) (res uint64, err error) {
	v, ok := m.getMem(kv.Sequence, []byte(bucket))
	if !ok && m.db != nil {
		v, err = m.db.GetOne(kv.Sequence, []byte(bucket))
		if err != nil {
			return 0, err
		}
	}
	var currentV uint64 = 0
	if len(v) > 0 {
		currentV = binary.BigEndian.Uint64(v)
	}

	return currentV, nil
}

// Can only be called from the worker thread
func (m *Mapmutation) GetOne(table string, key []byte) ([]byte, error) {
	if value, ok := m.getMem(table, key); ok {
		return value, nil
	}
	if m.db != nil {
		// TODO: simplify when tx can no longer be parent of mutation
		value, err := m.db.GetOne(table, key)
		if err != nil {
			return nil, err
		}
		return value, nil
	}
	return nil, nil
}

func (m *Mapmutation) Last(table string) ([]byte, []byte, error) {
	c, err := m.db.Cursor(table)
	if err != nil {
		return nil, nil, err
	}
	defer c.Close()
	return c.Last()
}

func (m *Mapmutation) Has(table string, key []byte) (bool, error) {
	if _, ok := m.getMem(table, key); ok {
		return ok, nil
	}
	if m.db != nil {
		return m.db.Has(table, key)
	}
	return false, nil
}

// puts a table key with a value and if the table is not found then it appends a table
func (m *Mapmutation) Put(table string, k, v []byte) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if _, ok := m.puts[table]; !ok {
		m.puts[table] = make(map[string][]byte)
	}

	stringKey := string(k)

	var ok bool
	if _, ok = m.puts[table][stringKey]; ok {
		m.size += len(v) - len(m.puts[table][stringKey])
		m.puts[table][stringKey] = v
		return nil
	}
	m.puts[table][stringKey] = v
	m.size += len(k) + len(v)
	m.count++

	return nil
}

func (m *Mapmutation) Append(table string, key []byte, value []byte) error {
	return m.Put(table, key, value)
}

func (m *Mapmutation) AppendDup(table string, key []byte, value []byte) error {
	return m.Put(table, key, value)
}

func (m *Mapmutation) BatchSize() int {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return m.size
}

func (m *Mapmutation) ForEach(bucket string, fromPrefix []byte, walker func(k, v []byte) error) error {
	m.panicOnEmptyDB()

	// take a readlock on the cache
	m.mu.RLock()
	defer m.mu.RUnlock()

	// if the bucket is not in the cache, then we can just use the db
	if _, ok := m.puts[bucket]; !ok {
		return m.db.ForEach(bucket, fromPrefix, walker)
	}

	// create an ordered structure to hold our data
	keys := make([]string, 0, len(m.puts[bucket]))
	values := make(map[string][]byte)

	// otherwise fill the ordered data structure
	// range the db table
	err := m.db.ForEach(bucket, fromPrefix, func(k, v []byte) error {
		keys = append(keys, string(k))
		values[string(k)] = v
		return nil
	})
	if err != nil {
		return err
	}

	// range the cache, and perform an ordered insert to the local structure
	for k, v := range m.puts[bucket] {
		// ordered insert to keys
		index := sort.Search(len(keys), func(i int) bool { return keys[i] >= k })
		keys = append(keys, "")
		copy(keys[index+1:], keys[index:])
		keys[index] = k

		// collect value in map
		values[k] = v
	}

	// temp check to see if we are in order
	sort.SliceStable(keys, func(i, j int) bool {
		return keys[i] < keys[j]
	})

	// range the ordered structure and call the walker
	for _, k := range keys {
		// only where the prefix matches
		sp := string(fromPrefix)
		if !strings.HasPrefix(k, sp) {
			continue
		}
		err := walker([]byte(k), values[k])
		if err != nil {
			return err
		}
	}

	return nil
}

func (m *Mapmutation) ForPrefix(bucket string, prefix []byte, walker func(k, v []byte) error) error {
	m.panicOnEmptyDB()
	return m.db.ForPrefix(bucket, prefix, walker)
}

func (m *Mapmutation) ForAmount(bucket string, prefix []byte, amount uint32, walker func(k, v []byte) error) error {
	m.panicOnEmptyDB()
	return m.db.ForAmount(bucket, prefix, amount, walker)
}

func (m *Mapmutation) Delete(table string, k []byte) error {
	return m.Put(table, k, nil)
}

func (m *Mapmutation) doCommit(tx kv.RwTx) error {
	startTime := time.Now()
	keyCount := 0
	total := m.count

	// 设置批量限制
	batchLimit := 1000
	for table, bucket := range m.puts {
		// 预分配更大的内存池以减少内存分配
		batchKeys := make([][]byte, 0, batchLimit*2)
		batchValues := make([][]byte, 0, batchLimit*2)
		collector := etl.NewCollector("", m.tmpdir, etl.NewSortableBuffer(etl.BufferOptimalSize/2), m.logger)
		collector.SortAndFlushInBackground(true)

		for key, value := range bucket {
			// 批量填充数据
			batchKeys = append(batchKeys, []byte(key))
			batchValues = append(batchValues, value)
			keyCount++

			// 达到批量限制时进行处理
			if len(batchKeys) >= batchLimit {
				// 批量收集
				if err := collectBatch(collector, batchKeys, batchValues); err != nil {
					return err
				}
				// 清空内存池
				batchKeys = batchKeys[:0]
				batchValues = batchValues[:0]
			}

			// 每 30s 记录一次进度，减少日志记录频率
			if time.Since(startTime) > 30*time.Second {
				progress := fmt.Sprintf("%.1fM/%.1fM", float64(keyCount)/1_000_000, total/1_000_000)
				m.logger.Info("Write to db", "progress", progress, "current table", table)
				tx.CollectMetrics()
				startTime = time.Now()
			}
		}

		// 处理剩余未满 batchLimit 的数据
		if len(batchKeys) > 0 {
			if err := collectBatch(collector, batchKeys, batchValues); err != nil {
				return err
			}
		}

		// 一次性执行 Load()，减少对 tx 的多次写入开销
		if err := collector.Load(tx, table, etl.IdentityLoadFunc, etl.TransformArgs{Quit: m.quit}); err != nil {
			return err
		}
	}

	tx.CollectMetrics()
	return nil
}

// collectBatch 负责批量收集
func collectBatch(collector *etl.Collector, keys [][]byte, values [][]byte) error {
	// 键值长度不匹配时返回错误
	if len(keys) != len(values) {
		return fmt.Errorf("keys and values length mismatch")
	}
	// 批量写入
	for i := range keys {
		if err := collector.Collect(keys[i], values[i]); err != nil {
			return err
		}
	}
	return nil
}

func (m *Mapmutation) Flush(ctx context.Context, tx kv.RwTx) error {
	if tx == nil {
		return errors.New("rwTx needed")
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	if err := m.doCommit(tx); err != nil {
		return err
	}

	m.puts = map[string]map[string][]byte{}
	m.size = 0
	m.count = 0
	return nil
}

func (m *Mapmutation) Close() {
	if m.clean == nil {
		return
	}

	m.mu.Lock()
	defer m.mu.Unlock()
	m.puts = map[string]map[string][]byte{}
	m.size = 0
	m.count = 0
	m.size = 0

	m.clean()
	m.clean = nil

}
func (m *Mapmutation) Commit() error { panic("not db txn, use .Flush method") }
func (m *Mapmutation) Rollback()     { panic("not db txn, use .Close method") }

func (m *Mapmutation) panicOnEmptyDB() {
	if m.db == nil {
		panic("Not implemented")
	}
}
