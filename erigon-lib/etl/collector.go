/*
   Copyright 2021 Erigon contributors

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

package etl

import (
	"bytes"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"time"

	"github.com/c2h5oh/datasize"
	"github.com/ledgerwatch/log/v3"

	"github.com/ledgerwatch/erigon-lib/common"
	"github.com/ledgerwatch/erigon-lib/common/dir"
	"github.com/ledgerwatch/erigon-lib/kv"
)

type LoadNextFunc func(originalK, k, v []byte) error
type LoadFunc func(k, v []byte, table CurrentTableReader, next LoadNextFunc) error
type simpleLoadFunc func(k, v []byte) error

// Collector performs the job of ETL Transform, but can also be used without "E" (Extract) part
// as a Collect Transform Load
type Collector struct {
	buf           Buffer
	logPrefix     string
	tmpdir        string
	dataProviders []dataProvider
	logLvl        log.Lvl
	bufType       int
	allFlushed    bool
	autoClean     bool
	logger        log.Logger

	// sortAndFlushInBackground increase insert performance, but make RAM use less-predictable:
	//   - if disk is over-loaded - app may have much background threads which waiting for flush - and each thread whill hold own `buf` (can't free RAM until flush is done)
	//   - enable it only when writing to `etl` is a bottleneck and unlikely to have many parallel collectors (to not overload CPU/Disk)
	sortAndFlushInBackground bool
}

// NewCollectorFromFiles creates collector from existing files (left over from previous unsuccessful loading)
func NewCollectorFromFiles(logPrefix, tmpdir string, logger log.Logger) (*Collector, error) {
	if _, err := os.Stat(tmpdir); os.IsNotExist(err) {
		return nil, nil
	}
	dirEntries, err := dir.ReadDir(tmpdir)
	if err != nil {
		return nil, fmt.Errorf("collector from files - reading directory %s: %w", tmpdir, err)
	}
	if len(dirEntries) == 0 {
		return nil, nil
	}
	dataProviders := make([]dataProvider, len(dirEntries))
	for i, dirEntry := range dirEntries {
		fileInfo, err := dirEntry.Info()
		if err != nil {
			return nil, fmt.Errorf("collector from files - reading file info %s: %w", dirEntry.Name(), err)
		}
		var dataProvider fileDataProvider
		dataProvider.file, err = os.Open(filepath.Join(tmpdir, fileInfo.Name()))
		if err != nil {
			return nil, fmt.Errorf("collector from files - opening file %s: %w", fileInfo.Name(), err)
		}
		dataProviders[i] = &dataProvider
	}
	return &Collector{dataProviders: dataProviders, allFlushed: true, autoClean: false, logPrefix: logPrefix}, nil
}

// NewCriticalCollector does not clean up temporary files if loading has failed
func NewCriticalCollector(logPrefix, tmpdir string, sortableBuffer Buffer, logger log.Logger) *Collector {
	c := NewCollector(logPrefix, tmpdir, sortableBuffer, logger)
	c.autoClean = false
	return c
}

func NewCollector(logPrefix, tmpdir string, sortableBuffer Buffer, logger log.Logger) *Collector {
	return &Collector{autoClean: true, bufType: getTypeByBuffer(sortableBuffer), buf: sortableBuffer, logPrefix: logPrefix, tmpdir: tmpdir, logLvl: log.LvlInfo, logger: logger}
}

func (c *Collector) SortAndFlushInBackground(v bool) { c.sortAndFlushInBackground = v }

func (c *Collector) extractNextFunc(originalK, k []byte, v []byte) error {
	c.buf.Put(k, v)
	if !c.buf.CheckFlushSize() {
		return nil
	}
	return c.flushBuffer(false)
}

func (c *Collector) Collect(k, v []byte) error {
	return c.extractNextFunc(k, k, v)
}

func (c *Collector) LogLvl(v log.Lvl) { c.logLvl = v }

func (c *Collector) flushBuffer(canStoreInRam bool) error {
	if c.buf.Len() == 0 {
		return nil
	}

	var provider dataProvider
	if canStoreInRam && len(c.dataProviders) == 0 {
		c.buf.Sort()
		provider = KeepInRAM(c.buf)
		c.allFlushed = true
	} else {
		doFsync := !c.autoClean /* is critical collector */
		var err error

		if c.sortAndFlushInBackground {
			fullBuf := c.buf // can't `.Reset()` because this `buf` will move to another goroutine
			prevLen, prevSize := fullBuf.Len(), fullBuf.SizeLimit()
			c.buf = getBufferByType(c.bufType, datasize.ByteSize(c.buf.SizeLimit()), c.buf)

			provider, err = FlushToDiskAsync(c.logPrefix, fullBuf, c.tmpdir, doFsync, c.logLvl)
			if err != nil {
				return err
			}
			c.buf.Prealloc(prevLen/8, prevSize/8)
		} else {
			provider, err = FlushToDisk(c.logPrefix, c.buf, c.tmpdir, doFsync, c.logLvl)
			if err != nil {
				return err
			}
			c.buf.Reset()
		}
	}
	if provider != nil {
		c.dataProviders = append(c.dataProviders, provider)
	}
	return nil
}

// Flush - an optional method (usually user don't need to call it) - forcing sort+flush current buffer.
// it does trigger background sort and flush, reducing RAM-holding, etc...
// it's useful when working with many collectors: to trigger background sort for all of them
func (c *Collector) Flush() error {
	if !c.allFlushed {
		if e := c.flushBuffer(false); e != nil {
			return e
		}
	}
	return nil
}

func (c *Collector) Load(db kv.RwTx, toBucket string, loadFunc LoadFunc, args TransformArgs) error {
	if c.autoClean {
		defer c.Close()
	}
	args.BufferType = c.bufType

	if !c.allFlushed {
		if err := c.flushBuffer(true); err != nil {
			return err
		}
	}

	var cursor kv.RwCursor
	var lastKey []byte
	bucket := toBucket

	// 初始化游标（cursor）
	if bucket != "" {
		var err error
		if cursor, err = db.RwCursor(bucket); err != nil {
			return err
		}
		if lastKey, _, err = cursor.Last(); err != nil {
			return err
		}
	}

	haveSortingGuarantees := isIdentityLoadFunc(loadFunc)
	isDupSort := kv.ChaindataTablesCfg[bucket].Flags&kv.DupSort != 0 && !kv.ChaindataTablesCfg[bucket].AutoDupSortKeysConversion

	logTicker := time.NewTicker(30 * time.Second)
	defer logTicker.Stop()

	// 预分配
	i := 0
	canUseAppend := false
	currentTable := &currentTableReader{db, bucket}

	loadNextFunc := func(_, k, v []byte) error {
		if i == 0 {
			canUseAppend = haveSortingGuarantees && (lastKey == nil || bytes.Compare(lastKey, k) == -1)
		}
		i++

		// 记录日志，避免 `select-case` 造成的性能损失
		select {
		case <-logTicker.C:
			logArgs := []interface{}{"into", bucket}
			if args.LogDetailsLoad != nil {
				logArgs = append(logArgs, args.LogDetailsLoad(k, v)...)
			} else {
				logArgs = append(logArgs, "current_prefix", makeCurrentKeyStr(k))
			}
			c.logger.Log(c.logLvl, fmt.Sprintf("[%s] ETL [2/2] Loading", c.logPrefix), logArgs...)
		default:
		}

		// nil 值处理优化，减少 `if` 嵌套
		isNil := len(v) == 0 && (c.bufType == SortableAppendBuffer || c.bufType == SortableOldestAppearedBuffer || c.bufType == SortableSliceBuffer)
		if isNil {
			if canUseAppend {
				return nil
			}
			return cursor.Delete(k)
		}

		// Append 方式优化
		if canUseAppend {
			if isDupSort {
				return cursor.(kv.RwCursorDupSort).AppendDup(k, v)
			}
			return cursor.Append(k, v)
		}

		// 默认使用 Put
		return cursor.Put(k, v)
	}

	// 使用 `mergeSortFiles` 加载数据
	simpleLoad := func(k, v []byte) error {
		return loadFunc(k, v, currentTable, loadNextFunc)
	}
	if err := mergeSortFiles(c.logPrefix, c.dataProviders, simpleLoad, args, c.buf); err != nil {
		return fmt.Errorf("loadIntoTable %s: %w", toBucket, err)
	}

	return nil
}

func (c *Collector) reset() {
	if c.dataProviders != nil {
		for _, p := range c.dataProviders {
			p.Dispose()
		}
		c.dataProviders = nil
	}
	c.buf.Reset()
	c.allFlushed = false
}

func (c *Collector) Close() {
	c.reset()
}

// mergeSortFiles uses merge-sort to order the elements stored within the slice of providers,
// regardless of ordering within the files the elements will be processed in order.
// The first pass reads the first element from each of the providers and populates a heap with the key/value/provider index.
// Later, the heap is popped to get the first element, the record is processed using the LoadFunc, and the provider is asked
// for the next item, which is then added back to the heap.
// The subsequent iterations pop the heap again and load up the provider associated with it to get the next element after processing LoadFunc.
// this continues until all providers have reached their EOF.
func mergeSortFiles(logPrefix string, providers []dataProvider, loadFunc simpleLoadFunc, args TransformArgs, buf Buffer) (err error) {
	for _, provider := range providers {
		if err := provider.Wait(); err != nil {
			return err
		}
	}

	h := &Heap{}
	heapInit(h)

	// 预取第一批数据
	elements := make([]*HeapElem, 0, len(providers))
	for i, provider := range providers {
		if key, value, err := provider.Next(nil, nil); err == nil {
			elements = append(elements, &HeapElem{key, value, i})
		} else {
			return fmt.Errorf("%s: error reading first readers: n=%d current=%d provider=%s err=%w",
				logPrefix, len(providers), i, provider, err)
		}
	}

	// 批量插入 Heap，减少 heap 操作次数
	heapPushBatch(h, elements)

	var prevK, prevV []byte
	prevKSet := false

	// Main loading loop
	for h.Len() > 0 {
		if err := common.Stopped(args.Quit); err != nil {
			return err
		}

		element := heapPop(h)
		provider := providers[element.TimeIdx]

		switch args.BufferType {
		case SortableOldestAppearedBuffer:
			if !bytes.Equal(prevK, element.Key) {
				if err = loadFunc(element.Key, element.Value); err != nil {
					return err
				}
				prevK = common.ReuseOrCopy(prevK, element.Key)
			}
		case SortableAppendBuffer:
			if !bytes.Equal(prevK, element.Key) {
				if prevKSet {
					if err = loadFunc(prevK, prevV); err != nil {
						return err
					}
				}
				prevK = common.ReuseOrCopy(prevK, element.Key)
				prevV = append(prevV[:0], element.Value...) // 避免 append 触发扩容
				prevKSet = true
			} else {
				prevV = append(prevV, element.Value...)
			}
		case SortableMergeBuffer:
			if !bytes.Equal(prevK, element.Key) {
				if prevKSet {
					if err = loadFunc(prevK, prevV); err != nil {
						return err
					}
				}
				prevK = common.ReuseOrCopy(prevK, element.Key)
				prevV = common.ReuseOrCopy(prevV, element.Value)
				prevKSet = true
			} else {
				prevV = buf.(*oldestMergedEntrySortableBuffer).merge(prevV, element.Value)
			}
		default:
			if err = loadFunc(element.Key, element.Value); err != nil {
				return err
			}
		}

		// 预取下一个元素，避免频繁 I/O
		if element.Key, element.Value, err = provider.Next(element.Key[:0], element.Value[:0]); err == nil {
			heapPush(h, element)
		} else if !errors.Is(err, io.EOF) {
			return fmt.Errorf("%s: error while reading next element from disk: %w", logPrefix, err)
		}
	}

	if args.BufferType == SortableAppendBuffer && prevKSet {
		if err = loadFunc(prevK, prevV); err != nil {
			return err
		}
	}

	return nil
}

// heapPushBatch 批量插入 heap，减少 heap 操作的开销
func heapPushBatch(h *Heap, elements []*HeapElem) {
	for _, elem := range elements {
		heapPush(h, elem)
	}
}

func makeCurrentKeyStr(k []byte) string {
	var currentKeyStr string
	if k == nil {
		currentKeyStr = "final"
	} else if len(k) < 4 {
		currentKeyStr = hex.EncodeToString(k)
	} else if k[0] == 0 && k[1] == 0 && k[2] == 0 && k[3] == 0 && len(k) >= 8 { // if key has leading zeroes, show a bit more info
		currentKeyStr = hex.EncodeToString(k)
	} else {
		currentKeyStr = hex.EncodeToString(k[:4])
	}
	return currentKeyStr
}
