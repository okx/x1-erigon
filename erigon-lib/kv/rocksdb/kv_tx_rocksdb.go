package rocksdb

import (
	"context"
	"encoding/binary"
	"fmt"
	"github.com/ledgerwatch/erigon-lib/kv"
	"github.com/ledgerwatch/erigon-lib/kv/iter"
	"github.com/ledgerwatch/erigon-lib/kv/order"
	"github.com/linxGnu/grocksdb"
	"unsafe"
)

/*Not actually using RocksDB Tx just implementing interface*/

type RocksTx struct {
	id       uint64
	kv       *RocksKV
	ctx      context.Context
	wo       *grocksdb.WriteOptions
	ro       *grocksdb.ReadOptions
	fo       *grocksdb.FlushOptions
	readOnly bool
	complete bool
}

func (rtx *RocksTx) Has(table string, key []byte) (bool, error) {
	if cfHandle, exists := rtx.kv.cfHandles[table]; exists {
		psh, err := rtx.kv.db.GetPinnedCF(rtx.ro, cfHandle, key)
		defer psh.Destroy()
		//sh, err := r.kv.db.GetCF(r.ro, cfHandle, key)
		if err != nil {
			return false, err
		}
		return psh.Exists(), nil
	} else {
		return false, fmt.Errorf("table/cf %s not found", table)
	}
}

func (rtx *RocksTx) GetOne(table string, key []byte) (val []byte, err error) {
	if cfHandle, exists := rtx.kv.cfHandles[table]; exists {
		var psh *grocksdb.Slice
		psh, err = rtx.kv.db.GetCF(rtx.ro, cfHandle, key)
		if err != nil {
			return nil, err
		}

		if !psh.Exists() {
			return nil, nil
		}

		return psh.Data(), nil
	} else {
		return nil, fmt.Errorf("table %s not found", table)
	}
}

func (rtx *RocksTx) ForEach(table string, fromPrefix []byte, walker func(k []byte, v []byte) error) error {
	cfHandle, exists := rtx.kv.cfHandles[table]
	if !exists {
		return fmt.Errorf("cfHandle not found for table: %s", table)
	}
	it := rtx.kv.db.NewIteratorCF(rtx.ro, cfHandle)
	defer it.Close()

	for it.Seek(fromPrefix); it.Valid(); it.Next() {
		if err := walker(it.Key().Data(), it.Value().Data()); err != nil {
			return err
		}
	}
	return nil
}

func (rtx *RocksTx) ForPrefix(table string, prefix []byte, walker func(k []byte, v []byte) error) error {
	//TODO implement me
	panic("implement me - ForPrefix")
}

func (rtx *RocksTx) ForAmount(table string, prefix []byte, amount uint32, walker func(k []byte, v []byte) error) error {
	//TODO implement me
	panic("implement me - ForAmount")
}

func (rtx *RocksTx) Commit() error {
	if rtx.complete {
		return nil
	}
	rtx.complete = true
	rtx.kv.trackTxEnd()
	rtx.kv.leakDetector.Del(rtx.id)
	rtx.ro.Destroy()
	if !rtx.readOnly {
		rtx.wo.Destroy()
	}

	err := rtx.kv.db.Flush(rtx.fo)
	rtx.fo.Destroy()
	return err
}

func (rtx *RocksTx) Rollback() {
	if rtx.complete {
		return
	}

	rtx.complete = true
	rtx.kv.trackTxEnd()
	rtx.ro.Destroy()
	if !rtx.readOnly {
		rtx.wo.Destroy()
	}

	rtx.kv.leakDetector.Del(rtx.id)
	return
}

func (rtx *RocksTx) ListBuckets() ([]string, error) {
	//TODO implement me
	panic("implement me- ListBuckets")
}

func (rtx *RocksTx) ViewID() uint64 {
	//TODO implement me
	panic("implement me - ViewID")
}

func (rtx *RocksTx) Cursor(table string) (kv.Cursor, error) {
	return rtx.RwCursor(table)
}

func (rtx *RocksTx) CursorDupSort(table string) (kv.CursorDupSort, error) {
	//TODO implement me
	panic("implement me - CursorDupSort")
}

func (rtx *RocksTx) DBSize() (uint64, error) {
	//TODO implement me
	panic("implement me - DBSize")
}

func (rtx *RocksTx) Range(table string, fromPrefix, toPrefix []byte) (iter.KV, error) {
	//TODO implement me
	panic("implement me - Range")
}

func (rtx *RocksTx) RangeAscend(table string, fromPrefix, toPrefix []byte, limit int) (iter.KV, error) {
	//TODO implement me
	panic("implement me - RangeAscend")
}

func (rtx *RocksTx) RangeDescend(table string, fromPrefix, toPrefix []byte, limit int) (iter.KV, error) {
	//TODO implement me
	panic("implement me - RangeDescend")
}

func (rtx *RocksTx) Prefix(table string, prefix []byte) (iter.KV, error) {
	//TODO implement me
	panic("implement me - Prefix")
}

func (rtx *RocksTx) RangeDupSort(table string, key []byte, fromPrefix, toPrefix []byte, asc order.By, limit int) (iter.KV, error) {
	//TODO implement me
	panic("implement me - RangeDupSort")
}

func (rtx *RocksTx) CHandle() unsafe.Pointer {
	//TODO implement me
	panic("implement me - CHandle")
}

func (rtx *RocksTx) BucketSize(table string) (uint64, error) {
	//TODO implement me
	panic("implement me - BucketSize")
}

func (rtx *RocksTx) Put(table string, k, v []byte) error {
	if rtx.readOnly {
		return fmt.Errorf("put in read-only transaction")
	}
	var cfHandle *grocksdb.ColumnFamilyHandle
	var exists bool
	if cfHandle, exists = rtx.kv.cfHandles[table]; !exists {
		return fmt.Errorf("cfHandle not found for table: %s", table)
	}

	err := rtx.kv.db.PutCF(rtx.wo, cfHandle, k, v)
	return err
}

func (rtx *RocksTx) Delete(table string, k []byte) error {
	if rtx.readOnly {
		return fmt.Errorf("delete in read-only transaction")
	}
	var cfHandle *grocksdb.ColumnFamilyHandle
	var exists bool
	if cfHandle, exists = rtx.kv.cfHandles[table]; !exists {
		return fmt.Errorf("cfHandle not found for table: %s", table)
	}
	err := rtx.kv.db.DeleteCF(rtx.wo, cfHandle, k)
	return err
}

func (rtx *RocksTx) ReadSequence(table string) (uint64, error) {
	val, err := rtx.GetOne(kv.Sequence, []byte(table))
	if err != nil {
		return 0, err
	}

	var currentV uint64
	if len(val) > 0 {
		currentV = binary.BigEndian.Uint64(val)
	}
	return currentV, nil
}

func (rtx *RocksTx) IncrementSequence(table string, amount uint64) (uint64, error) {
	val, err := rtx.GetOne(kv.Sequence, []byte(table))
	if err != nil {
		return 0, err
	}

	var currentV uint64 = 0
	if len(val) > 0 {
		currentV = binary.BigEndian.Uint64(val)
	}
	newVBytes := make([]byte, 8)
	binary.BigEndian.PutUint64(newVBytes, currentV+amount)

	err = rtx.Put(kv.Sequence, []byte(table), newVBytes)
	if err != nil {
		return 0, err
	}
	return currentV, nil
}

func (rtx *RocksTx) Append(table string, k, v []byte) error {
	//TODO implement me
	panic("implement me - Append")
}

func (rtx *RocksTx) AppendDup(table string, k, v []byte) error {
	//TODO implement me
	panic("implement me - AppendDup")
}

func (rtx *RocksTx) DropBucket(s string) error {
	//TODO implement me
	panic("implement me - DropBucket")
}

func (rtx *RocksTx) CreateBucket(name string) error {
	if _, exists := rtx.kv.cfHandles[name]; exists {
		return nil
	}
	cfHandle, err := rtx.kv.db.CreateColumnFamily(grocksdb.NewDefaultOptions(), name)
	if err != nil {
		return err
	}
	rtx.kv.cfHandles[name] = cfHandle
	return nil
}

func (rtx *RocksTx) ExistsBucket(s string) (bool, error) {
	//TODO implement me
	panic("implement me - ExistsBucket")
}

func (rtx *RocksTx) ClearBucket(s string) error {
	//TODO implement me
	panic("implement me - ClearBucket")
}

func (rtx *RocksTx) RwCursor(table string) (kv.RwCursor, error) {
	return rtx.stdCursor(table)
}

func (rtx *RocksTx) stdCursor(table string) (kv.RwCursor, error) {
	cfHandle, exists := rtx.kv.cfHandles[table]
	if !exists {
		return nil, fmt.Errorf("cfHandle not found for table: %s", table)
	}
	it := rtx.kv.db.NewIteratorCF(rtx.ro, cfHandle)

	c := &RocksCursor{
		tx: rtx,
		id: rtx.id,
		it: it,
	}

	return c, nil
}

func (rtx *RocksTx) RwCursorDupSort(table string) (kv.RwCursorDupSort, error) {
	//TODO implement me
	panic("implement me - RwCursorDupSort")
}

func (rtx *RocksTx) CollectMetrics() {
	//TODO implement me
	panic("implement me - CollectMetrics")
}
