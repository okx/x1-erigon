package rocksdb

import (
	"bytes"
	"fmt"
	"github.com/erigontech/mdbx-go/mdbx"
	"github.com/ledgerwatch/erigon-lib/kv"
	"github.com/linxGnu/grocksdb"
	"regexp"
	"strconv"
)

type RocksIterator struct {
	tx       *RocksTx
	id       uint64
	it       *grocksdb.Iterator
	tableCfg kv.TableCfgItem
	cfHandle *grocksdb.ColumnFamilyHandle
}

var DUP_REGEX = regexp.MustCompile(`:\d{4}$`)
var KEY_ESTIMATE_PROP = "rocksdb.estimate-num-keys"

func (r *RocksIterator) Seek(key []byte) (k []byte, v []byte, err error) {
	if r.tableCfg.AutoDupSortKeysConversion {
		return r.seekDupSort(key)
	}

	if len(key) == 0 {
		k, v, err = r.first()
	} else {
		k, v, err = r.setRange(key)
	}

	if err != nil {
		return []byte{}, nil, err
	}
	return k, v, nil
}

func (r *RocksIterator) SeekExact(key []byte) ([]byte, []byte, error) {

	//TODO implement me
	panic("implement me - SeekExact")
}

func (r *RocksIterator) Last() ([]byte, []byte, error) {
	r.it.SeekToLast()
	if r.it.Valid() {
		return bytes.Clone(r.it.Key().Data()), bytes.Clone(r.it.Value().Data()), nil
	}
	return nil, nil, nil
}

func (r *RocksIterator) Current() ([]byte, []byte, error) {
	//TODO implement me
	panic("implement me - Current")
}

func (r *RocksIterator) Close() {
	if r.it != nil {
		r.it.Close()
	}
}

func (r *RocksIterator) Put(k, v []byte) error {
	//TODO implement me
	panic("implement me - RocksDB iterator doesnt support Put!")
}

func (r *RocksIterator) Delete(k []byte) error {
	//TODO implement me
	panic("implement me - Delete")
}

func (r *RocksIterator) DeleteCurrent() error {
	//TODO implement me
	panic("implement me - DeleteCurrent")
}

func (r *RocksIterator) first() ([]byte, []byte, error) {
	r.it.SeekToFirst()
	if r.it.Valid() {
		return bytes.Clone(r.it.Key().Data()), bytes.Clone(r.it.Value().Data()), nil
	}
	return nil, nil, nil
}

func (r *RocksIterator) setRange(key []byte) ([]byte, []byte, error) {
	r.it.Seek(key)
	if r.it.Valid() {
		return bytes.Clone(r.it.Key().Data()), bytes.Clone(r.it.Value().Data()), nil
	}
	return nil, nil, nil
}

func (r *RocksIterator) seekDupSort(key []byte) ([]byte, []byte, error) {
	b := r.tableCfg
	from, to := b.DupFromLen, b.DupToLen
	if len(key) == 0 {
		k, v, err := r.first()
		if err != nil {
			return []byte{}, nil, err
		}
		if v == nil {
			return nil, nil, nil
		}
		if (r.tableCfg.Flags&mdbx.DupSort) == 1 && len(k) > 5 && DUP_REGEX.Match(k) {
			k = k[:len(k)-5]
		}
		if len(k) == to {
			k2 := make([]byte, 0, len(k)+from-to)
			k2 = append(append(k2, k...), v[:from-to]...)
			v = v[from-to:]
			k = k2
		}
		return k, v, nil
	}

	var seek1, seek2 []byte
	if len(key) > to {
		seek1, seek2 = key[:to], key[to:]
	} else {
		seek1 = key
	}
	k, v, err := r.setRange(seek1)
	if err != nil {
		return []byte{}, nil, err
	}
	if v == nil {
		return nil, nil, nil
	}

	if seek2 != nil && bytes.HasPrefix(seek1, k) {
		if (r.tableCfg.Flags&mdbx.DupSort) == 1 && len(k) > 5 && DUP_REGEX.Match(k) {
			k = k[:len(k)-5]
		}
		if bytes.Equal(k, seek1) {
			v, err = r.getBothRange(seek1, seek2)
			if err == nil && v == nil {
				k, v, err = r.next()
				if err == nil && v == nil {
					return nil, nil, nil
				}
				if err != nil {
					return []byte{}, nil, err
				}
				if (r.tableCfg.Flags&mdbx.DupSort) == 1 && len(k) > 5 && DUP_REGEX.Match(k) {
					k = k[:len(k)-5]
				}
			} else if err != nil {
				return []byte{}, nil, err
			}
		}

	}

	if len(key) == to {
		k2 := make([]byte, 0, len(k)+from-to)
		k2 = append(append(k2, k...), v[:from-to]...)
		v = v[from-to:]
		k = k2
	}

	return k, v, nil
}

func (r *RocksIterator) getBothRange(k, v []byte) ([]byte, error) {
	for r.it.Seek(k); r.it.Valid(); r.it.Next() {
		if bytes.Compare(r.it.Value().Data(), v) >= 0 {
			return bytes.Clone(r.it.Value().Data()), nil
		}
	}

	return nil, nil
}

func (r *RocksIterator) next() ([]byte, []byte, error) {
	r.it.Next()
	if r.it.Valid() {
		return bytes.Clone(r.it.Key().Data()), bytes.Clone(r.it.Value().Data()), nil
	}
	return nil, nil, nil
}

func (r *RocksIterator) Append(k []byte, v []byte) error {
	if r.tableCfg.AutoDupSortKeysConversion {
		cfg := r.tableCfg
		from, to := cfg.DupFromLen, cfg.DupToLen

		if len(k) != from && len(k) >= to {
			return fmt.Errorf("label: %s, append dupsort bucket: %s, can have keys of len==%d and len<%d. key: %x,%d", "label", "bucketname", from, to, k, len(k))
		}

		if len(k) == from {
			v = append(k[to:], v...)
			k = k[:to]
		}
	}

	if r.tableCfg.Flags&mdbx.DupSort != 0 { //Duplicate records are enabled
		rd := RocksDupSortIterator{
			RocksIterator: r,
		}
		if err := rd.AppendDup(k, v); err != nil {
			return err
		}
		return nil
	}

	return r.tx.kv.db.PutCF(r.tx.wo, r.cfHandle, k, v)
}

func (r *RocksIterator) Prev() ([]byte, []byte, error) {
	k, v, _ := r.prev()
	if v == nil {
		return nil, nil, nil
	}
	cfg := r.tableCfg

	if (r.tableCfg.Flags&mdbx.DupSort) == 1 && len(k) > 5 && DUP_REGEX.Match(k) {
		k = k[:len(k)-5]
	}

	if cfg.AutoDupSortKeysConversion && len(k) == cfg.DupToLen {
		keyPart := cfg.DupFromLen - cfg.DupToLen
		k = append(k, v[:keyPart]...)
		v = v[keyPart:]
	}
	return k, v, nil
}

func (r *RocksIterator) prev() ([]byte, []byte, error) {
	r.it.Prev()
	if r.it.Valid() {
		return bytes.Clone(r.it.Key().Data()), bytes.Clone(r.it.Value().Data()), nil
	}
	return nil, nil, nil
}

func (r *RocksIterator) First() ([]byte, []byte, error) {
	return r.Seek(nil)
}

func (r *RocksIterator) Count() (uint64, error) {
	return strconv.ParseUint(r.tx.kv.db.GetPropertyCF(KEY_ESTIMATE_PROP, r.cfHandle), 10, 64)
}

func (r *RocksIterator) Next() ([]byte, []byte, error) {
	k, v, err := r.next()
	if err != nil {
		return []byte{}, nil, fmt.Errorf("failed RocksDB Iterator.Next(): %w", err)
	}
	if v == nil {
		return nil, nil, nil
	}

	cfg := r.tableCfg

	if (r.tableCfg.Flags&mdbx.DupSort) == 1 && len(k) > 5 && DUP_REGEX.Match(k) {
		k = k[:len(k)-5]
	}

	if cfg.AutoDupSortKeysConversion && len(k) == cfg.DupToLen {
		keyPart := cfg.DupFromLen - cfg.DupToLen
		if len(v) == 0 {
			return nil, nil, fmt.Errorf("key with empty value: k=%x, len(k)=%d, v=%x", k, len(k), v)
		}
		k = append(k, v[:keyPart]...)
		v = v[keyPart:]
	}
	return k, v, nil
}
