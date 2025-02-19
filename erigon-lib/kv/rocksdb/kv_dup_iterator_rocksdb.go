package rocksdb

import (
	"fmt"
	"strconv"
)

const DUP_DELIMETER = ':'

type RocksDupSortIterator struct {
	*RocksIterator
}

func (ri *RocksDupSortIterator) AppendDup(k []byte, v []byte) error {
	prefix := append(k, DUP_DELIMETER)
	suffix := 0
	for ri.it.Seek(prefix); ri.it.ValidForPrefix(prefix); ri.it.Next() {
		currSuffix, err := strconv.Atoi(string(ri.it.Key().Data()[len(prefix):]))
		if err != nil {
			return err
		}
		if currSuffix >= suffix {
			suffix = currSuffix + 1
		}
	}
	suffix++
	k = append(k, []byte(fmt.Sprintf("%04d", suffix))...)

	return ri.tx.kv.db.PutCF(ri.tx.wo, ri.cfHandle, k, v)
}
