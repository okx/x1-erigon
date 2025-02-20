package mdbx

import (
	"fmt"
	"github.com/ledgerwatch/erigon-lib/common/dbg"

	"github.com/ledgerwatch/log/v3"
)

func (opts *MdbxOpts) Print() {

	writeMap := dbg.WriteMap()

	log.Info(fmt.Sprintf(
		"MdbxOpts: Path=%s, SyncPeriod=%s, MapSize=%s, GrowthStep=%s, ShrinkThreshold=%d, Flags=%d, PageSize=%d, DirtySpace=%d, MergeThreshold=%d, Verbosity=%v, Label=%v, InMem=%v%s%s, writeMap=%v",
		opts.path, opts.syncPeriod, opts.mapSize.String(), opts.growthStep.String(),
		opts.shrinkThreshold, opts.flags, opts.pageSize, opts.dirtySpace, opts.mergeThreshold,
		opts.verbosity, opts.label, opts.inMem, writeMap,
		func() string {
			if opts.readTxLimiter != nil {
				return fmt.Sprintf(", ReadTxLimiter=%v", opts.readTxLimiter)
			}
			return ""
		}(),
		func() string {
			if opts.writeTxLimiter != nil {
				return fmt.Sprintf(", WriteTxLimiter=%v", opts.writeTxLimiter)
			}
			return ""
		}(),
	))
}
