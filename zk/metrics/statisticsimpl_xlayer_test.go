package metrics

import (
	"testing"
	"time"
)

func TestStatisticsInstanceSummary(t *testing.T) {
	type fields struct {
		timestamp  time.Time
		statistics map[logTag]int64
		tags       map[logTag]string
	}
	tests := []struct {
		name   string
		fields fields
		want   string
	}{
		{"1", fields{
			timestamp: time.Now().Add(-time.Second),
			statistics: map[logTag]int64{
				BatchGas:                      111111,
				TxCounter:                     10,
				GetTxTiming:                   time.Second.Milliseconds(),
				GetTxPauseCounter:             2,
				GetTxPauseTiming:              time.Second.Milliseconds() * 30,
				ReprocessingTxCounter:         3,
				FailTxGasOverCounter:          1,
				FailTxResourceOverCounter:     1,
				ZKOverflowBlockCounter:        1,
				ProcessingInvalidTxCounter:    2,
				SequencingBatchTiming:         time.Second.Milliseconds() * 20,
				ProcessingTxTiming:            time.Second.Milliseconds() * 30,
				BatchCommitDBTiming:           time.Second.Milliseconds() * 10,
				PbStateTiming:                 time.Second.Milliseconds() * 20,
				ZkIncIntermediateHashesTiming: time.Second.Milliseconds() * 15,
				FinaliseBlockWriteTiming:      time.Second.Milliseconds() * 25,
				ZKHashAccountCount:            1,
				ZKHashStoreCount:              2,
				ZKHashCodeCount:               3,

				ZKHashSMTDeleteByNodeKey: 4,
				ZKHashSMTDeleteHashKey:   5,
				ZKHashSMTInsertKey:       6,
				ZKHashSMTGetKey:          7,

				ZKHashSMTDeleteByNodeKeyTiming: 4100,
				ZKHashSMTDeleteHashKeyTiming:   5100,
				ZKHashSMTInsertKeyTiming:       6100,
				ZKHashSMTGetKeyTiming:          7100,
			},
			tags: map[logTag]string{BatchCloseReason: "deadline", FinalizeBatchNumber: "123"},
		}, "test"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			l := &statisticsInstance{
				newRoundTime: tt.fields.timestamp,
				statistics:   tt.fields.statistics,
				tags:         tt.fields.tags,
			}
			t.Log(l.Summary())
		})
	}
}
