package metrics

import (
	"fmt"
	"time"

	"github.com/ledgerwatch/log/v3"
	"github.com/prometheus/client_golang/prometheus"
)

type BatchFinalizeType string

const (
	BatchTimeOut         BatchFinalizeType = "EmptyBatchTimeOut"
	BatchCounterOverflow BatchFinalizeType = "BatchCounterOverflow"
	BatchLimboRecovery   BatchFinalizeType = "LimboRecovery"
)

var (
	SeqPrefix            = "sequencer_"
	BatchExecuteTimeName = SeqPrefix + "batch_execute_time"
	PoolTxCountName      = SeqPrefix + "pool_tx_count"
	SeqTxDurationName    = SeqPrefix + "tx_duration"
	SeqTxCountName       = SeqPrefix + "tx_count"
	SeqFailTxCountName   = SeqPrefix + "fail_tx_count"

	RpcPrefix              = "rpc_"
	RpcDynamicGasPriceName = RpcPrefix + "dynamic_gas_price"
	RpcInnerTxExecutedName = RpcPrefix + "inner_tx_executed"
)

func Init() {
	prometheus.MustRegister(BatchExecuteTimeGauge)
	prometheus.MustRegister(PoolTxCount)
	prometheus.MustRegister(RpcDynamicGasPrice)
	prometheus.MustRegister(RpcInnerTxExecuted)
	prometheus.MustRegister(SeqTxDuration)
	prometheus.MustRegister(SeqTxCount)
	prometheus.MustRegister(SeqFailTxCount)
}

var BatchExecuteTimeGauge = prometheus.NewGaugeVec(
	prometheus.GaugeOpts{
		Name: BatchExecuteTimeName,
		Help: "[SEQUENCER] batch execution time in second",
	},
	[]string{"closingReason"},
)

var PoolTxCount = prometheus.NewGaugeVec(
	prometheus.GaugeOpts{
		Name: PoolTxCountName,
		Help: "[SEQUENCER] tx count of each pool in tx pool",
	},
	[]string{"poolName"},
)

func BatchExecuteTime(closingReason string, duration time.Duration) {
	log.Info(fmt.Sprintf("[BatchExecuteTime] ClosingReason: %v, Duration: %.2fs", closingReason, duration.Seconds()))
	BatchExecuteTimeGauge.WithLabelValues(closingReason).Set(duration.Seconds())
}

func AddPoolTxCount(pending, baseFee, queued int) {
	log.Info(fmt.Sprintf("[PoolTxCount] pending: %v, basefee: %v, queued: %v", pending, baseFee, queued))
	PoolTxCount.WithLabelValues("pending").Set(float64(pending))
	PoolTxCount.WithLabelValues("basefee").Set(float64(baseFee))
	PoolTxCount.WithLabelValues("queued").Set(float64(queued))
}

var RpcDynamicGasPrice = prometheus.NewGauge(
	prometheus.GaugeOpts{
		Name: RpcDynamicGasPriceName,
		Help: "[RPC] dynamic gas price",
	},
)

var RpcInnerTxExecuted = prometheus.NewCounter(
	prometheus.CounterOpts{
		Name: RpcInnerTxExecutedName,
		Help: "[RPC] inner tx executed, used to trace contract calls in blockchain explorer",
	},
)

var SeqTxDuration = prometheus.NewSummary(
	prometheus.SummaryOpts{
		Name: SeqTxDurationName,
		Help: "[SEQUENCER] tx processing duration in microsecond",
	},
)

var SeqTxCount = prometheus.NewCounter(
	prometheus.CounterOpts{
		Name: SeqTxCountName,
		Help: "[SEQUENCER] total processed tx count",
	},
)

var SeqFailTxCount = prometheus.NewCounter(
	prometheus.CounterOpts{
		Name: SeqFailTxCountName,
		Help: "[SEQUENCER] total fail tx count",
	},
)
