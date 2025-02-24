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

package chain

import (
	"encoding/json"
	"fmt"
	"math/big"
	"strconv"

	"github.com/ledgerwatch/erigon-lib/common"
	"github.com/ledgerwatch/erigon-lib/common/fixedgas"
)

// this needs to always be in descending order
// add new forkIds at the beginning of the array
var ForkIdsOrdered = []ForkId{
	ForkId13Durian,
	ForkID12Banana,
	ForkID11,
	ForkID10,
	ForkID9Elderberry2,
	ForkID8Elderberry,
	ForkID7Etrog,
	ForkID6IncaBerry,
	ForkID5Dragonfruit,
	ForkID4,
}

// Config is the core config which determines the blockchain settings.
//
// Config is stored in the database on a per block basis. This means
// that any network, identified by its genesis block, can have its own
// set of configuration options.
type Config struct {
	ChainName string   `json:"chainName"` // chain name, eg: mainnet, sepolia, bor-mainnet
	ChainID   *big.Int `json:"chainId"`   // chainId identifies the current chain and is used for replay protection

	Consensus ConsensusName `json:"consensus,omitempty"` // aura, ethash or clique

	// *Block fields activate the corresponding hard fork at a certain block number,
	// while *Time fields do so based on the block's time stamp.
	// nil means that the hard-fork is not scheduled,
	// while 0 means that it's already activated from genesis.

	// ETH mainnet upgrades
	// See https://github.com/ethereum/execution-specs/blob/master/network-upgrades/mainnet-upgrades
	HomesteadBlock        *big.Int `json:"homesteadBlock,omitempty"`
	DAOForkBlock          *big.Int `json:"daoForkBlock,omitempty"`
	TangerineWhistleBlock *big.Int `json:"eip150Block,omitempty"`
	SpuriousDragonBlock   *big.Int `json:"eip155Block,omitempty"`
	ByzantiumBlock        *big.Int `json:"byzantiumBlock,omitempty"`
	ConstantinopleBlock   *big.Int `json:"constantinopleBlock,omitempty"`
	PetersburgBlock       *big.Int `json:"petersburgBlock,omitempty"`
	IstanbulBlock         *big.Int `json:"istanbulBlock,omitempty"`
	MuirGlacierBlock      *big.Int `json:"muirGlacierBlock,omitempty"`
	BerlinBlock           *big.Int `json:"berlinBlock,omitempty"`
	LondonBlock           *big.Int `json:"londonBlock,omitempty"`
	ArrowGlacierBlock     *big.Int `json:"arrowGlacierBlock,omitempty"`
	GrayGlacierBlock      *big.Int `json:"grayGlacierBlock,omitempty"`

	// EIP-3675: Upgrade consensus to Proof-of-Stake (a.k.a. "Paris", "The Merge")
	TerminalTotalDifficulty       *big.Int `json:"terminalTotalDifficulty,omitempty"`       // The merge happens when terminal total difficulty is reached
	TerminalTotalDifficultyPassed bool     `json:"terminalTotalDifficultyPassed,omitempty"` // Disable PoW sync for networks that have already passed through the Merge
	MergeNetsplitBlock            *big.Int `json:"mergeNetsplitBlock,omitempty"`            // Virtual fork after The Merge to use as a network splitter; see FORK_NEXT_VALUE in EIP-3675

	// Mainnet fork scheduling switched from block numbers to timestamps after The Merge
	ShanghaiTime *big.Int `json:"shanghaiTime,omitempty"`
	CancunTime   *big.Int `json:"cancunTime,omitempty"`
	PragueTime   *big.Int `json:"pragueTime,omitempty"`
	OsakaTime    *big.Int `json:"osakaTime,omitempty"`

	// Optional EIP-4844 parameters
	MinBlobGasPrice            *uint64 `json:"minBlobGasPrice,omitempty"`
	MaxBlobGasPerBlock         *uint64 `json:"maxBlobGasPerBlock,omitempty"`
	TargetBlobGasPerBlock      *uint64 `json:"targetBlobGasPerBlock,omitempty"`
	BlobGasPriceUpdateFraction *uint64 `json:"blobGasPriceUpdateFraction,omitempty"`

	// (Optional) governance contract where EIP-1559 fees will be sent to that otherwise would be burnt since the London fork
	BurntContract map[string]common.Address `json:"burntContract,omitempty"`

	// Various consensus engines
	Ethash *EthashConfig `json:"ethash,omitempty"`
	Clique *CliqueConfig `json:"clique,omitempty"`
	Aura   *AuRaConfig   `json:"aura,omitempty"`

	Bor     BorConfig       `json:"-"`
	BorJSON json.RawMessage `json:"bor,omitempty"`

	// For not pruning the logs of these contracts
	// For deposit contract logs are needed by CL to validate/produce blocks.
	// All logs should be available to a validating node through eth_getLogs
	NoPruneContracts map[common.Address]bool `json:"noPruneContracts,omitempty"`

	//zkEVM updates
	ForkID4Block            *big.Int `json:"forkID4Block,omitempty"`
	ForkID5DragonfruitBlock *big.Int `json:"forkID5DragonfruitBlock,omitempty"`
	ForkID6IncaBerryBlock   *big.Int `json:"forkID6IncaBerryBlock,omitempty"`
	ForkID7EtrogBlock       *big.Int `json:"forkID7EtrogBlock,omitempty"`
	ForkID88ElderberryBlock *big.Int `json:"forkID88ElderberryBlock,omitempty"`
	ForkID9Elderberry2Block *big.Int `json:"forkID9FeijoaBlock,omitempty"`
	ForkID10                *big.Int `json:"forkID10,omitempty"`
	ForkID11                *big.Int `json:"forkID11,omitempty"`
	ForkID12BananaBlock     *big.Int `json:"forkID12BananaBlock,omitempty"`
	ForkId13Durian          *big.Int `json:"forkID13Durian,omitempty"`
	NormalcyBlock           *big.Int `json:"normalcyBlock,omitempty"`

	AllowFreeTransactions bool   `json:"allowFreeTransactions,omitempty"`
	ZkDefaultGasPrice     uint64 `json:"zkDefaultGasFee,omitempty"`
}

type BorConfig interface {
	fmt.Stringer
	IsAgra(num uint64) bool
	GetAgraBlock() *big.Int
	IsNapoli(num uint64) bool
	GetNapoliBlock() *big.Int
}

func (c *Config) String() string {
	engine := c.getEngine()

	return fmt.Sprintf("{ChainID: %v, Homestead: %v, DAO: %v, Tangerine Whistle: %v, Spurious Dragon: %v, Byzantium: %v, Constantinople: %v, Petersburg: %v, Istanbul: %v, Muir Glacier: %v, Berlin: %v, London: %v, Arrow Glacier: %v, Gray Glacier: %v, Terminal Total Difficulty: %v, Merge Netsplit: %v, Shanghai: %v, Cancun: %v, Prague: %v, Osaka: %v, Normalcy: %v, Engine: %v, NoPruneContracts: %v}",
		c.ChainID,
		c.HomesteadBlock,
		c.DAOForkBlock,
		c.TangerineWhistleBlock,
		c.SpuriousDragonBlock,
		c.ByzantiumBlock,
		c.ConstantinopleBlock,
		c.PetersburgBlock,
		c.IstanbulBlock,
		c.MuirGlacierBlock,
		c.BerlinBlock,
		c.LondonBlock,
		c.ArrowGlacierBlock,
		c.GrayGlacierBlock,
		c.TerminalTotalDifficulty,
		c.MergeNetsplitBlock,
		c.ShanghaiTime,
		c.CancunTime,
		c.PragueTime,
		c.OsakaTime,
		c.NormalcyBlock,
		engine,
		c.NoPruneContracts,
	)
}

func (c *Config) SetForkIdBlock(forkIdNumber ForkId, blockNum uint64) error {
	switch forkIdNumber {
	case ForkID4:
		c.ForkID4Block = new(big.Int).SetUint64(blockNum)
	case ForkID5Dragonfruit:
		c.ForkID5DragonfruitBlock = new(big.Int).SetUint64(blockNum)
	case ForkID6IncaBerry:
		c.ForkID6IncaBerryBlock = new(big.Int).SetUint64(blockNum)
	case ForkID7Etrog:
		c.ForkID7EtrogBlock = new(big.Int).SetUint64(blockNum)
	case ForkID8Elderberry:
		c.ForkID88ElderberryBlock = new(big.Int).SetUint64(blockNum)
	case ForkID9Elderberry2:
		c.ForkID9Elderberry2Block = new(big.Int).SetUint64(blockNum)
	case ForkID10:
		c.ForkID10 = new(big.Int).SetUint64(blockNum)
	case ForkID11:
		c.ForkID11 = new(big.Int).SetUint64(blockNum)
	case ForkID12Banana:
		c.ForkID12BananaBlock = new(big.Int).SetUint64(blockNum)
	case ForkId13Durian:
		c.ForkId13Durian = new(big.Int).SetUint64(blockNum)
	default:
		return fmt.Errorf("unknown fork id number %d", forkIdNumber)
	}

	return nil
}

func (c *Config) getEngine() string {
	switch {
	case c.Ethash != nil:
		return c.Ethash.String()
	case c.Clique != nil:
		return c.Clique.String()
	case c.Bor != nil:
		return c.Bor.String()
	case c.Aura != nil:
		return c.Aura.String()
	default:
		return "unknown"
	}
}

// IsHomestead returns whether num is either equal to the homestead block or greater.
func (c *Config) IsHomestead(num uint64) bool {
	return isForked(c.HomesteadBlock, num)
}

// IsDAOFork returns whether num is either equal to the DAO fork block or greater.
func (c *Config) IsDAOFork(num uint64) bool {
	return isForked(c.DAOForkBlock, num)
}

// IsTangerineWhistle returns whether num is either equal to the Tangerine Whistle (EIP150) fork block or greater.
func (c *Config) IsTangerineWhistle(num uint64) bool {
	return isForked(c.TangerineWhistleBlock, num)
}

// IsSpuriousDragon returns whether num is either equal to the Spurious Dragon fork block or greater.
func (c *Config) IsSpuriousDragon(num uint64) bool {
	return isForked(c.SpuriousDragonBlock, num)
}

// IsByzantium returns whether num is either equal to the Byzantium fork block or greater.
func (c *Config) IsByzantium(num uint64) bool {
	return isForked(c.ByzantiumBlock, num)
}

// IsConstantinople returns whether num is either equal to the Constantinople fork block or greater.
func (c *Config) IsConstantinople(num uint64) bool {
	return isForked(c.ConstantinopleBlock, num)
}

// IsMuirGlacier returns whether num is either equal to the Muir Glacier (EIP-2384) fork block or greater.
func (c *Config) IsMuirGlacier(num uint64) bool {
	return isForked(c.MuirGlacierBlock, num)
}

// IsPetersburg returns whether num is either
// - equal to or greater than the PetersburgBlock fork block,
// - OR is nil, and Constantinople is active
func (c *Config) IsPetersburg(num uint64) bool {
	return isForked(c.PetersburgBlock, num) || c.PetersburgBlock == nil && isForked(c.ConstantinopleBlock, num)
}

// IsIstanbul returns whether num is either equal to the Istanbul fork block or greater.
func (c *Config) IsIstanbul(num uint64) bool {
	return isForked(c.IstanbulBlock, num)
}

// IsBerlin returns whether num is either equal to the Berlin fork block or greater.
func (c *Config) IsBerlin(num uint64) bool {
	return isForked(c.BerlinBlock, num)
}

// IsLondon returns whether num is either equal to the London fork block or greater.
func (c *Config) IsLondon(num uint64) bool {
	return isForked(c.LondonBlock, num)
}

// IsArrowGlacier returns whether num is either equal to the Arrow Glacier (EIP-4345) fork block or greater.
func (c *Config) IsArrowGlacier(num uint64) bool {
	return isForked(c.ArrowGlacierBlock, num)
}

// IsGrayGlacier returns whether num is either equal to the Gray Glacier (EIP-5133) fork block or greater.
func (c *Config) IsGrayGlacier(num uint64) bool {
	return isForked(c.GrayGlacierBlock, num)
}

// IsShanghai returns whether time is either equal to the Shanghai fork time or greater.
func (c *Config) IsShanghai(time uint64) bool {
	return isForked(c.ShanghaiTime, time)
}

// IsAgra returns whether num is either equal to the Agra fork block or greater.
// The Agra hard fork is based on the Shanghai hard fork, but it doesn't include withdrawals.
// Also Agra is activated based on the block number rather than the timestamp.
// Refer to https://forum.polygon.technology/t/pip-28-agra-hardfork
func (c *Config) IsAgra(num uint64) bool {
	return (c != nil) && (c.Bor != nil) && c.Bor.IsAgra(num)
}

// Refer to https://forum.polygon.technology/t/pip-33-napoli-upgrade
func (c *Config) IsNapoli(num uint64) bool {
	return (c != nil) && (c.Bor != nil) && c.Bor.IsNapoli(num)
}

// IsCancun returns whether time is either equal to the Cancun fork time or greater.
func (c *Config) IsCancun(time uint64) bool {
	return isForked(c.CancunTime, time)
}

// IsPrague returns whether time is either equal to the Prague fork time or greater.
func (c *Config) IsPrague(time uint64) bool {
	return isForked(c.PragueTime, time)
}

// IsOsaka returns whether time is either equal to the Osaka fork time or greater.
func (c *Config) IsOsaka(time uint64) bool {
	return isForked(c.OsakaTime, time)
}

func (c *Config) GetBurntContract(num uint64) *common.Address {
	if len(c.BurntContract) == 0 {
		return nil
	}
	addr := borKeyValueConfigHelper(c.BurntContract, num)
	return &addr
}

func (c *Config) GetMinBlobGasPrice() uint64 {
	if c != nil && c.MinBlobGasPrice != nil {
		return *c.MinBlobGasPrice
	}
	return 1 // MIN_BLOB_GASPRICE (EIP-4844)
}

func (c *Config) GetMaxBlobGasPerBlock() uint64 {
	if c != nil && c.MaxBlobGasPerBlock != nil {
		return *c.MaxBlobGasPerBlock
	}
	return 786432 // MAX_BLOB_GAS_PER_BLOCK (EIP-4844)
}

func (c *Config) GetTargetBlobGasPerBlock() uint64 {
	if c != nil && c.TargetBlobGasPerBlock != nil {
		return *c.TargetBlobGasPerBlock
	}
	return 393216 // TARGET_BLOB_GAS_PER_BLOCK (EIP-4844)
}

func (c *Config) GetBlobGasPriceUpdateFraction() uint64 {
	if c != nil && c.BlobGasPriceUpdateFraction != nil {
		return *c.BlobGasPriceUpdateFraction
	}
	return 3338477 // BLOB_GASPRICE_UPDATE_FRACTION (EIP-4844)
}

func (c *Config) GetMaxBlobsPerBlock() uint64 {
	return c.GetMaxBlobGasPerBlock() / fixedgas.BlobGasPerBlob
}

func (c *Config) IsNormalcy(num uint64) bool {
	return isForked(c.NormalcyBlock, num)
}

func (c *Config) IsForkID4(num uint64) bool {
	return isForked(c.ForkID4Block, num)
}

func (c *Config) IsForkID5Dragonfruit(num uint64) bool {
	return isForked(c.ForkID5DragonfruitBlock, num)
}

func (c *Config) IsForkID6IncaBerry(num uint64) bool {
	return isForked(c.ForkID6IncaBerryBlock, num)
}

func (c *Config) IsForkID7Etrog(num uint64) bool {
	return isForked(c.ForkID7EtrogBlock, num)
}

func (c *Config) IsForkID8Elderberry(num uint64) bool {
	return isForked(c.ForkID88ElderberryBlock, num)
}

func (c *Config) IsForkId9Elderberry2(num uint64) bool {
	return isForked(c.ForkID9Elderberry2Block, num)
}
func (c *Config) IsForkID10(num uint64) bool {
	return isForked(c.ForkID10, num)
}
func (c *Config) IsForkID11(num uint64) bool {
	return isForked(c.ForkID11, num)
}

func (c *Config) IsForkID12Banana(num uint64) bool {
	return isForked(c.ForkID12BananaBlock, num)
}

func (c *Config) IsForkID13Durian(num uint64) bool {
	return isForked(c.ForkId13Durian, num)
}

// CheckCompatible checks whether scheduled fork transitions have been imported
// with a mismatching chain configuration.
func (c *Config) CheckCompatible(newcfg *Config, height uint64) *ConfigCompatError {
	bhead := height

	// Iterate checkCompatible to find the lowest conflict.
	var lasterr *ConfigCompatError
	for {
		err := c.checkCompatible(newcfg, bhead)
		if err == nil || (lasterr != nil && err.RewindTo == lasterr.RewindTo) {
			break
		}
		lasterr = err
		bhead = err.RewindTo
	}
	return lasterr
}

//////////////// not used currently due to dynamic fork
// type forkBlockNumber struct {
// 	name        string
// 	blockNumber *big.Int
// 	optional    bool // if true, the fork may be nil and next fork is still allowed
// }

//	func (c *Config) forkBlockNumbers() []forkBlockNumber {
//		return []forkBlockNumber{
//			{name: "homesteadBlock", blockNumber: c.HomesteadBlock},
//			{name: "daoForkBlock", blockNumber: c.DAOForkBlock, optional: true},
//			{name: "eip150Block", blockNumber: c.TangerineWhistleBlock},
//			{name: "eip155Block", blockNumber: c.SpuriousDragonBlock},
//			{name: "byzantiumBlock", blockNumber: c.ByzantiumBlock},
//			{name: "constantinopleBlock", blockNumber: c.ConstantinopleBlock},
//			{name: "petersburgBlock", blockNumber: c.PetersburgBlock},
//			{name: "istanbulBlock", blockNumber: c.IstanbulBlock},
//			{name: "muirGlacierBlock", blockNumber: c.MuirGlacierBlock, optional: true},
//			{name: "berlinBlock", blockNumber: c.BerlinBlock},
//			{name: "londonBlock", blockNumber: c.LondonBlock},
//			{name: "arrowGlacierBlock", blockNumber: c.ArrowGlacierBlock, optional: true},
//			{name: "grayGlacierBlock", blockNumber: c.GrayGlacierBlock, optional: true},
//			{name: "mergeNetsplitBlock", blockNumber: c.MergeNetsplitBlock, optional: true},
//		}
//	}
//
// ////////////////////////
// CheckConfigForkOrder checks that we don't "skip" any forks
func (c *Config) CheckConfigForkOrder() error {
	if c != nil && c.ChainID != nil && c.ChainID.Uint64() == 77 {
		return nil
	}

	if c != nil && IsZk(c.ChainID.Uint64()) {
		return CheckForkOrder()
	}

	// todo: upstream merge
	// [dynamic fork]
	return nil

	//////////////// not used currently due to dynamic fork

	// var lastFork forkBlockNumber

	// for _, fork := range c.forkBlockNumbers() {
	// 	if lastFork.name != "" {
	// 		// Next one must be higher number
	// 		if lastFork.blockNumber == nil && fork.blockNumber != nil {
	// 			return fmt.Errorf("unsupported fork ordering: %v not enabled, but %v enabled at %v",
	// 				lastFork.name, fork.name, fork.blockNumber)
	// 		}
	// 		if lastFork.blockNumber != nil && fork.blockNumber != nil {
	// 			if lastFork.blockNumber.Cmp(fork.blockNumber) > 0 {
	// 				return fmt.Errorf("unsupported fork ordering: %v enabled at %v, but %v enabled at %v",
	// 					lastFork.name, lastFork.blockNumber, fork.name, fork.blockNumber)
	// 			}
	// 		}
	// 		// If it was optional and not set, then ignore it
	// 	}
	// 	if !fork.optional || fork.blockNumber != nil {
	// 		lastFork = fork
	// 	}
	// }
	// return nil
	//////////////////////////

}

func (c *Config) checkCompatible(newcfg *Config, head uint64) *ConfigCompatError {
	// returns true if a fork scheduled at s1 cannot be rescheduled to block s2 because head is already past the fork.
	incompatible := func(s1, s2 *big.Int, head uint64) bool {
		return (isForked(s1, head) || isForked(s2, head)) && !numEqual(s1, s2)
	}

	// Ethereum mainnet forks
	if incompatible(c.HomesteadBlock, newcfg.HomesteadBlock, head) {
		return newCompatError("Homestead fork block", c.HomesteadBlock, newcfg.HomesteadBlock)
	}
	if incompatible(c.DAOForkBlock, newcfg.DAOForkBlock, head) {
		return newCompatError("DAO fork block", c.DAOForkBlock, newcfg.DAOForkBlock)
	}
	if incompatible(c.TangerineWhistleBlock, newcfg.TangerineWhistleBlock, head) {
		return newCompatError("Tangerine Whistle fork block", c.TangerineWhistleBlock, newcfg.TangerineWhistleBlock)
	}
	if incompatible(c.SpuriousDragonBlock, newcfg.SpuriousDragonBlock, head) {
		return newCompatError("Spurious Dragon fork block", c.SpuriousDragonBlock, newcfg.SpuriousDragonBlock)
	}
	if c.IsSpuriousDragon(head) && !numEqual(c.ChainID, newcfg.ChainID) {
		return newCompatError("EIP155 chain ID", c.SpuriousDragonBlock, newcfg.SpuriousDragonBlock)
	}
	if incompatible(c.ByzantiumBlock, newcfg.ByzantiumBlock, head) {
		return newCompatError("Byzantium fork block", c.ByzantiumBlock, newcfg.ByzantiumBlock)
	}
	if incompatible(c.ConstantinopleBlock, newcfg.ConstantinopleBlock, head) {
		return newCompatError("Constantinople fork block", c.ConstantinopleBlock, newcfg.ConstantinopleBlock)
	}
	if incompatible(c.PetersburgBlock, newcfg.PetersburgBlock, head) {
		// the only case where we allow Petersburg to be set in the past is if it is equal to Constantinople
		// mainly to satisfy fork ordering requirements which state that Petersburg fork be set if Constantinople fork is set
		if incompatible(c.ConstantinopleBlock, newcfg.PetersburgBlock, head) {
			return newCompatError("Petersburg fork block", c.PetersburgBlock, newcfg.PetersburgBlock)
		}
	}
	if incompatible(c.IstanbulBlock, newcfg.IstanbulBlock, head) {
		return newCompatError("Istanbul fork block", c.IstanbulBlock, newcfg.IstanbulBlock)
	}
	if incompatible(c.MuirGlacierBlock, newcfg.MuirGlacierBlock, head) {
		return newCompatError("Muir Glacier fork block", c.MuirGlacierBlock, newcfg.MuirGlacierBlock)
	}
	if incompatible(c.BerlinBlock, newcfg.BerlinBlock, head) {
		return newCompatError("Berlin fork block", c.BerlinBlock, newcfg.BerlinBlock)
	}
	if incompatible(c.LondonBlock, newcfg.LondonBlock, head) {
		return newCompatError("London fork block", c.LondonBlock, newcfg.LondonBlock)
	}
	if incompatible(c.ArrowGlacierBlock, newcfg.ArrowGlacierBlock, head) {
		return newCompatError("Arrow Glacier fork block", c.ArrowGlacierBlock, newcfg.ArrowGlacierBlock)
	}
	if incompatible(c.GrayGlacierBlock, newcfg.GrayGlacierBlock, head) {
		return newCompatError("Gray Glacier fork block", c.GrayGlacierBlock, newcfg.GrayGlacierBlock)
	}
	if incompatible(c.MergeNetsplitBlock, newcfg.MergeNetsplitBlock, head) {
		return newCompatError("Merge netsplit block", c.MergeNetsplitBlock, newcfg.MergeNetsplitBlock)
	}
	if incompatible(c.NormalcyBlock, newcfg.NormalcyBlock, head) {
		return newCompatError("London fork block", c.NormalcyBlock, newcfg.NormalcyBlock)
	}

	return nil
}

func numEqual(x, y *big.Int) bool {
	if x == nil {
		return y == nil
	}
	if y == nil {
		return x == nil
	}
	return x.Cmp(y) == 0
}

// ConfigCompatError is raised if the locally-stored blockchain is initialised with a
// ChainConfig that would alter the past.
type ConfigCompatError struct {
	What string
	// block numbers of the stored and new configurations
	StoredConfig, NewConfig *big.Int
	// the block number to which the local chain must be rewound to correct the error
	RewindTo uint64
}

func newCompatError(what string, storedblock, newblock *big.Int) *ConfigCompatError {
	var rew *big.Int
	switch {
	case storedblock == nil:
		rew = newblock
	case newblock == nil || storedblock.Cmp(newblock) < 0:
		rew = storedblock
	default:
		rew = newblock
	}
	err := &ConfigCompatError{what, storedblock, newblock, 0}
	if rew != nil && rew.Sign() > 0 {
		err.RewindTo = rew.Uint64() - 1
	}
	return err
}

func (err *ConfigCompatError) Error() string {
	return fmt.Sprintf("mismatching %s in database (have %d, want %d, rewindto %d)", err.What, err.StoredConfig, err.NewConfig, err.RewindTo)
}

// EthashConfig is the consensus engine configs for proof-of-work based sealing.
type EthashConfig struct{}

// String implements the stringer interface, returning the consensus engine details.
func (c *EthashConfig) String() string {
	return "ethash"
}

// CliqueConfig is the consensus engine configs for proof-of-authority based sealing.
type CliqueConfig struct {
	Period uint64 `json:"period"` // Number of seconds between blocks to enforce
	Epoch  uint64 `json:"epoch"`  // Epoch length to reset votes and checkpoint
}

// String implements the stringer interface, returning the consensus engine details.
func (c *CliqueConfig) String() string {
	return "clique"
}

func borKeyValueConfigHelper[T uint64 | common.Address](field map[string]T, number uint64) T {
	fieldUint := make(map[uint64]T)
	for k, v := range field {
		keyUint, err := strconv.ParseUint(k, 10, 64)
		if err != nil {
			panic(err)
		}
		fieldUint[keyUint] = v
	}

	keys := common.SortedKeys(fieldUint)

	for i := 0; i < len(keys)-1; i++ {
		if number >= keys[i] && number < keys[i+1] {
			return fieldUint[keys[i]]
		}
	}

	return fieldUint[keys[len(keys)-1]]
}

// Rules is syntactic sugar over Config. It can be used for functions
// that do not have or require information about the block.
//
// Rules is a one time interface meaning that it shouldn't be used in between transition
// phases.
type Rules struct {
	ChainID                                                                                                                                              *big.Int
	IsHomestead, IsTangerineWhistle, IsSpuriousDragon                                                                                                    bool
	IsByzantium, IsConstantinople, IsPetersburg                                                                                                          bool
	IsIstanbul, IsBerlin, IsLondon, IsShanghai                                                                                                           bool
	IsCancun, IsNapoli                                                                                                                                   bool
	IsPrague, isOsaka                                                                                                                                    bool
	IsAura                                                                                                                                               bool
	IsNormalcy                                                                                                                                           bool
	IsForkID4, IsForkID5Dragonfruit, IsForkID6IncaBerry, IsForkID7Etrog, IsForkID8Elderberry, IsForkId10, IsForkId11, IsForkID12Banana, IsForkID13Durian bool
}

// Rules ensures c's ChainID is not nil and returns a new Rules instance
func (c *Config) Rules(num uint64, time uint64) *Rules {
	chainID := c.ChainID
	if chainID == nil {
		chainID = new(big.Int)
	}

	return &Rules{
		ChainID:              new(big.Int).Set(chainID),
		IsHomestead:          c.IsHomestead(num),
		IsTangerineWhistle:   c.IsTangerineWhistle(num),
		IsSpuriousDragon:     c.IsSpuriousDragon(num),
		IsByzantium:          c.IsByzantium(num),
		IsConstantinople:     c.IsConstantinople(num),
		IsPetersburg:         c.IsPetersburg(num),
		IsIstanbul:           c.IsIstanbul(num),
		IsBerlin:             c.IsBerlin(num),
		IsLondon:             c.IsLondon(num),
		IsShanghai:           c.IsShanghai(time) || c.IsAgra(num),
		IsCancun:             c.IsCancun(time),
		IsNapoli:             c.IsNapoli(num),
		IsPrague:             c.IsPrague(time),
		isOsaka:              c.IsOsaka(time),
		IsNormalcy:           c.IsNormalcy(num),
		IsAura:               c.Aura != nil,
		IsForkID4:            c.IsForkID4(num),
		IsForkID5Dragonfruit: c.IsForkID5Dragonfruit(num),
		IsForkID6IncaBerry:   c.IsForkID6IncaBerry(num),
		IsForkID7Etrog:       c.IsForkID7Etrog(num),
		IsForkID8Elderberry:  c.IsForkID8Elderberry(num),
		IsForkId10:           c.IsForkID10(num),
		IsForkId11:           c.IsForkID11(num),
		IsForkID12Banana:     c.IsForkID12Banana(num),
		IsForkID13Durian:     c.IsForkID13Durian(num),
	}
}

// isForked returns whether a fork scheduled at block s is active at the given head block.
func isForked(s *big.Int, head uint64) bool {
	if s == nil {
		return false
	}
	return s.Uint64() <= head
}
