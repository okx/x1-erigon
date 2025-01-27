package keccak

import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"
	"math/big"

	"github.com/ledgerwatch/erigon/core/types"
	"github.com/ledgerwatch/erigon/rlp"

	libcommon "github.com/ledgerwatch/erigon-lib/common"
)

func populateStateAVX2(data []byte, idx int, state *[]uint64, pstart *int) {
	rate := 136
	rate_64 := rate / 8

	start := *pstart
	if start+rate <= len(data) {
		for j := 0; j < rate_64; j++ {
			(*state)[4*j+idx] ^= binary.LittleEndian.Uint64(data[start+j*8 : start+(j+1)*8])
		}
		*pstart = start + rate
	} else {
		rem_64 := (len(data) - start) / 8
		rem_bytes := (len(data) - start) % 8
		for j := 0; j < rem_64; j++ {
			(*state)[4*j+idx] ^= binary.LittleEndian.Uint64(data[start+j*8 : start+(j+1)*8])
		}
		if rem_bytes > 0 {
			buf := make([]byte, 8)
			copy(buf[:], data[start+rem_64*8:])
			(*state)[4*rem_64+idx] ^= binary.LittleEndian.Uint64(buf) | (uint64(0x1) << (rem_bytes * 8))
		} else {
			(*state)[4*rem_64+idx] ^= 0x1
		}
		(*state)[(rate_64-1)*4+idx] ^= 0x80 << 56
		*pstart = len(data) + 1
	}
}

func populateHashAVX2(state []uint64, idx int, hashes *[32]byte) {
	for j := 0; j < 4; j++ {
		binary.LittleEndian.PutUint64(
			(*hashes)[8*j:8*(j+1)],
			state[4*j+idx],
		)
	}
}

func HashKeccakAVX2(data [4][]byte) ([4][32]byte, error) {
	if !IsEnabledX4() {
		return [4][32]byte{}, errors.New("AVX2 not available")
	}

	var hashes [4][32]byte

	// f1600 acts on 1600 bits arranged as 25 uint64s.  Our fourway f1600
	// acts on four interleaved states; that is a [100]uint64.  (A separate
	// type is used to ensure that the encapsulated [100]uint64 is aligned
	// properly to be used efficiently with vector instructions.)
	var perm StateX4
	state := perm.Initialize(false)

	// state is initialized with zeroes
	start1 := 0
	start2 := 0
	start3 := 0
	start4 := 0
	done1 := false
	done2 := false
	done3 := false
	done4 := false

	for !done1 || !done2 || !done3 || !done4 {
		populateStateAVX2(data[0], 0, &state, &start1)
		populateStateAVX2(data[1], 1, &state, &start2)
		populateStateAVX2(data[2], 2, &state, &start3)
		populateStateAVX2(data[3], 3, &state, &start4)
		perm.Permute()
		if start1 == len(data[0])+1 && !done1 {
			done1 = true
			populateHashAVX2(state, 0, &hashes[0])
		}
		if start2 == len(data[1])+1 && !done2 {
			done2 = true
			populateHashAVX2(state, 1, &hashes[1])
		}
		if start3 == len(data[2])+1 && !done3 {
			done3 = true
			populateHashAVX2(state, 2, &hashes[2])
		}
		if start4 == len(data[3])+1 && !done4 {
			done4 = true
			populateHashAVX2(state, 3, &hashes[3])
		}
	}
	return hashes, nil
}

func populateStateAVX512(data []byte, idx int, state *[]uint64, pstart *int) {
	rate := 136         // absorption occurs on 136 bytes or 1088 bits known as rate
	rate_64 := rate / 8 // 17 * 64 bit chunks = 1088 bits

	start := *pstart
	if start+rate <= len(data) { // more data than rate
		for j := 0; j < rate_64; j++ { // 17 rounds
			// Each round needs 64 bits to be read into absorption i.e. 8 bytes
			(*state)[8*j+idx] ^= binary.LittleEndian.Uint64(data[start+j*8 : start+(j+1)*8])
		}
		*pstart = start + rate
	} else {
		//lesser data than rate
		rem_64 := (len(data) - start) / 8    // chunks of additional data (each chunk is 8 bytes)
		rem_bytes := (len(data) - start) % 8 // remainder bytes after above chunks
		for j := 0; j < rem_64; j++ {
			(*state)[8*j+idx] ^= binary.LittleEndian.Uint64(data[start+j*8 : start+(j+1)*8])
		}
		if rem_bytes > 0 {
			buf := make([]byte, 8)
			copy(buf[:], data[start+rem_64*8:]) //remaining bytes get copied over to the buffer
			(*state)[8*rem_64+idx] ^= binary.LittleEndian.Uint64(buf) | (uint64(0x1) << (rem_bytes * 8))
		} else {
			(*state)[8*rem_64+idx] ^= 0x1
		}
		(*state)[(rate_64-1)*8+idx] ^= 0x80 << 56 // according to https://cs.opensource.google/go/x/crypto/+/master:sha3/sha3.go
		*pstart = len(data) + 1                   // stop condition is start == len(data) + 1
	}
}

func populateHashAVX512(state []uint64, idx int, hashes *[32]byte) {
	for j := 0; j < 4; j++ {
		binary.LittleEndian.PutUint64(
			(*hashes)[8*j:8*(j+1)],
			state[8*j+idx],
		)
	}
}

func HashKeccakAVX512(data [8][]byte) ([8][32]byte, error) {
	if !IsEnabledX8() {
		return [8][32]byte{}, errors.New("AVX512 not available")
	}

	// f1600 acts on 1600 bits arranged as 25 uint64s.  Our eightway f1600
	// acts on eight interleaved states; that is a [200]uint64.  (A separate
	// type is used to ensure that the encapsulated [200]uint64 is aligned
	// properly to be used efficiently with vector instructions.)
	var hashes [8][32]byte
	var perm StateX8
	state := perm.Initialize(false)

	start1 := 0
	start2 := 0
	start3 := 0
	start4 := 0
	start5 := 0
	start6 := 0
	start7 := 0
	start8 := 0
	done1 := false
	done2 := false
	done3 := false
	done4 := false
	done5 := false
	done6 := false
	done7 := false
	done8 := false

	for !done1 || !done2 || !done3 || !done4 || !done5 || !done6 || !done7 || !done8 {
		populateStateAVX512(data[0], 0, &state, &start1)
		populateStateAVX512(data[1], 1, &state, &start2)
		populateStateAVX512(data[2], 2, &state, &start3)
		populateStateAVX512(data[3], 3, &state, &start4)
		populateStateAVX512(data[4], 4, &state, &start5)
		populateStateAVX512(data[5], 5, &state, &start6)
		populateStateAVX512(data[6], 6, &state, &start7)
		populateStateAVX512(data[7], 7, &state, &start8)
		perm.Permute()
		if start1 == len(data[0])+1 && !done1 {
			done1 = true
			populateHashAVX512(state, 0, &hashes[0])
		}

		if start2 == len(data[1])+1 && !done2 {
			done2 = true
			populateHashAVX512(state, 1, &hashes[1])
		}

		if start3 == len(data[2])+1 && !done3 {
			done3 = true
			populateHashAVX512(state, 2, &hashes[2])
		}

		if start4 == len(data[3])+1 && !done4 {
			done4 = true
			populateHashAVX512(state, 3, &hashes[3])
		}

		if start5 == len(data[4])+1 && !done5 {
			done5 = true
			populateHashAVX512(state, 4, &hashes[4])
		}

		if start6 == len(data[5])+1 && !done6 {
			done6 = true
			populateHashAVX512(state, 5, &hashes[5])
		}

		if start7 == len(data[6])+1 && !done7 {
			done7 = true
			populateHashAVX512(state, 6, &hashes[6])
		}

		if start8 == len(data[7])+1 && !done8 {
			done8 = true
			populateHashAVX512(state, 7, &hashes[7])
		}
	}

	return hashes, nil
}

func SigningHashAVX(chainID *big.Int, txs []types.Transaction, h []libcommon.Hash, isAVX512 bool) error {
	var buf [8]bytes.Buffer
	lanes := 4
	if isAVX512 {
		lanes = 8
	}
	for i := 0; i < lanes; i++ {
		switch t := txs[i].(type) {
		case *types.LegacyTx:
			signChainID := chainID
			if !t.Protected() {
				signChainID = nil
			}
			if signChainID != nil && signChainID.Sign() != 0 {
				y := []interface{}{
					t.Nonce,
					t.GasPrice,
					t.Gas,
					t.To,
					t.Value,
					t.Data,
					signChainID, uint(0), uint(0),
				}
				rlp.Encode(&buf[i], y)
			} else {
				y := []interface{}{
					t.Nonce,
					t.GasPrice,
					t.Gas,
					t.To,
					t.Value,
					t.Data,
				}
				rlp.Encode(&buf[i], y)
			}
		case *types.AccessListTx:
			buf[i].Write([]byte{byte(types.AccessListTxType)})
			y := []interface{}{
				chainID,
				t.Nonce,
				t.GasPrice,
				t.Gas,
				t.To,
				t.Value,
				t.Data,
				t.AccessList,
			}
			rlp.Encode(&buf[i], y)
		case *types.DynamicFeeTransaction:
			buf[i].Write([]byte{byte(types.DynamicFeeTxType)})
			y := []interface{}{
				chainID,
				t.Nonce,
				t.Tip,
				t.FeeCap,
				t.Gas,
				t.To,
				t.Value,
				t.Data,
				t.AccessList,
			}
			rlp.Encode(&buf[i], y)
		case *types.BlobTx:
			buf[i].Write([]byte{byte(types.BlobTxType)})
			y := []interface{}{
				chainID,
				t.Nonce,
				t.Tip,
				t.FeeCap,
				t.Gas,
				t.To,
				t.Value,
				t.Data,
				t.AccessList,
				t.MaxFeePerBlobGas,
				t.BlobVersionedHashes,
			}
			rlp.Encode(&buf[i], y)
		default:
			err := fmt.Errorf("SigningHashAVX2() transaction type not supported")
			return err
		}
	}
	if isAVX512 {
		hashes, err := HashKeccakAVX512([8][]byte{buf[0].Bytes(), buf[1].Bytes(), buf[2].Bytes(), buf[3].Bytes(), buf[4].Bytes(), buf[5].Bytes(), buf[6].Bytes(), buf[7].Bytes()})
		if err != nil {
			err = fmt.Errorf("SigningHashAVX() Error: %v", err)
			return err
		}
		for i := 0; i < lanes; i++ {
			h[i] = libcommon.BytesToHash(hashes[i][:])
		}
	} else {
		hashes, err := HashKeccakAVX2([4][]byte{buf[0].Bytes(), buf[1].Bytes(), buf[2].Bytes(), buf[3].Bytes()})
		if err != nil {
			err = fmt.Errorf("SigningHashAVX() Error: %v", err)
			return err
		}
		for i := 0; i < lanes; i++ {
			h[i] = libcommon.BytesToHash(hashes[i][:])
		}
	}
	return nil
}

func RlpHashAVX(txs []types.Transaction, h []libcommon.Hash, isAVX512 bool) error {
	var buf [8]bytes.Buffer
	lanes := 4
	if isAVX512 {
		lanes = 8
	}
	for i := 0; i < lanes; i++ {
		txs[i].EncodeRLP(&buf[i])
	}
	if isAVX512 {
		hashes, err := HashKeccakAVX512([8][]byte{buf[0].Bytes(), buf[1].Bytes(), buf[2].Bytes(), buf[3].Bytes(), buf[4].Bytes(), buf[5].Bytes(), buf[6].Bytes(), buf[7].Bytes()})
		if err != nil {
			err = fmt.Errorf("RlpHashAVX512() Error: %v", err)
			return err
		}
		for i := 0; i < lanes; i++ {
			h[i] = libcommon.BytesToHash(hashes[i][:])
		}
	} else {
		hashes, err := HashKeccakAVX2([4][]byte{buf[0].Bytes(), buf[1].Bytes(), buf[2].Bytes(), buf[3].Bytes()})
		if err != nil {
			err = fmt.Errorf("RlpHashAVX() Error: %v", err)
			return err
		}
		for i := 0; i < lanes; i++ {
			h[i] = libcommon.BytesToHash(hashes[i][:])
		}
	}
	return nil
}
