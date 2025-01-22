package sha3

import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"

	"github.com/cloudflare/circl/simd/keccakf1600"
	"github.com/ledgerwatch/erigon/core/types"

	libcommon "github.com/ledgerwatch/erigon-lib/common"
)

func populateState(data []byte, idx int, state *[]uint64, pstart *int) {
	rate := 136
	rate_64 := rate / 8

	start := *pstart
	if start+rate <= len(data) {
		for j := 0; j < rate_64; j++ {
			(*state)[4*j+idx] = binary.LittleEndian.Uint64(data[start+j*8 : start+(j+1)*8])
		}
		*pstart = start + rate
	} else {
		rem_64 := (len(data) - start) / 8
		rem_bytes := (len(data) - start) % 8
		for j := 0; j < rem_64; j++ {
			(*state)[4*j+idx] = binary.LittleEndian.Uint64(data[start+j*8 : start+(j+1)*8])
		}
		if rem_bytes > 0 {
			buf := make([]byte, 8)
			copy(buf[:], data[start+rem_64*8:])
			(*state)[4*rem_64+idx] = binary.LittleEndian.Uint64(buf) | (uint64(0x1) << (rem_bytes * 8))
		} else {
			(*state)[4*rem_64+idx] = 0x1
		}
		(*state)[(rate_64-1)*4+idx] = 0x80 << 56
		*pstart = len(data)
	}
}

func populateHash(state []uint64, idx int, hashes *[32]byte) {
	for j := 0; j < 4; j++ {
		binary.LittleEndian.PutUint64(
			(*hashes)[8*j:8*(j+1)],
			state[4*j+idx],
		)
	}
}

func Hash_Keccak_AVX2(data [4][]byte) ([4][32]byte, error) {
	if !keccakf1600.IsEnabledX4() {
		return [4][32]byte{}, errors.New("AVX2 not available")
	}

	var hashes [4][32]byte

	// f1600 acts on 1600 bits arranged as 25 uint64s.  Our fourway f1600
	// acts on four interleaved states; that is a [100]uint64.  (A separate
	// type is used to ensure that the encapsulated [100]uint64 is aligned
	// properly to be used efficiently with vector instructions.)
	var perm keccakf1600.StateX4
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
		populateState(data[0], 0, &state, &start1)
		populateState(data[1], 1, &state, &start2)
		populateState(data[2], 2, &state, &start3)
		populateState(data[3], 3, &state, &start4)
		perm.Permute()
		if start1 == len(data[0]) && !done1 {
			done1 = true
			populateHash(state, 0, &hashes[0])
		}
		if start2 == len(data[1]) && !done2 {
			done2 = true
			populateHash(state, 1, &hashes[1])
		}
		if start3 == len(data[2]) && !done3 {
			done3 = true
			populateHash(state, 2, &hashes[2])
		}
		if start4 == len(data[3]) && !done4 {
			done4 = true
			populateHash(state, 3, &hashes[3])
		}
	}

	return hashes, nil
}

func RlpHashAVX2(x []types.Transaction, h []libcommon.Hash) error {
	var buf [4]bytes.Buffer
	for i := 0; i < 4; i++ {
		x[i].EncodeRLP(&buf[i])
	}
	hashes, err := Hash_Keccak_AVX2([4][]byte{buf[0].Bytes(), buf[1].Bytes(), buf[2].Bytes(), buf[3].Bytes()})
	if err != nil {
		err = fmt.Errorf("RlpHashAVX2() Error: %v", err)
		return err
	}
	for i := 0; i < 4; i++ {
		h[i] = libcommon.BytesToHash(hashes[i][:])
	}
	return nil
}

func populateStateAVX512(data []byte, idx int, state *[]uint64, pstart *int) {
	rate := 136         //absorption occurs on 136 bytes or 1088 bits known as rate
	rate_64 := rate / 8 // 17 * 64 bit lanes = 1088 bits

	start := *pstart
	if start+rate <= len(data) { //more data than rate
		for j := 0; j < rate_64; j++ { //17 rounds
			//Each round needs 64 bits to be read into absorption i.e. 8 bytes
			(*state)[8*j+idx] = binary.LittleEndian.Uint64(data[start+j*8 : start+(j+1)*8])
		}
		*pstart = start + rate
	} else {
		//lesser data than rate
		rem_64 := (len(data) - start) / 8    //num 64 bit lanes of additional data
		rem_bytes := (len(data) - start) % 8 //remainder bytes after above lanes
		for j := 0; j < rem_64; j++ {
			(*state)[8*j+idx] = binary.LittleEndian.Uint64(data[start+j*8 : start+(j+1)*8])
		}
		if rem_bytes > 0 {
			buf := make([]byte, 8)
			copy(buf[:], data[start+rem_64*8:]) //remaining bytes get copied over to the buffer
			(*state)[8*rem_64+idx] = binary.LittleEndian.Uint64(buf) | (uint64(0x1) << (rem_bytes * 8))
		} else {
			(*state)[8*rem_64+idx] = 0x1
		}
		(*state)[(rate_64-1)*8+idx] = 0x80 << 56
		*pstart = len(data)
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

func Hash_Keccak_AVX512(data [8][]byte) ([8][32]byte, error) {
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
		if start1 == len(data[0]) && !done1 {
			done1 = true
			populateHashAVX512(state, 0, &hashes[0])
		}

		if start2 == len(data[1]) && !done2 {
			done2 = true
			populateHashAVX512(state, 1, &hashes[1])
		}

		if start3 == len(data[2]) && !done3 {
			done3 = true
			populateHashAVX512(state, 2, &hashes[2])
		}

		if start4 == len(data[3]) && !done4 {
			done4 = true
			populateHashAVX512(state, 3, &hashes[3])
		}

		if start5 == len(data[4]) && !done5 {
			done5 = true
			populateHashAVX512(state, 4, &hashes[4])
		}

		if start6 == len(data[5]) && !done6 {
			done6 = true
			populateHashAVX512(state, 5, &hashes[5])
		}

		if start7 == len(data[6]) && !done7 {
			done7 = true
			populateHashAVX512(state, 6, &hashes[6])
		}

		if start8 == len(data[7]) && !done8 {
			done8 = true
			populateHashAVX512(state, 7, &hashes[7])
		}
	}

	return hashes, nil
}

func RlpHashAVX512(x []types.Transaction, h []libcommon.Hash) error {
	var buf [8]bytes.Buffer
	for i := 0; i < 8; i++ {
		x[i].EncodeRLP(&buf[i])
	}
	hashes, err := Hash_Keccak_AVX512([8][]byte{buf[0].Bytes(), buf[1].Bytes(), buf[2].Bytes(), buf[3].Bytes(), buf[4].Bytes(), buf[5].Bytes(), buf[6].Bytes(), buf[7].Bytes()})
	if err != nil {
		err = fmt.Errorf("RlpHashAVX512() Error: %v", err)
		return err
	}

	for i := 0; i < 8; i++ {
		h[i] = libcommon.BytesToHash(hashes[i][:])
	}

	return nil
}
