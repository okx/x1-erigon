package apollo

import (
	"crypto/rand"
	"testing"

	"github.com/ledgerwatch/erigon-lib/common"
)

var testAddresses = make([]common.Address, 64)
var isTestAddressesInit = false

func initAddresses() {
	if isTestAddressesInit {
		return
	}
	for i := 0; i < len(testAddresses); i++ {
		r := make([]byte, 20)
		rand.Read(r)
		testAddresses[i] = common.BytesToAddress(r)
	}
	isTestAddressesInit = true
}

func BenchmarkContainsAddressNew(b *testing.B) {
	initAddresses()
	localAddrs := common.NewOrderedListOfAddresses(len(testAddresses))
	for _, item := range testAddresses {
		localAddrs.Add(item)
	}
	// no sort => linear search worst case
	addr := testAddresses[len(testAddresses)-1]
	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		localAddrs.Contains(addr)
	}
}

func TestContainsAddressBinarySearch(t *testing.T) {
	initAddresses()
	localAddrs := common.NewOrderedListOfAddresses(len(testAddresses))
	for _, item := range testAddresses {
		localAddrs.Add(item)
	}
	localAddrs.Sort()

	// should find
	addr := testAddresses[len(testAddresses)-1]
	if !localAddrs.Contains(addr) {
		t.Errorf("Expected to be found")
	}

	// should not find
	b := addr.Bytes()
	b[0] = b[0] + 1
	addr = common.BytesToAddress(b)
	if localAddrs.Contains(addr) {
		t.Errorf("Expected not to be found")
	}
}

func BenchmarkContainsAddressBinarySearch(b *testing.B) {
	initAddresses()
	localAddrs := common.NewOrderedListOfAddresses(len(testAddresses))
	for _, item := range testAddresses {
		localAddrs.Add(item)
	}
	localAddrs.Sort()
	addr := testAddresses[len(testAddresses)-1]
	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		localAddrs.Contains(addr)
	}
}

func BenchmarkContainsAddressOld(b *testing.B) {
	localAddrStr := []string{}
	initAddresses()
	for _, item := range testAddresses {
		localAddrStr = append(localAddrStr, item.String())
	}
	addr := testAddresses[len(testAddresses)-1]
	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		containsAddressOldImpl(localAddrStr, addr)
	}
}
