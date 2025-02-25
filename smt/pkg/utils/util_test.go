package utils

import (
	"crypto/rand"
	"encoding/hex"
	"fmt"
	"math/big"
	"reflect"
	"strconv"
	"strings"
	"testing"
)

func BenchmarkConvertBigIntToHex(b *testing.B) {
	b.ReportAllocs()
	for n := 0; n < b.N; n++ {
		ConvertBigIntToHex(big.NewInt(int64(n)))
	}
}

func BenchmarkHashContractBytecode(b *testing.B) {
	str := strings.Repeat("7e", 500)
	h1 := HashContractBytecodeBigIntV1(str)
	h2 := HashContractBytecodeBigInt(str)
	fmt.Println(h1)
	fmt.Println(h2)
	if h1.Cmp(h2) != 0 {
		panic("hashes do not match")
	}
	b.ResetTimer()
	b.Run("1", func(b *testing.B) {
		for n := 0; n < b.N; n++ {
			HashContractBytecodeBigIntV1(str)
		}
	})
	b.Run("2", func(b *testing.B) {
		for n := 0; n < b.N; n++ {
			HashContractBytecodeBigInt(str)
		}
	})
	b.Run("3", func(b *testing.B) {
		for n := 0; n < b.N; n++ {
			HashContractBytecode(str)
		}
	})
}

// for input strings of even size
func runTestHashContractBytecodeConsistencyEven(size int, t *testing.T) {
	data := make([]byte, size)
	rand.Read(data)
	strData := hex.EncodeToString(data)
	if !strings.HasPrefix(strData, "0x") {
		strData = "0x" + strData
	}
	h1 := HashContractBytecodeBigIntV1(strings.ToLower(strData))
	h2 := HashContractBytecodeBigInt(strData)
	if h1.Cmp(h2) != 0 {
		t.Errorf("(lower case) Expected %v, but got %v", h1, h2)
	}
	h3 := HashContractBytecodeBigInt(strings.ToUpper(strData[2:]))
	if h1.Cmp(h3) != 0 {
		t.Errorf("(upper case) Expected %v, but got %v", h1, h3)
	}
}

// for input strings of odd size
func runTestHashContractBytecodeConsistencyOdd(size int, t *testing.T) {
	data := make([]byte, size)
	rand.Read(data)
	strData := hex.EncodeToString(data)
	strData = strData[:len(strData)-1]
	h1 := HashContractBytecodeBigIntV1(strings.ToLower(strData))
	h2 := HashContractBytecodeBigInt(strData)
	if h1.Cmp(h2) != 0 {
		t.Errorf("(lower case) Expected %v, but got %v", h1, h2)
	}
	h3 := HashContractBytecodeBigInt(strings.ToUpper(strData))
	if h1.Cmp(h3) != 0 {
		t.Errorf("(upper case) Expected %v, but got %v", h1, h3)
	}
}

func TestHashContractBytecodeConsistency(t *testing.T) {
	runTestHashContractBytecodeConsistencyEven(1234, t)
	runTestHashContractBytecodeConsistencyEven(37, t)
	runTestHashContractBytecodeConsistencyEven(111, t) // edge case, the actual size is divisible by 56*2
	runTestHashContractBytecodeConsistencyOdd(37, t)
	runTestHashContractBytecodeConsistencyOdd(1, t)
	runTestHashContractBytecodeConsistencyOdd(111, t) // edge case, the actual size is divisible by 56*2
}

func TestConvertBigIntToHex(t *testing.T) {
	testCases := []struct {
		name     string
		input    *big.Int
		expected string
	}{
		{
			name:     "Case 1",
			input:    big.NewInt(16),
			expected: "0x10",
		},
		{
			name:     "Case 2",
			input:    big.NewInt(255),
			expected: "0xff",
		},
		{
			name:     "Case 3",
			input:    big.NewInt(4096),
			expected: "0x1000",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := ConvertBigIntToHex(tc.input)
			if result != tc.expected {
				t.Errorf("Expected %v, but got %v", tc.expected, result)
			}
		})
	}
}

func TestConvertHexToBigInt(t *testing.T) {
	reallyBig, _ := new(big.Int).SetString("66192783235284117971885209808488305726649121900484207371085803724835092316526", 10)

	testCases := []struct {
		name     string
		hexInput string
		expected *big.Int
	}{
		{
			name:     "basic case",
			hexInput: "0x1A",
			expected: big.NewInt(26),
		},
		{
			name:     "without prefix",
			hexInput: "1A",
			expected: big.NewInt(26),
		},
		{
			name:     "zero case",
			hexInput: "0x0",
			expected: big.NewInt(0),
		},
		{
			name:     "large number",
			hexInput: "0x1B2E8BAC",
			expected: big.NewInt(456035244),
		},
		{
			name:     "really big number",
			hexInput: "0x9257c9a31308a7cb046aba1a95679dd7e3ad695b6900e84a6470b401b1ea416e",
			expected: reallyBig,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			result := ConvertHexToBigInt(tc.hexInput)
			if result.Cmp(tc.expected) != 0 {
				t.Errorf("ConvertHexToBigInt(%q) = %v; want %v", tc.hexInput, result, tc.expected)
			}
		})
	}
}

func TestScalarToArray8(t *testing.T) {
	scalar := big.NewInt(0x1234567890ABCDEF)

	expected := []*big.Int{
		big.NewInt(0x90ABCDEF),
		big.NewInt(0x12345678),
		big.NewInt(0),
		big.NewInt(0),
		big.NewInt(0),
		big.NewInt(0),
		big.NewInt(0),
		big.NewInt(0),
	}

	result := ScalarToArray8(scalar)

	for i := range result {
		if result[i] != expected[i].Uint64() {
			t.Errorf("ScalarToArray = %v; want %v", result, expected)
			break
		}
	}
}

func BenchmarkScalarToArrayBig(b *testing.B) {
	scalar := big.NewInt(0x1234567890ABCDEF)
	for i := 0; i < b.N; i++ {
		ScalarToArray12(scalar)
	}
}

func TestArrayToScalar32Bit(t *testing.T) {
	scalar := big.NewInt(0x1234567890ABCDEF)

	result := ArrayToScalar32Bit(ScalarToArray12(scalar))

	if !reflect.DeepEqual(result, scalar) {
		t.Errorf("ScalarToArray = %v; want %v", result, scalar)
	}
}

func TestArrayToScalar(t *testing.T) {
	array := []uint64{2, 3}
	want := big.NewInt(0)
	want = want.Lsh(big.NewInt(3), 64)
	want = want.Add(want, big.NewInt(2))

	got := ArrayToScalar64Bit(array)

	if got.Cmp(want) != 0 {
		t.Errorf("ArrayToScalar(%v) = %v; want %v", array, got, want)
	}
}

func TestArrayToScalarBig(t *testing.T) {
	array := []uint64{
		0x1122334455667788,
		0x99aabbccddeeff00,
		0x1122334455667788,
	}

	expected, _ := new(big.Int).SetString("112233445566778899aabbccddeeff001122334455667788", 16)

	result := ArrayToScalar64Bit(array)

	if !reflect.DeepEqual(result, expected) {
		t.Errorf("ArrayToScalarBig(%v) = %v, want %v", array, result, expected)
	}
}

func TestRemoveKeyBits(t *testing.T) {
	testCases := map[string]struct {
		k      NodeKey
		nBits  int
		expect NodeKey
	}{
		"Test 1": {
			k:      NodeKey{14833827758303204589, 15154033943678652181, 5489675274157668397, 7250342125880245156},
			nBits:  0,
			expect: NodeKey{14833827758303204589, 15154033943678652181, 5489675274157668397, 7250342125880245156},
		},
	}

	for name, tc := range testCases {
		t.Run(name, func(t *testing.T) {
			got := RemoveKeyBits(tc.k, tc.nBits)

			if !reflect.DeepEqual(got, tc.expect) {
				t.Errorf("RemoveKeyBits(%v, %v) = %v; want %v", tc.k, tc.nBits, got, tc.expect)
			}
		})
	}
}

func TestNodeKey_GetPath(t *testing.T) {
	testCases := []struct {
		name     string
		key      NodeKey
		expected string
	}{
		{
			name:     "Test case 1",
			key:      NodeKey{0, 0, 0, 15},
			expected: "0001000100010001" + strings.Repeat("0", 248-8),
		},
		{
			name:     "Test case 2",
			key:      NodeKey{1, 0, 0, 1},
			expected: "10010000" + strings.Repeat("0", 256-8),
		},
		{
			name:     "Test case 3",
			key:      NodeKey{14833827758303204589, 15154033943678652181, 5489675274157668397, 7250342125880245156},
			expected: "1110000011111010010010111000100101010101110001111011001110011110111000001101111010001111101010000101010001000110100000011001101101110011010100010111000110001111110110111010001011100111110101000110001111111111100100101100100110000100101110100100000111111100",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			r := tc.key.GetPath()

			binaryArr := parseBinaryString(tc.expected)

			areEqual := compareIntArray(r, binaryArr)

			if len(binaryArr) != len(r) {
				t.Errorf("GetPath(%v) - lengths don't match = %v; want %v", tc.key, len(r), len(binaryArr))
			}

			if !areEqual {
				t.Errorf("GetPath(%v) = %v; want %v", tc.key, r, binaryArr)
			}
		})
	}
}

func TestNodeKeyIsZero(t *testing.T) {
	cases := []struct {
		name string
		key  NodeKey
		want bool
	}{
		{
			name: "Zero Key",
			key:  NodeKey{0, 0, 0, 0},
			want: true,
		},
		{
			name: "Non-Zero Key",
			key:  NodeKey{1, 0, 0, 0},
			want: false,
		},
		// add more cases here as needed
	}

	for _, tt := range cases {
		t.Run(tt.name, func(t *testing.T) {
			if got := tt.key.IsZero(); got != tt.want {
				t.Errorf("IsZero() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestNodeValueIsZero(t *testing.T) {
	cases := []struct {
		name  string
		value NodeValue12
		want  bool
	}{
		{
			name: "Zero Key",
			value: NodeValue12{
				0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
			},
			want: true,
		},
		{
			name: "Non-Zero Key",
			value: NodeValue12{
				1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
			},
			want: false,
		},
	}

	for _, tt := range cases {
		t.Run(tt.name, func(t *testing.T) {
			if got := tt.value.IsZero(); got != tt.want {
				t.Errorf("IsZero() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestNodeValue8SetHalfValue(t *testing.T) {
	cases := []struct {
		name string
		part int
	}{
		{
			name: "first part",
			part: 0,
		},
		{
			name: "second part",
			part: 1,
		},
		{
			name: "both parts",
			part: 2,
		},
	}

	for _, tt := range cases {
		t.Run(tt.name, func(t *testing.T) {
			var a NodeValue8
			v := [4]uint64{1, 0, 0, 0}
			if tt.part == 2 {
				a.SetHalfValue(v, 0)
				a.SetHalfValue(v, 1)
			} else {
				a.SetHalfValue(v, tt.part)
			}

			if tt.part == 0 && a[0] != v[0] {
				t.Errorf("first part not set to 1")
			} else if tt.part == 1 && a[4] != v[0] {
				t.Errorf("second part not set to 1")
			} else if tt.part == 2 && a[0] != v[0] && a[4] != v[0] {
				t.Errorf("first and second part not set to 1")
			}
		})
	}
}

func TestIsFinalNode(t *testing.T) {
	cases := []struct {
		name  string
		value NodeValue12
		want  bool
	}{
		{
			name:  "Final Node",
			value: NodeValue12{0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0},
			want:  true,
		},
		{
			name:  "Not a Final Node",
			value: NodeValue12{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
			want:  false,
		},
		{
			name:  "Nil value at 9th element",
			value: NodeValue12{0, 0, 0, 0, 0, 0, 0, 0},
			want:  false,
		},
	}

	for _, tt := range cases {
		t.Run(tt.name, func(t *testing.T) {
			if got := tt.value.IsFinalNode(); got != tt.want {
				t.Errorf("IsFinalNode() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestNodeKeyFromBigIntArray(t *testing.T) {
	var tests = []struct {
		input    []uint64
		expected NodeKey
		err      error
	}{
		{
			input:    []uint64{1, 2, 3, 4},
			expected: NodeKey{1, 2, 3, 4},
			err:      nil,
		},
		{
			input:    []uint64{10, 20, 30},
			expected: NodeKey{10, 20, 30, 0},
			err:      fmt.Errorf("invalid array length"),
		},
	}

	for _, tt := range tests {
		nk := NodeKeyFromArray(tt.input)
		if nk != tt.expected {
			t.Errorf("FromBigIntArray(%v) = %v, want %v", tt.input, nk, tt.expected)
		}
	}
}

func TestNodeValueFromBigIntArray(t *testing.T) {
	var tests = []struct {
		input    []uint64
		expected *NodeValue12
		err      error
	}{
		{
			input:    []uint64{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12},
			expected: &NodeValue12{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12},
			err:      nil,
		},
		{
			input:    []uint64{10, 20, 30},
			expected: &NodeValue12{},
			err:      fmt.Errorf("invalid array length"),
		},
	}

	for _, tt := range tests {
		nv, err := NodeValue12FromBigIntArray(tt.input)
		if (err != nil && tt.err != nil && err.Error() != tt.err.Error()) ||
			(err != nil && tt.err == nil) ||
			(err == nil && tt.err != nil) {
			t.Errorf("FromBigIntArray(%v) returned error %v, want %v", tt.input, err, tt.err)
		}
		if !reflect.DeepEqual(nv, tt.expected) {
			t.Errorf("FromBigIntArray(%v) = %v, want %v", tt.input, nv, tt.expected)
		}
	}
}

func TestJoinKey(t *testing.T) {
	tt := map[string]struct {
		usedBits     []int
		remainingKey NodeKey
		want         NodeKey
	}{
		"Test 1": {
			usedBits:     []int{1, 0, 0, 0, 0},
			remainingKey: [4]uint64{0, 0, 0, 0},
			want:         [4]uint64{1, 0, 0, 0},
		},
		"Test 2": {
			usedBits:     []int{0, 1, 0, 0, 0},
			remainingKey: [4]uint64{0, 0, 0, 0},
			want:         [4]uint64{0, 1, 0, 0},
		},
		"Test 3": {
			usedBits:     []int{1, 1, 0, 0, 0},
			remainingKey: [4]uint64{0, 0, 0, 0},
			want:         [4]uint64{1, 1, 0, 0},
		},
		"Test 4": {
			usedBits:     []int{1},
			remainingKey: [4]uint64{0, 0, 0, 1},
			want:         [4]uint64{1, 0, 0, 1},
		},
	}

	for n, tc := range tt {
		t.Run(n, func(t *testing.T) {
			got := JoinKey(tc.usedBits, tc.remainingKey)
			for i := 0; i < 4; i++ {
				if got[i] != tc.want[i] {
					t.Errorf("got %v, want %v", got, tc.want)
				}
			}
		})
	}
}

func Test_StringToH4(t *testing.T) {
	tests := map[string]struct {
		input   string
		want    [4]uint64
		wantErr bool
	}{
		"Test Case 1": {
			input:   "0xc71603f33a1144ca7953db0ab48808f4c4055e3364a246c33c18a9786cb0b359",
			want:    [4]uint64{4330397376401421145, 14124799381142128323, 8742572140681234676, 14345658006221440202},
			wantErr: false,
		},
	}

	for name, tc := range tests {
		t.Run(name, func(t *testing.T) {
			got, err := StringToH4(tc.input)
			if (err != nil) != tc.wantErr {
				t.Errorf("StringToH4() error = %v, wantErr %v", err, tc.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tc.want) {
				t.Errorf("StringToH4() = %v, want %v", got, tc.want)
			}
		})
	}
}

func TestScalarToNodeKey(t *testing.T) {
	tc2bi := big.Int{}
	tc2bi.SetString("69905", 10)

	tc4bi := big.Int{}
	tc4bi.SetString("56714103185361745016746792718676985000067748055642999311525839752090945477479", 10)

	testCases := map[string]struct {
		input    *big.Int
		expected NodeKey
	}{
		"test case 1": {big.NewInt(7), NodeKey{1, 1, 1, 0}},
		"test case 2": {&tc2bi, NodeKey{31, 0, 0, 0}},
		"test case 3": {big.NewInt(1), NodeKey{1, 0, 0, 0}},
		"test case 4": {&tc4bi, NodeKey{15508201873038097485, 13226964191399612151, 16289586894263066011, 5039894867879804772}},
	}

	for name, tc := range testCases {
		t.Run(name, func(t *testing.T) {
			output := ScalarToNodeKey(tc.input)
			if output != tc.expected { // This assumes NodeKey type can be directly compared
				t.Errorf("For input: %v, expected: %v, but got: %v", tc.input, tc.expected, output)
			}
		})
	}
}

func TestScalarToNodeValue(t *testing.T) {
	// Define the array of original values
	originalValues := [12]*big.Int{
		big.NewInt(1),
		big.NewInt(2),
		big.NewInt(3),
		big.NewInt(4),
		big.NewInt(5),
		big.NewInt(6),
		big.NewInt(7),
		big.NewInt(8),
		big.NewInt(9),
		big.NewInt(10),
		big.NewInt(11),
		big.NewInt(12),
	}

	// Create a big scalar that is the concatenation of the 12 original values
	scalar := new(big.Int)
	for i := 11; i >= 0; i-- {
		scalar.Lsh(scalar, 64)
		scalar.Or(scalar, originalValues[i])
	}

	// Call the function to test
	result := ScalarToNodeValue(scalar)

	// Check that each element of the result matches the corresponding original value
	for i := range originalValues {
		if result[i] != originalValues[i].Uint64() {
			t.Errorf("Element %d: expected %s, got %d", i, originalValues[i], result[i])
		}
	}
}

func TestScalarToNodeValue8(t *testing.T) {
	// Define the array of original values
	originalValues := [8]*big.Int{
		big.NewInt(1),
		big.NewInt(2),
		big.NewInt(3),
		big.NewInt(4),
		big.NewInt(5),
		big.NewInt(6),
		big.NewInt(7),
		big.NewInt(8),
	}

	// Create a big scalar that is the concatenation of the 12 original values
	scalar := new(big.Int)
	for i := 7; i >= 0; i-- {
		scalar.Lsh(scalar, 64)
		scalar.Or(scalar, originalValues[i])
	}

	// Call the function to test
	result := ScalarToNodeValue8(scalar)

	// Check that each element of the result matches the corresponding original value
	for i := range originalValues {
		if result[i] != originalValues[i].Uint64() {
			t.Errorf("Element %d: expected %s, got %d", i, originalValues[i], result[i])
		}
	}
}

func TestValue8FromBigIntArray(t *testing.T) {
	tests := []struct {
		input  []uint64
		output NodeValue8
	}{
		{
			input:  []uint64{1, 2, 3},
			output: NodeValue8{1, 2, 3},
		},
		{
			input:  []uint64{1, 2, 3, 4, 5, 6, 7, 8},
			output: NodeValue8{1, 2, 3, 4, 5, 6, 7, 8},
		},
	}

	for _, test := range tests {
		result := Value8FromBigIntArray(test.input)
		for i := range result {
			if result[i] != test.output[i] {
				t.Errorf("For input %v, expected %v but got %v", test.input, test.output, result)
			}
		}
	}
}

// parseBinaryString converts a string of binary digits to an array of ints
func parseBinaryString(s string) []int {
	binaryArr := make([]int, len(s))
	for i, ch := range s {
		num, _ := strconv.Atoi(string(ch))
		binaryArr[i] = num
	}
	return binaryArr
}

// compareIntArray compares two arrays of ints and returns true if they are equal
func compareIntArray(arr1, arr2 []int) bool {
	if len(arr1) != len(arr2) {
		return false
	}
	for i := 0; i < len(arr1); i++ {
		if arr1[i] != arr2[i] {
			return false
		}
	}
	return true
}

func TestSortNodeKeysBitwiseAsc(t *testing.T) {
	tests := []struct {
		input  []NodeKey
		output []NodeKey
	}{
		{
			input:  []NodeKey{{0, 1, 0, 0}, {1, 0, 0, 0}, {0, 0, 1, 0}},
			output: []NodeKey{{0, 0, 1, 0}, {0, 1, 0, 0}, {1, 0, 0, 0}},
		},
		{
			input:  []NodeKey{{1, 0, 0, 0}, {0, 0, 1, 0}, {0, 1, 0, 0}, {0, 0, 0, 1}, {0, 1, 0, 0}},
			output: []NodeKey{{0, 0, 0, 1}, {0, 0, 1, 0}, {0, 1, 0, 0}, {0, 1, 0, 0}, {1, 0, 0, 0}},
		},
		{
			input:  []NodeKey{{345, 13626, 23, 1}, {124, 54, 3452, 547547}, {121, 434, 34436, 1}, {25, 346, 235, 12456}, {6334, 346346, 1, 0}},
			output: []NodeKey{{124, 54, 3452, 547547}, {6334, 346346, 1, 0}, {121, 434, 34436, 1}, {25, 346, 235, 12456}, {345, 13626, 23, 1}},
		},
	}

	for _, test := range tests {
		SortNodeKeysBitwiseAsc(test.input)
		for i := range test.input {
			if test.input[i] != test.output[i] {
				fmt.Println(test.input[i].GetPath())
				t.Errorf("expected %v but got %v", test.output, test.input)
			}
		}
	}
}

func TestNodeKeyFromPath(t *testing.T) {
	tests := []struct {
		input  int
		output NodeKey
	}{
		{
			input: 0,
		},
		{
			input: 1,
		},
		{
			input: 124124,
		},
		{
			input: 124124124124124,
		},
	}

	for _, test := range tests {
		input := ScalarToNodeKey(big.NewInt(int64(test.input)))
		result, err := NodeKeyFromPath(input.GetPath())

		if err != nil {
			t.Fatal(err)
		}

		if result != input {
			t.Errorf("parse doesn't match, expected: %v, got: %v", input, result)
		}
	}
}
