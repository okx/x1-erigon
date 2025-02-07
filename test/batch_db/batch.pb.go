// Code generated by protoc-gen-go. DO NOT EDIT.
// versions:
// 	protoc-gen-go v1.36.5
// 	protoc        v5.29.3
// source: batch.proto

package main

import (
	protoreflect "google.golang.org/protobuf/reflect/protoreflect"
	protoimpl "google.golang.org/protobuf/runtime/protoimpl"
	reflect "reflect"
	sync "sync"
	unsafe "unsafe"
)

const (
	// Verify that this generated code is sufficiently up-to-date.
	_ = protoimpl.EnforceVersion(20 - protoimpl.MinVersion)
	// Verify that runtime/protoimpl is sufficiently up-to-date.
	_ = protoimpl.EnforceVersion(protoimpl.MaxVersion - 20)
)

type BatchData struct {
	state         protoimpl.MessageState   `protogen:"open.v1"`
	Blocks        []*BatchData_FullL2Block `protobuf:"bytes,1,rep,name=blocks,proto3" json:"blocks,omitempty"`
	unknownFields protoimpl.UnknownFields
	sizeCache     protoimpl.SizeCache
}

func (x *BatchData) Reset() {
	*x = BatchData{}
	mi := &file_batch_proto_msgTypes[0]
	ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
	ms.StoreMessageInfo(mi)
}

func (x *BatchData) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*BatchData) ProtoMessage() {}

func (x *BatchData) ProtoReflect() protoreflect.Message {
	mi := &file_batch_proto_msgTypes[0]
	if x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use BatchData.ProtoReflect.Descriptor instead.
func (*BatchData) Descriptor() ([]byte, []int) {
	return file_batch_proto_rawDescGZIP(), []int{0}
}

func (x *BatchData) GetBlocks() []*BatchData_FullL2Block {
	if x != nil {
		return x.Blocks
	}
	return nil
}

type BatchData_FullL2Block struct {
	state           protoimpl.MessageState `protogen:"open.v1"`
	BatchNumber     uint64                 `protobuf:"varint,1,opt,name=batch_number,json=batchNumber,proto3" json:"batch_number,omitempty"`
	L2BlockNumber   uint64                 `protobuf:"varint,2,opt,name=l2_block_number,json=l2BlockNumber,proto3" json:"l2_block_number,omitempty"`
	Timestamp       int64                  `protobuf:"varint,3,opt,name=timestamp,proto3" json:"timestamp,omitempty"`
	DeltaTimestamp  uint32                 `protobuf:"varint,4,opt,name=delta_timestamp,json=deltaTimestamp,proto3" json:"delta_timestamp,omitempty"`
	L1InfoTreeIndex uint32                 `protobuf:"varint,5,opt,name=l1_info_tree_index,json=l1InfoTreeIndex,proto3" json:"l1_info_tree_index,omitempty"`
	GlobalExitRoot  []byte                 `protobuf:"bytes,6,opt,name=global_exit_root,json=globalExitRoot,proto3" json:"global_exit_root,omitempty"`
	Coinbase        []byte                 `protobuf:"bytes,7,opt,name=coinbase,proto3" json:"coinbase,omitempty"`
	ForkId          uint64                 `protobuf:"varint,8,opt,name=fork_id,json=forkId,proto3" json:"fork_id,omitempty"`
	L1BlockHash     []byte                 `protobuf:"bytes,9,opt,name=l1_block_hash,json=l1BlockHash,proto3" json:"l1_block_hash,omitempty"`
	L2BlockHash     []byte                 `protobuf:"bytes,10,opt,name=l2_block_hash,json=l2BlockHash,proto3" json:"l2_block_hash,omitempty"`
	ParentHash      []byte                 `protobuf:"bytes,11,opt,name=parent_hash,json=parentHash,proto3" json:"parent_hash,omitempty"`
	StateRoot       []byte                 `protobuf:"bytes,12,opt,name=state_root,json=stateRoot,proto3" json:"state_root,omitempty"`
	BlockGasLimit   uint64                 `protobuf:"varint,13,opt,name=block_gas_limit,json=blockGasLimit,proto3" json:"block_gas_limit,omitempty"`
	BlockInfoRoot   []byte                 `protobuf:"bytes,14,opt,name=block_info_root,json=blockInfoRoot,proto3" json:"block_info_root,omitempty"`
	unknownFields   protoimpl.UnknownFields
	sizeCache       protoimpl.SizeCache
}

func (x *BatchData_FullL2Block) Reset() {
	*x = BatchData_FullL2Block{}
	mi := &file_batch_proto_msgTypes[1]
	ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
	ms.StoreMessageInfo(mi)
}

func (x *BatchData_FullL2Block) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*BatchData_FullL2Block) ProtoMessage() {}

func (x *BatchData_FullL2Block) ProtoReflect() protoreflect.Message {
	mi := &file_batch_proto_msgTypes[1]
	if x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use BatchData_FullL2Block.ProtoReflect.Descriptor instead.
func (*BatchData_FullL2Block) Descriptor() ([]byte, []int) {
	return file_batch_proto_rawDescGZIP(), []int{0, 0}
}

func (x *BatchData_FullL2Block) GetBatchNumber() uint64 {
	if x != nil {
		return x.BatchNumber
	}
	return 0
}

func (x *BatchData_FullL2Block) GetL2BlockNumber() uint64 {
	if x != nil {
		return x.L2BlockNumber
	}
	return 0
}

func (x *BatchData_FullL2Block) GetTimestamp() int64 {
	if x != nil {
		return x.Timestamp
	}
	return 0
}

func (x *BatchData_FullL2Block) GetDeltaTimestamp() uint32 {
	if x != nil {
		return x.DeltaTimestamp
	}
	return 0
}

func (x *BatchData_FullL2Block) GetL1InfoTreeIndex() uint32 {
	if x != nil {
		return x.L1InfoTreeIndex
	}
	return 0
}

func (x *BatchData_FullL2Block) GetGlobalExitRoot() []byte {
	if x != nil {
		return x.GlobalExitRoot
	}
	return nil
}

func (x *BatchData_FullL2Block) GetCoinbase() []byte {
	if x != nil {
		return x.Coinbase
	}
	return nil
}

func (x *BatchData_FullL2Block) GetForkId() uint64 {
	if x != nil {
		return x.ForkId
	}
	return 0
}

func (x *BatchData_FullL2Block) GetL1BlockHash() []byte {
	if x != nil {
		return x.L1BlockHash
	}
	return nil
}

func (x *BatchData_FullL2Block) GetL2BlockHash() []byte {
	if x != nil {
		return x.L2BlockHash
	}
	return nil
}

func (x *BatchData_FullL2Block) GetParentHash() []byte {
	if x != nil {
		return x.ParentHash
	}
	return nil
}

func (x *BatchData_FullL2Block) GetStateRoot() []byte {
	if x != nil {
		return x.StateRoot
	}
	return nil
}

func (x *BatchData_FullL2Block) GetBlockGasLimit() uint64 {
	if x != nil {
		return x.BlockGasLimit
	}
	return 0
}

func (x *BatchData_FullL2Block) GetBlockInfoRoot() []byte {
	if x != nil {
		return x.BlockInfoRoot
	}
	return nil
}

var File_batch_proto protoreflect.FileDescriptor

var file_batch_proto_rawDesc = string([]byte{
	0x0a, 0x0b, 0x62, 0x61, 0x74, 0x63, 0x68, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x08, 0x62,
	0x61, 0x74, 0x63, 0x68, 0x5f, 0x64, 0x62, 0x22, 0xca, 0x04, 0x0a, 0x09, 0x42, 0x61, 0x74, 0x63,
	0x68, 0x44, 0x61, 0x74, 0x61, 0x12, 0x37, 0x0a, 0x06, 0x62, 0x6c, 0x6f, 0x63, 0x6b, 0x73, 0x18,
	0x01, 0x20, 0x03, 0x28, 0x0b, 0x32, 0x1f, 0x2e, 0x62, 0x61, 0x74, 0x63, 0x68, 0x5f, 0x64, 0x62,
	0x2e, 0x42, 0x61, 0x74, 0x63, 0x68, 0x44, 0x61, 0x74, 0x61, 0x2e, 0x46, 0x75, 0x6c, 0x6c, 0x4c,
	0x32, 0x42, 0x6c, 0x6f, 0x63, 0x6b, 0x52, 0x06, 0x62, 0x6c, 0x6f, 0x63, 0x6b, 0x73, 0x1a, 0x83,
	0x04, 0x0a, 0x0b, 0x46, 0x75, 0x6c, 0x6c, 0x4c, 0x32, 0x42, 0x6c, 0x6f, 0x63, 0x6b, 0x12, 0x21,
	0x0a, 0x0c, 0x62, 0x61, 0x74, 0x63, 0x68, 0x5f, 0x6e, 0x75, 0x6d, 0x62, 0x65, 0x72, 0x18, 0x01,
	0x20, 0x01, 0x28, 0x04, 0x52, 0x0b, 0x62, 0x61, 0x74, 0x63, 0x68, 0x4e, 0x75, 0x6d, 0x62, 0x65,
	0x72, 0x12, 0x26, 0x0a, 0x0f, 0x6c, 0x32, 0x5f, 0x62, 0x6c, 0x6f, 0x63, 0x6b, 0x5f, 0x6e, 0x75,
	0x6d, 0x62, 0x65, 0x72, 0x18, 0x02, 0x20, 0x01, 0x28, 0x04, 0x52, 0x0d, 0x6c, 0x32, 0x42, 0x6c,
	0x6f, 0x63, 0x6b, 0x4e, 0x75, 0x6d, 0x62, 0x65, 0x72, 0x12, 0x1c, 0x0a, 0x09, 0x74, 0x69, 0x6d,
	0x65, 0x73, 0x74, 0x61, 0x6d, 0x70, 0x18, 0x03, 0x20, 0x01, 0x28, 0x03, 0x52, 0x09, 0x74, 0x69,
	0x6d, 0x65, 0x73, 0x74, 0x61, 0x6d, 0x70, 0x12, 0x27, 0x0a, 0x0f, 0x64, 0x65, 0x6c, 0x74, 0x61,
	0x5f, 0x74, 0x69, 0x6d, 0x65, 0x73, 0x74, 0x61, 0x6d, 0x70, 0x18, 0x04, 0x20, 0x01, 0x28, 0x0d,
	0x52, 0x0e, 0x64, 0x65, 0x6c, 0x74, 0x61, 0x54, 0x69, 0x6d, 0x65, 0x73, 0x74, 0x61, 0x6d, 0x70,
	0x12, 0x2b, 0x0a, 0x12, 0x6c, 0x31, 0x5f, 0x69, 0x6e, 0x66, 0x6f, 0x5f, 0x74, 0x72, 0x65, 0x65,
	0x5f, 0x69, 0x6e, 0x64, 0x65, 0x78, 0x18, 0x05, 0x20, 0x01, 0x28, 0x0d, 0x52, 0x0f, 0x6c, 0x31,
	0x49, 0x6e, 0x66, 0x6f, 0x54, 0x72, 0x65, 0x65, 0x49, 0x6e, 0x64, 0x65, 0x78, 0x12, 0x28, 0x0a,
	0x10, 0x67, 0x6c, 0x6f, 0x62, 0x61, 0x6c, 0x5f, 0x65, 0x78, 0x69, 0x74, 0x5f, 0x72, 0x6f, 0x6f,
	0x74, 0x18, 0x06, 0x20, 0x01, 0x28, 0x0c, 0x52, 0x0e, 0x67, 0x6c, 0x6f, 0x62, 0x61, 0x6c, 0x45,
	0x78, 0x69, 0x74, 0x52, 0x6f, 0x6f, 0x74, 0x12, 0x1a, 0x0a, 0x08, 0x63, 0x6f, 0x69, 0x6e, 0x62,
	0x61, 0x73, 0x65, 0x18, 0x07, 0x20, 0x01, 0x28, 0x0c, 0x52, 0x08, 0x63, 0x6f, 0x69, 0x6e, 0x62,
	0x61, 0x73, 0x65, 0x12, 0x17, 0x0a, 0x07, 0x66, 0x6f, 0x72, 0x6b, 0x5f, 0x69, 0x64, 0x18, 0x08,
	0x20, 0x01, 0x28, 0x04, 0x52, 0x06, 0x66, 0x6f, 0x72, 0x6b, 0x49, 0x64, 0x12, 0x22, 0x0a, 0x0d,
	0x6c, 0x31, 0x5f, 0x62, 0x6c, 0x6f, 0x63, 0x6b, 0x5f, 0x68, 0x61, 0x73, 0x68, 0x18, 0x09, 0x20,
	0x01, 0x28, 0x0c, 0x52, 0x0b, 0x6c, 0x31, 0x42, 0x6c, 0x6f, 0x63, 0x6b, 0x48, 0x61, 0x73, 0x68,
	0x12, 0x22, 0x0a, 0x0d, 0x6c, 0x32, 0x5f, 0x62, 0x6c, 0x6f, 0x63, 0x6b, 0x5f, 0x68, 0x61, 0x73,
	0x68, 0x18, 0x0a, 0x20, 0x01, 0x28, 0x0c, 0x52, 0x0b, 0x6c, 0x32, 0x42, 0x6c, 0x6f, 0x63, 0x6b,
	0x48, 0x61, 0x73, 0x68, 0x12, 0x1f, 0x0a, 0x0b, 0x70, 0x61, 0x72, 0x65, 0x6e, 0x74, 0x5f, 0x68,
	0x61, 0x73, 0x68, 0x18, 0x0b, 0x20, 0x01, 0x28, 0x0c, 0x52, 0x0a, 0x70, 0x61, 0x72, 0x65, 0x6e,
	0x74, 0x48, 0x61, 0x73, 0x68, 0x12, 0x1d, 0x0a, 0x0a, 0x73, 0x74, 0x61, 0x74, 0x65, 0x5f, 0x72,
	0x6f, 0x6f, 0x74, 0x18, 0x0c, 0x20, 0x01, 0x28, 0x0c, 0x52, 0x09, 0x73, 0x74, 0x61, 0x74, 0x65,
	0x52, 0x6f, 0x6f, 0x74, 0x12, 0x26, 0x0a, 0x0f, 0x62, 0x6c, 0x6f, 0x63, 0x6b, 0x5f, 0x67, 0x61,
	0x73, 0x5f, 0x6c, 0x69, 0x6d, 0x69, 0x74, 0x18, 0x0d, 0x20, 0x01, 0x28, 0x04, 0x52, 0x0d, 0x62,
	0x6c, 0x6f, 0x63, 0x6b, 0x47, 0x61, 0x73, 0x4c, 0x69, 0x6d, 0x69, 0x74, 0x12, 0x26, 0x0a, 0x0f,
	0x62, 0x6c, 0x6f, 0x63, 0x6b, 0x5f, 0x69, 0x6e, 0x66, 0x6f, 0x5f, 0x72, 0x6f, 0x6f, 0x74, 0x18,
	0x0e, 0x20, 0x01, 0x28, 0x0c, 0x52, 0x0d, 0x62, 0x6c, 0x6f, 0x63, 0x6b, 0x49, 0x6e, 0x66, 0x6f,
	0x52, 0x6f, 0x6f, 0x74, 0x42, 0x0d, 0x5a, 0x0b, 0x2e, 0x2f, 0x3b, 0x62, 0x61, 0x74, 0x63, 0x68,
	0x5f, 0x64, 0x62, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
})

var (
	file_batch_proto_rawDescOnce sync.Once
	file_batch_proto_rawDescData []byte
)

func file_batch_proto_rawDescGZIP() []byte {
	file_batch_proto_rawDescOnce.Do(func() {
		file_batch_proto_rawDescData = protoimpl.X.CompressGZIP(unsafe.Slice(unsafe.StringData(file_batch_proto_rawDesc), len(file_batch_proto_rawDesc)))
	})
	return file_batch_proto_rawDescData
}

var file_batch_proto_msgTypes = make([]protoimpl.MessageInfo, 2)
var file_batch_proto_goTypes = []any{
	(*BatchData)(nil),             // 0: batch_db.BatchData
	(*BatchData_FullL2Block)(nil), // 1: batch_db.BatchData.FullL2Block
}
var file_batch_proto_depIdxs = []int32{
	1, // 0: batch_db.BatchData.blocks:type_name -> batch_db.BatchData.FullL2Block
	1, // [1:1] is the sub-list for method output_type
	1, // [1:1] is the sub-list for method input_type
	1, // [1:1] is the sub-list for extension type_name
	1, // [1:1] is the sub-list for extension extendee
	0, // [0:1] is the sub-list for field type_name
}

func init() { file_batch_proto_init() }
func file_batch_proto_init() {
	if File_batch_proto != nil {
		return
	}
	type x struct{}
	out := protoimpl.TypeBuilder{
		File: protoimpl.DescBuilder{
			GoPackagePath: reflect.TypeOf(x{}).PkgPath(),
			RawDescriptor: unsafe.Slice(unsafe.StringData(file_batch_proto_rawDesc), len(file_batch_proto_rawDesc)),
			NumEnums:      0,
			NumMessages:   2,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_batch_proto_goTypes,
		DependencyIndexes: file_batch_proto_depIdxs,
		MessageInfos:      file_batch_proto_msgTypes,
	}.Build()
	File_batch_proto = out.File
	file_batch_proto_goTypes = nil
	file_batch_proto_depIdxs = nil
}
