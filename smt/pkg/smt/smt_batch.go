package smt

import (
	"context"
	"fmt"
	"github.com/ledgerwatch/log/v3"
	"runtime"
	"sync"
	"time"

	"github.com/dgravesa/go-parallel/parallel"
	"github.com/ledgerwatch/erigon/smt/pkg/utils"
	"github.com/ledgerwatch/erigon/zk"
)

type InsertBatchConfig struct {
	ctx                 context.Context
	logPrefix           string
	shouldPrintProgress bool
}

func NewInsertBatchConfig(ctx context.Context, logPrefix string, shouldPrintProgress bool) InsertBatchConfig {
	return InsertBatchConfig{
		ctx:                 ctx,
		logPrefix:           logPrefix,
		shouldPrintProgress: shouldPrintProgress,
	}
}

func getProgressPrinterPre(logPrefix string, progressType string, size uint64, shouldPrintProgress bool) (progressChanPre *chan uint64, stopProgressPrinterPre func()) {
	var newChan chan uint64
	if shouldPrintProgress {
		newChan, stopProgressPrinterPre = zk.ProgressPrinter(fmt.Sprintf("[%s] SMT incremental progress (%s)", logPrefix, progressType), size, false)
	} else {
		newChan = make(chan uint64, size)
		var once sync.Once

		stopProgressPrinterPre = func() {
			once.Do(func() { close(newChan) })
		}
	}

	return &newChan, stopProgressPrinterPre
}

func (s *SMT) InsertBatch(cfg InsertBatchConfig, nodeKeys []*utils.NodeKey, nodeValues []*utils.NodeValue8, nodeValuesHashes []*[4]uint64, rootNodeHash *utils.NodeKey) (r *SMTResponse, err error) {
	s.clearUpMutex.Lock()
	defer s.clearUpMutex.Unlock()

	var (
		maxInsertingNodePathLevel = 0
		size                      = len(nodeKeys)
		smtBatchNodeRoot          *smtBatchNode
		nodeHashesForDelete       = make(map[uint64]map[uint64]map[uint64]map[uint64]*utils.NodeKey)
	)

	// BE CAREFUL: modifies the arrays
	if err := s.preprocessBatchedNodeValues(
		cfg.logPrefix,
		cfg.shouldPrintProgress,
		&nodeKeys,
		&nodeValues,
		&nodeValuesHashes,
		&rootNodeHash,
	); err != nil {
		return nil, fmt.Errorf("preprocessBatchedNodeValues: %w", err)
	}

	// DO NOT MOVE ABOVE PREPROCESS
	size = len(nodeKeys)

	progressChan, stopProgressPrinter := getProgressPrinterPre(cfg.logPrefix, "process", uint64(size), cfg.shouldPrintProgress)
	defer stopProgressPrinter()

	for i := 0; i < size; i++ {
		select {
		case <-cfg.ctx.Done():
			return nil, fmt.Errorf("context done")
		case *progressChan <- uint64(1):
		default:
		}

		insertingNodeKey := nodeKeys[i]
		insertingNodeValue := nodeValues[i]
		insertingNodeValueHash := nodeValuesHashes[i]
		insertingNodePath := insertingNodeKey.GetPath()
		insertingNodePathLevel, insertingPointerToSmtBatchNode, visitedNodeHashes, err := s.findInsertingPoint(insertingNodePath, rootNodeHash, &smtBatchNodeRoot, insertingNodeValue.IsZero())
		if err != nil {
			return nil, err
		}
		updateNodeHashesForDelete(nodeHashesForDelete, visitedNodeHashes)

		// special case if root does not exists yet
		if (*insertingPointerToSmtBatchNode) == nil {
			if !insertingNodeValue.IsZero() {
				*insertingPointerToSmtBatchNode = newSmtBatchNodeLeaf(insertingNodeKey, (*utils.NodeKey)(insertingNodeValueHash), nil)
			}
			// else branch would be for deleting a value but the root does not exists => there is nothing to delete
			continue
		}

		insertingRemainingKey := utils.RemoveKeyBits(*insertingNodeKey, insertingNodePathLevel)
		if !insertingNodeValue.IsZero() {
			if !((*insertingPointerToSmtBatchNode).isLeaf()) {
				if insertingPointerToSmtBatchNode, err = (*insertingPointerToSmtBatchNode).createALeafInEmptyDirection(insertingNodePath, insertingNodePathLevel, insertingNodeKey); err != nil {
					return nil, err
				}
				insertingRemainingKey = *((*insertingPointerToSmtBatchNode).nodeLeftHashOrRemainingKey)
				insertingNodePathLevel++
			}

			if !((*insertingPointerToSmtBatchNode).nodeLeftHashOrRemainingKey.IsEqualTo(insertingRemainingKey)) {
				currentTreeNodePath := utils.JoinKey(insertingNodePath[:insertingNodePathLevel], *(*insertingPointerToSmtBatchNode).nodeLeftHashOrRemainingKey).GetPath()
				for insertingNodePath[insertingNodePathLevel] == currentTreeNodePath[insertingNodePathLevel] {
					insertingPointerToSmtBatchNode = (*insertingPointerToSmtBatchNode).expandLeafByAddingALeafInDirection(insertingNodePath, insertingNodePathLevel)
					insertingNodePathLevel++
				}

				(*insertingPointerToSmtBatchNode).expandLeafByAddingALeafInDirection(currentTreeNodePath, insertingNodePathLevel)

				if insertingPointerToSmtBatchNode, err = (*insertingPointerToSmtBatchNode).createALeafInEmptyDirection(insertingNodePath, insertingNodePathLevel, insertingNodeKey); err != nil {
					return nil, err
				}
				insertingNodePathLevel++
			}

			(*insertingPointerToSmtBatchNode).nodeRightHashOrValueHash = (*utils.NodeKey)(insertingNodeValueHash)
		} else {
			if (*insertingPointerToSmtBatchNode).nodeLeftHashOrRemainingKey.IsEqualTo(insertingRemainingKey) {
				parentAfterDelete := &((*insertingPointerToSmtBatchNode).parentNode)
				*insertingPointerToSmtBatchNode = nil
				insertingPointerToSmtBatchNode = parentAfterDelete
				if (*insertingPointerToSmtBatchNode) != nil {
					(*insertingPointerToSmtBatchNode).updateHashesAfterDelete()
				}
				insertingNodePathLevel--
			}

			for {
				if *insertingPointerToSmtBatchNode == nil {
					break
				}

				if (*insertingPointerToSmtBatchNode).isLeaf() {
					break
				}

				theSingleNodeLeaf, theSingleNodeLeafDirection := (*insertingPointerToSmtBatchNode).getTheSingleLeafAndDirectionIfAny()
				if theSingleNodeLeaf == nil {
					break
				}

				insertingPointerToSmtBatchNode = (*insertingPointerToSmtBatchNode).collapseLeafByRemovingTheSingleLeaf(insertingNodePath, insertingNodePathLevel, theSingleNodeLeaf, theSingleNodeLeafDirection)
				insertingNodePathLevel--
			}
		}

		if maxInsertingNodePathLevel < insertingNodePathLevel {
			maxInsertingNodePathLevel = insertingNodePathLevel
		}
	}

	select {
	case *progressChan <- uint64(1):
	default:
	}
	stopProgressPrinter()

	if err := s.updateDepth(maxInsertingNodePathLevel); err != nil {
		return nil, fmt.Errorf("updateDepth: %w", err)
	}

	if err := s.deleteBatchedNodeValues(cfg.logPrefix, nodeHashesForDelete); err != nil {
		return nil, fmt.Errorf("deleteBatchedNodeValues: %w", err)
	}

	if err := s.saveBatchedNodeValues(cfg.logPrefix, nodeValues, nodeValuesHashes); err != nil {
		return nil, fmt.Errorf("saveBatchedNodeValues: %w", err)
	}

	// 4. Calculate and Save Hashes Dfs (此操作保持在主线程外部)
	if smtBatchNodeRoot == nil {
		rootNodeHash = &utils.NodeKey{0, 0, 0, 0}
	} else {
		sdh := newSmtDfsHelper(s)
		t1 := time.Now()

		go func() {
			defer sdh.destroy()

			calculateAndSaveHashesDfs(sdh, smtBatchNodeRoot, make([]int, 256), 0)
			rootNodeHash = (*utils.NodeKey)(smtBatchNodeRoot.hash)
		}()

		if !s.noSaveOnInsert {
			if err = sdh.startConsumersLoop(s); err != nil {
				return nil, fmt.Errorf("saving smt hashes dfs: %w", err)
			}
		}
		sdh.wg.Wait()
		log.Info("[FUCK] calculateAndSaveHashesDfs", "duration", time.Since(t1))
	}
	if err := s.setLastRoot(*rootNodeHash); err != nil {
		return nil, err
	}

	return &SMTResponse{
		Mode:          "batch insert",
		NewRootScalar: rootNodeHash,
	}, nil
}

// returns the new size of the values batch after removing duplicate entries
func (s *SMT) preprocessBatchedNodeValues(
	logPrefix string,
	shouldPrintProgress bool,
	nodeKeys *[]*utils.NodeKey,
	nodeValues *[]*utils.NodeValue8,
	nodeValuesHashes *[]*[4]uint64,
	rootNodeHash **utils.NodeKey,
) error {
	progressChanPre, stopProgressPrinterPre := getProgressPrinterPre(logPrefix, "pre-process", 4, shouldPrintProgress)
	defer stopProgressPrinterPre()

	if err := validateDataLengths(*nodeKeys, *nodeValues, nodeValuesHashes); err != nil {
		return fmt.Errorf("validateDataLengths: %w", err)
	}
	*progressChanPre <- uint64(1)

	if err := removeDuplicateEntriesByKeys(nodeKeys, nodeValues, nodeValuesHashes); err != nil {
		return fmt.Errorf("removeDuplicateEntriesByKeys: %w", err)
	}
	*progressChanPre <- uint64(1)

	if err := calculateNodeValueHashesIfMissing(*nodeValues, nodeValuesHashes); err != nil {
		return fmt.Errorf("calculateNodeValueHashesIfMissing: %w", err)
	}
	*progressChanPre <- uint64(1)

	if err := calculateRootNodeHashIfNil(s, rootNodeHash); err != nil {
		return fmt.Errorf("calculateRootNodeHashIfNil: %w", err)
	}
	*progressChanPre <- uint64(1)
	stopProgressPrinterPre()

	return nil
}

func (s *SMT) deleteBatchedNodeValues(
	logPrefix string,
	nodeHashesForDelete map[uint64]map[uint64]map[uint64]map[uint64]*utils.NodeKey,
) error {
	progressChanDel, stopProgressPrinterDel := getProgressPrinterPre(logPrefix, "deletes", uint64(len(nodeHashesForDelete)), false)
	defer stopProgressPrinterDel()

	for _, mapLevel0 := range nodeHashesForDelete {
		*progressChanDel <- uint64(1)
		for _, mapLevel1 := range mapLevel0 {
			for _, mapLevel2 := range mapLevel1 {
				for _, nodeHash := range mapLevel2 {
					if err := s.Db.DeleteByNodeKey(*nodeHash); err != nil {
						return fmt.Errorf("DeleteByNodeKey: %w", err)
					}
					if err := s.Db.DeleteHashKey(*nodeHash); err != nil {
						return fmt.Errorf("DeleteHashKey: %w", err)
					}
				}
			}
		}
	}
	stopProgressPrinterDel()

	return nil
}

func (s *SMT) saveBatchedNodeValues(
	logPrefix string,
	nodeValues []*utils.NodeValue8,
	nodeValuesHashes []*[4]uint64,
) error {
	progressChanFin, stopProgressPrinterFin := getProgressPrinterPre(logPrefix, "finalize", uint64(len(nodeValues)), false)
	defer stopProgressPrinterFin()

	for i, nodeValue := range nodeValues {
		select {
		case *progressChanFin <- uint64(1):
		default:
		}
		if !nodeValue.IsZero() {
			if err := s.hashSaveByPointers(nodeValue.ToUintArrayByPointer(), &utils.BranchCapacity, nodeValuesHashes[i]); err != nil {
				return err
			}
		}
	}
	stopProgressPrinterFin()
	return nil
}

func validateDataLengths(
	nodeKeys []*utils.NodeKey,
	nodeValues []*utils.NodeValue8,
	nodeValuesHashes *[]*[4]uint64,
) error {
	var size int = len(nodeKeys)

	if len(nodeValues) != size {
		return fmt.Errorf("mismatch nodeValues length, expected %d but got %d", size, len(nodeValues))
	}

	if (*nodeValuesHashes) == nil {
		(*nodeValuesHashes) = make([]*[4]uint64, size)
	}
	if len(*nodeValuesHashes) != size {
		return fmt.Errorf("mismatch nodeValuesHashes length, expected %d but got %d", size, len(*nodeValuesHashes))
	}

	return nil
}

func removeDuplicateEntriesByKeys(
	nodeKeys *[]*utils.NodeKey,
	nodeValues *[]*utils.NodeValue8,
	nodeValuesHashes *[]*[4]uint64,
) error {
	size := len(*nodeKeys)
	storage := make(map[uint64]map[uint64]map[uint64]map[uint64]int)

	resultNodeKeys := make([]*utils.NodeKey, 0, size)
	resultNodeValues := make([]*utils.NodeValue8, 0, size)
	resultNodeValuesHashes := make([]*[4]uint64, 0, size)

	for i, nodeKey := range *nodeKeys {
		setNodeKeyMapValue(storage, nodeKey, i)
	}

	for i, nodeKey := range *nodeKeys {
		latestIndex, found := getNodeKeyMapValue(storage, nodeKey)
		if !found {
			return fmt.Errorf("key not found")
		}

		if latestIndex == i {
			resultNodeKeys = append(resultNodeKeys, nodeKey)
			resultNodeValues = append(resultNodeValues, (*nodeValues)[i])
			resultNodeValuesHashes = append(resultNodeValuesHashes, (*nodeValuesHashes)[i])
		}
	}

	*nodeKeys = resultNodeKeys
	*nodeValues = resultNodeValues
	*nodeValuesHashes = resultNodeValuesHashes

	return nil
}

func calculateNodeValueHashesIfMissing(
	nodeValues []*utils.NodeValue8,
	nodeValuesHashes *[]*[4]uint64,
) error {
	var globalError error
	size := len(nodeValues)
	cpuNum := parallel.DefaultNumGoroutines()

	if size > (cpuNum << 2) {
		var wg sync.WaitGroup
		itemsPerCpu := (size + cpuNum - 1) / cpuNum

		wg.Add(cpuNum)

		for cpuIndex := 0; cpuIndex < cpuNum; cpuIndex++ {
			go func(cpuIndexInThread int) {
				defer wg.Done()
				startIndex := cpuIndexInThread * itemsPerCpu
				endIndex := startIndex + itemsPerCpu
				if endIndex > size {
					endIndex = size
				}
				err := calculateNodeValueHashesIfMissingInInterval(nodeValues, nodeValuesHashes, startIndex, endIndex)
				if err != nil {
					globalError = err
				}
			}(cpuIndex)
		}

		wg.Wait()
	} else {
		globalError = calculateNodeValueHashesIfMissingInInterval(nodeValues, nodeValuesHashes, 0, len(nodeValues))
	}

	return globalError
}

func calculateNodeValueHashesIfMissingInInterval(
	nodeValues []*utils.NodeValue8,
	nodeValuesHashes *[]*[4]uint64,
	startIndex,
	endIndex int,
) error {
	for i := startIndex; i < endIndex; i++ {
		if (*nodeValuesHashes)[i] != nil {
			continue
		}

		nodeValueHashObj := utils.Hash(nodeValues[i].ToUintArray(), utils.BranchCapacity)
		(*nodeValuesHashes)[i] = &nodeValueHashObj
	}

	return nil
}

func calculateRootNodeHashIfNil(s *SMT, root **utils.NodeKey) error {
	if (*root) == nil {
		oldRootObj, err := s.getLastRoot()
		if err != nil {
			return err
		}
		(*root) = &oldRootObj
	}
	return nil
}

func (s *SMT) findInsertingPoint(
	insertingNodePath []int,
	insertingPointerNodeHash *utils.NodeKey,
	insertingPointerToSmtBatchNode **smtBatchNode,
	fetchDirectSiblings bool,
) (
	insertingNodePathLevel int,
	nextInsertingPointerToSmtBatchNode **smtBatchNode,
	visitedNodeHashes []*utils.NodeKey,
	err error,
) {
	insertingNodePathLevel = -1
	visitedNodeHashes = make([]*utils.NodeKey, 0, 256)
	visitedNodeMap := make(map[string]struct{}) // 用于避免重复添加节点

	var (
		insertingPointerToSmtBatchNodeParent *smtBatchNode
		nextInsertingPointerNodeHash         *utils.NodeKey
	)

	// 辅助函数：将 NodeKey 转换为 BigInt 字符串
	toBigIntString := func(nodeKey *utils.NodeKey) string {
		return nodeKey.ToBigInt().String()
	}

	for {
		if (*insertingPointerToSmtBatchNode) == nil { // 从数据库更新内存结构
			if !insertingPointerNodeHash.IsZero() {
				*insertingPointerToSmtBatchNode, err = s.fetchNodeDataFromDb(insertingPointerNodeHash, insertingPointerToSmtBatchNodeParent)
				if err != nil {
					return -2, insertingPointerToSmtBatchNode, visitedNodeHashes, err
				}

				// 使用 ToBigInt() 进行去重操作
				nodeHashStr := toBigIntString(insertingPointerNodeHash)
				if _, exists := visitedNodeMap[nodeHashStr]; !exists {
					visitedNodeHashes = append(visitedNodeHashes, insertingPointerNodeHash)
					visitedNodeMap[nodeHashStr] = struct{}{}
				}
			} else {
				if insertingNodePathLevel != -1 {
					return -2, insertingPointerToSmtBatchNode, visitedNodeHashes, fmt.Errorf("nodekey is zero at non-root level")
				}
			}
		}

		if (*insertingPointerToSmtBatchNode) == nil {
			if insertingNodePathLevel != -1 {
				return -2, insertingPointerToSmtBatchNode, visitedNodeHashes, fmt.Errorf("working smt pointer is nil at non-root level")
			}
			break
		}

		insertingNodePathLevel++

		// 如果节点是叶子节点，跳出循环
		if (*insertingPointerToSmtBatchNode).isLeaf() {
			break
		}

		if fetchDirectSiblings {
			// 批量加载左兄弟和右兄弟
			err := s.fetchSiblingNodes(*insertingPointerToSmtBatchNode)
			if err != nil {
				return -2, insertingPointerToSmtBatchNode, visitedNodeHashes, err
			}

			// 记录访问的兄弟节点，避免重复添加
			leftHashStr := toBigIntString((*insertingPointerToSmtBatchNode).nodeLeftHashOrRemainingKey)
			if _, exists := visitedNodeMap[leftHashStr]; !exists {
				visitedNodeHashes = append(visitedNodeHashes, (*insertingPointerToSmtBatchNode).nodeLeftHashOrRemainingKey)
				visitedNodeMap[leftHashStr] = struct{}{}
			}

			rightHashStr := toBigIntString((*insertingPointerToSmtBatchNode).nodeRightHashOrValueHash)
			if _, exists := visitedNodeMap[rightHashStr]; !exists {
				visitedNodeHashes = append(visitedNodeHashes, (*insertingPointerToSmtBatchNode).nodeRightHashOrValueHash)
				visitedNodeMap[rightHashStr] = struct{}{}
			}
		}

		insertDirection := insertingNodePath[insertingNodePathLevel]
		// 使用 getNextNodeInfo 获取下一个节点的哈希和指针
		nextInsertingPointerNodeHash, nextInsertingPointerToSmtBatchNode = (*insertingPointerToSmtBatchNode).getNextNodeInfo(insertDirection)

		if nextInsertingPointerNodeHash.IsZero() && (*nextInsertingPointerToSmtBatchNode) == nil {
			break
		}

		insertingPointerNodeHash = nextInsertingPointerNodeHash
		insertingPointerToSmtBatchNodeParent = *insertingPointerToSmtBatchNode
		insertingPointerToSmtBatchNode = nextInsertingPointerToSmtBatchNode
	}

	return insertingNodePathLevel, insertingPointerToSmtBatchNode, visitedNodeHashes, nil
}

func (s *SMT) fetchSiblingNodes(node *smtBatchNode) error {
	var err error
	if node.leftNode == nil {
		node.leftNode, err = s.fetchNodeDataFromDb(node.nodeLeftHashOrRemainingKey, node)
		if err != nil {
			return err
		}
	}
	if node.rightNode == nil {
		node.rightNode, err = s.fetchNodeDataFromDb(node.nodeRightHashOrValueHash, node)
		if err != nil {
			return err
		}
	}
	return nil
}

func updateNodeHashesForDelete(
	nodeHashesForDelete map[uint64]map[uint64]map[uint64]map[uint64]*utils.NodeKey,
	visitedNodeHashes []*utils.NodeKey,
) {
	for _, visitedNodeHash := range visitedNodeHashes {
		if visitedNodeHash == nil {
			continue
		}

		setNodeKeyMapValue(nodeHashesForDelete, visitedNodeHash, visitedNodeHash)
	}
}

func calculateAndSaveHashesDfs(
	sdh *smtDfsHelper,
	smtBatchRootNode *smtBatchNode,
	path []int,
	level int,
) {
	const maxConcurrencyFactor = 2
	dataChan := sdh.dataChan
	noSave := sdh.s.noSaveOnInsert

	// Handle leaf node inline
	if smtBatchRootNode.isLeaf() {
		hashObj, hashValue := utils.HashKeyAndValueByPointers(
			utils.ConcatArrays4ByPointers(
				smtBatchRootNode.nodeLeftHashOrRemainingKey.AsUint64Pointer(),
				smtBatchRootNode.nodeRightHashOrValueHash.AsUint64Pointer(),
			),
			&utils.LeafCapacity,
		)
		smtBatchRootNode.hash = hashObj

		if !noSave && len(dataChan) < cap(dataChan) {
			buffer1 := newSmtDfsHelperDataStruct(hashObj, hashValue)
			buffer2 := newSmtDfsHelperDataStruct(hashObj, utils.JoinKey(path[:level], *smtBatchRootNode.nodeLeftHashOrRemainingKey))
			select {
			case dataChan <- buffer1:
				dataChan <- buffer2
			default:
			}
		}
		return
	}

	// Initialize path pool and semaphore
	var pathPool = sync.Pool{
		New: func() interface{} {
			return make([]int, 0, cap(path)) // Use original capacity
		},
	}
	maxConcurrency := runtime.NumCPU() * maxConcurrencyFactor
	sem := make(chan struct{}, maxConcurrency)
	var wg sync.WaitGroup
	var totalHash utils.NodeValue8

	// Process children
	children := [2]*smtBatchNode{smtBatchRootNode.leftNode, smtBatchRootNode.rightNode}
	for i, child := range children {
		if child == nil {
			defaultHash := smtBatchRootNode.nodeLeftHashOrRemainingKey
			if i == 1 {
				defaultHash = smtBatchRootNode.nodeRightHashOrValueHash
			}
			totalHash.SetHalfValue(*defaultHash, i)
			continue
		}

		// Ensure path has enough length for the new level
		if level >= len(path) {
			path = append(path, 0) // Grow path if needed
		}
		path[level] = i

		if level < 3 { // Serial processing for shallow levels
			calculateAndSaveHashesDfs(sdh, child, path, level+1)
			totalHash.SetHalfValue(*child.hash, i)
		} else { // Parallel processing for deeper levels
			wg.Add(1)
			sem <- struct{}{}
			childPath := append(pathPool.Get().([]int), path[:level+1]...)

			go func(c *smtBatchNode, p []int) {
				defer func() {
					<-sem
					pathPool.Put(p[:0])
					wg.Done()
				}()
				calculateAndSaveHashesDfs(sdh, c, p, level+1)
			}(child, childPath)
		}
	}

	// Wait for all goroutines to complete
	wg.Wait()

	// Update totalHash with child hashes after all are computed
	for i, child := range children {
		if child != nil && level >= 3 {
			totalHash.SetHalfValue(*child.hash, i)
		}
	}

	// Compute and set the current node's hash
	hashObj, hashValue := utils.HashKeyAndValueByPointers(totalHash.ToUintArrayByPointer(), &utils.BranchCapacity)
	smtBatchRootNode.hash = hashObj

	if !noSave && len(dataChan) < cap(dataChan) {
		dataChan <- newSmtDfsHelperDataStruct(hashObj, hashValue)
	}
}

type smtBatchNode struct {
	nodeLeftHashOrRemainingKey *utils.NodeKey
	nodeRightHashOrValueHash   *utils.NodeKey
	leaf                       bool
	parentNode                 *smtBatchNode // if nil => this is the root node
	leftNode                   *smtBatchNode
	rightNode                  *smtBatchNode
	hash                       *[4]uint64
}

func newSmtBatchNodeLeaf(
	nodeLeftHashOrRemainingKey,
	nodeRightHashOrValueHash *utils.NodeKey,
	parentNode *smtBatchNode,
) *smtBatchNode {
	return &smtBatchNode{
		nodeLeftHashOrRemainingKey: nodeLeftHashOrRemainingKey,
		nodeRightHashOrValueHash:   nodeRightHashOrValueHash,
		leaf:                       true,
		parentNode:                 parentNode,
		leftNode:                   nil,
		rightNode:                  nil,
		hash:                       nil,
	}
}

func (s *SMT) fetchNodeDataFromDb(nodeHash *utils.NodeKey, parentNode *smtBatchNode) (*smtBatchNode, error) {
	if nodeHash.IsZero() {
		return nil, nil
	}

	dbNodeValue, err := s.Db.Get(*nodeHash)
	if err != nil {
		return nil, err
	}

	nodeLeftHashOrRemainingKey := utils.NodeKeyFromBigIntArray(dbNodeValue[0:4])
	nodeRightHashOrValueHash := utils.NodeKeyFromBigIntArray(dbNodeValue[4:8])
	return &smtBatchNode{
		parentNode:                 parentNode,
		nodeLeftHashOrRemainingKey: &nodeLeftHashOrRemainingKey,
		nodeRightHashOrValueHash:   &nodeRightHashOrValueHash,
		leaf:                       dbNodeValue.IsFinalNode(),
	}, nil
}

func (sbn *smtBatchNode) isLeaf() bool {
	return sbn.leaf
}

func (node *smtBatchNode) getNextNodeInfo(insertDirection int) (*utils.NodeKey, **smtBatchNode) {
	var nextNodeHash *utils.NodeKey
	var nextNodePointer **smtBatchNode

	// 根据插入方向选择左或右节点
	if insertDirection == 0 { // 假设 0 是左子节点
		nextNodeHash = node.nodeLeftHashOrRemainingKey
		nextNodePointer = &node.leftNode
	} else { // 其他情况下是右子节点
		nextNodeHash = node.nodeRightHashOrValueHash
		nextNodePointer = &node.rightNode
	}

	return nextNodeHash, nextNodePointer
}

func (sbn *smtBatchNode) getTheSingleLeafAndDirectionIfAny() (*smtBatchNode, int) {
	if sbn.leftNode != nil && sbn.rightNode == nil && sbn.leftNode.isLeaf() {
		return sbn.leftNode, 0
	}
	if sbn.leftNode == nil && sbn.rightNode != nil && sbn.rightNode.isLeaf() {
		return sbn.rightNode, 1
	}
	return nil, -1
}

func (sbn *smtBatchNode) getNextNodeHashInDirection(direction int) *utils.NodeKey {
	if direction == 0 {
		return sbn.nodeLeftHashOrRemainingKey
	} else {
		return sbn.nodeRightHashOrValueHash
	}
}

func (sbn *smtBatchNode) getChildInDirection(direction int) **smtBatchNode {
	if direction == 0 {
		return &sbn.leftNode
	} else {
		return &sbn.rightNode
	}
}

func (sbn *smtBatchNode) updateHashesAfterDelete() {
	if sbn.leftNode == nil {
		sbn.nodeLeftHashOrRemainingKey = &utils.NodeKey{0, 0, 0, 0}
	}
	if sbn.rightNode == nil {
		sbn.nodeRightHashOrValueHash = &utils.NodeKey{0, 0, 0, 0}
	}
}

func (sbn *smtBatchNode) createALeafInEmptyDirection(
	insertingNodePath []int,
	insertingNodePathLevel int,
	insertingNodeKey *utils.NodeKey,
) (**smtBatchNode, error) {
	direction := insertingNodePath[insertingNodePathLevel]
	childPointer := sbn.getChildInDirection(direction)
	if (*childPointer) != nil {
		return nil, fmt.Errorf("branch has already been taken")
	}
	remainingKey := utils.RemoveKeyBits(*insertingNodeKey, insertingNodePathLevel+1)
	*childPointer = newSmtBatchNodeLeaf(&remainingKey, nil, sbn)
	return childPointer, nil
}

func (sbn *smtBatchNode) expandLeafByAddingALeafInDirection(
	insertingNodeKey []int,
	insertingNodeKeyLevel int,
) **smtBatchNode {
	direction := insertingNodeKey[insertingNodeKeyLevel]
	insertingNodeKeyUpToLevel := insertingNodeKey[:insertingNodeKeyLevel]

	childPointer := sbn.getChildInDirection(direction)

	nodeKey := utils.JoinKey(insertingNodeKeyUpToLevel, *sbn.nodeLeftHashOrRemainingKey)
	remainingKey := utils.RemoveKeyBits(*nodeKey, insertingNodeKeyLevel+1)

	*childPointer = newSmtBatchNodeLeaf(&remainingKey, sbn.nodeRightHashOrValueHash, sbn)
	sbn.nodeLeftHashOrRemainingKey = &utils.NodeKey{0, 0, 0, 0}
	sbn.nodeRightHashOrValueHash = &utils.NodeKey{0, 0, 0, 0}
	sbn.leaf = false

	return childPointer
}

func (sbn *smtBatchNode) collapseLeafByRemovingTheSingleLeaf(
	insertingNodeKey []int,
	insertingNodeKeyLevel int,
	theSingleLeaf *smtBatchNode,
	theSingleNodeLeafDirection int,
) **smtBatchNode {
	insertingNodeKeyUpToLevel := insertingNodeKey[:insertingNodeKeyLevel+1]
	insertingNodeKeyUpToLevel[insertingNodeKeyLevel] = theSingleNodeLeafDirection
	nodeKey := utils.JoinKey(insertingNodeKeyUpToLevel, *theSingleLeaf.nodeLeftHashOrRemainingKey)
	remainingKey := utils.RemoveKeyBits(*nodeKey, insertingNodeKeyLevel)

	sbn.nodeLeftHashOrRemainingKey = &remainingKey
	sbn.nodeRightHashOrValueHash = theSingleLeaf.nodeRightHashOrValueHash
	sbn.leaf = true
	sbn.leftNode = nil
	sbn.rightNode = nil

	return &sbn.parentNode
}

type smtDfsHelperDataStruct struct {
	key   *[4]uint64
	value interface{}
}

func newSmtDfsHelperDataStruct(key *[4]uint64, value interface{}) *smtDfsHelperDataStruct {
	return &smtDfsHelperDataStruct{
		key:   key,
		value: value,
	}
}

type smtDfsHelper struct {
	s        *SMT
	dataChan chan *smtDfsHelperDataStruct
	wg       *sync.WaitGroup
	once     *sync.Once
}

func newSmtDfsHelper(s *SMT) *smtDfsHelper {
	sdh := &smtDfsHelper{
		s:        s,
		dataChan: make(chan *smtDfsHelperDataStruct, 1<<16),
		wg:       &sync.WaitGroup{},
		once:     &sync.Once{},
	}

	sdh.wg.Add(1)

	return sdh
}

func (sdh *smtDfsHelper) destroy() {
	sdh.once.Do(func() {
		close(sdh.dataChan)
		sdh.wg.Done()
	})
}

func (sdh *smtDfsHelper) startConsumersLoop(s *SMT) error {
	for {
		dataStruct, ok := <-sdh.dataChan
		if !ok {
			return nil
		}

		switch castedDataStruct := dataStruct.value.(type) {
		case *utils.NodeKey:
			if err := s.Db.InsertHashKey(*dataStruct.key, *castedDataStruct); err != nil {
				return fmt.Errorf("calculating and saving hashes dfs: %w", err)
			}
		case *utils.NodeValue12:
			if err := s.Db.Insert(*dataStruct.key, *castedDataStruct); err != nil {
				return fmt.Errorf("calculating and saving hashes dfs: %w", err)
			}
		}
	}
}

func setNodeKeyMapValue[T int | *utils.NodeKey](
	nodeKeyMap map[uint64]map[uint64]map[uint64]map[uint64]T,
	nodeKey *utils.NodeKey,
	value T,
) {
	mapLevel0, found := nodeKeyMap[nodeKey[0]]
	if !found {
		mapLevel0 = make(map[uint64]map[uint64]map[uint64]T)
		nodeKeyMap[nodeKey[0]] = mapLevel0
	}

	mapLevel1, found := mapLevel0[nodeKey[1]]
	if !found {
		mapLevel1 = make(map[uint64]map[uint64]T)
		mapLevel0[nodeKey[1]] = mapLevel1
	}

	mapLevel2, found := mapLevel1[nodeKey[2]]
	if !found {
		mapLevel2 = make(map[uint64]T)
		mapLevel1[nodeKey[2]] = mapLevel2
	}

	mapLevel2[nodeKey[3]] = value
}

func getNodeKeyMapValue[T int | *utils.NodeKey](
	nodeKeyMap map[uint64]map[uint64]map[uint64]map[uint64]T,
	nodeKey *utils.NodeKey,
) (T, bool) {
	var notExistingValue T

	mapLevel0, found := nodeKeyMap[nodeKey[0]]
	if !found {
		return notExistingValue, false
	}

	mapLevel1, found := mapLevel0[nodeKey[1]]
	if !found {
		return notExistingValue, false
	}

	mapLevel2, found := mapLevel1[nodeKey[2]]
	if !found {
		return notExistingValue, false
	}

	value, found := mapLevel2[nodeKey[3]]
	return value, found
}
