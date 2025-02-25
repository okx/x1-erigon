// For X Layer

package common

import (
	"slices"
	"sync"
)

type OrderedList[T any] struct {
	list        []T
	lock        sync.RWMutex
	isOrdered   bool
	compareFunc func(a, b T) int
}

func (l *OrderedList[T]) Add(item T) {
	l.lock.Lock()
	defer l.lock.Unlock()
	l.isOrdered = false
	l.list = append(l.list, item)
}

func (l *OrderedList[T]) Sort() {
	l.lock.Lock()
	defer l.lock.Unlock()
	slices.SortFunc(l.list, l.compareFunc)
	l.isOrdered = true
}

func (l *OrderedList[T]) containsBinarySearch(item T) bool {
	upper := len(l.list)
	lower := 0
	for lower < upper {
		mid := (upper + lower) / 2
		cmp := l.compareFunc(item, l.list[mid])
		if cmp == 0 {
			return true
		}
		if cmp > 0 {
			lower = mid + 1
		} else {
			upper = mid
		}
	}
	return false
}

func (l *OrderedList[T]) containsLinear(item T) bool {
	for _, i := range l.list {
		if l.compareFunc(i, item) == 0 {
			return true
		}
	}
	return false
}

func (l *OrderedList[T]) Contains(item T) bool {
	l.lock.RLock()
	defer l.lock.RUnlock()
	if !l.isOrdered {
		return l.containsLinear(item)
	}
	return l.containsBinarySearch(item)
}

func (l *OrderedList[T]) Size() int {
	return len(l.list)
}

func (l *OrderedList[T]) Items() []T {
	l.lock.RLock()
	defer l.lock.RUnlock()
	return l.list
}

func AddItemsAndSort[T, U any](l *OrderedList[T], items []U, convert func(U) T) {
	l.lock.Lock()
	defer l.lock.Unlock()
	for _, item := range items {
		l.list = append(l.list, convert(item))
	}
	slices.SortFunc(l.list, l.compareFunc)
	l.isOrdered = true
}
