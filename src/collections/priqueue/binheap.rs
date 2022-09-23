// Copyright (c) 2016, 2017, 2020 Frank Fischer <frank-fischer@shadow-soft.de>
//
// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see  <http://www.gnu.org/licenses/>
//

//! Binary heap implementation

use crate::collections::ItemPriQueue;

use num_traits::{FromPrimitive, ToPrimitive};

/// Heap item information.
struct BinHeapItem<K, V, ID> {
    /// The key associated with this item.
    key: K,
    /// The value (priority) of the item.
    value: V,
    /// Position of this element on the heap. If this element is *not*
    /// on the heap, its the index of the next element in the free
    /// list.
    pos: ID,
}

/// Simply binary heap data structure.
pub struct BinHeap<K, V, ID = u32> {
    /// The heap elements.
    heap: Vec<ID>,
    /// The key and heap-index for each element.
    data: Vec<BinHeapItem<K, V, ID>>,
    /// First free item.
    free: Option<ID>,
}

impl<K, V> BinHeap<K, V> {
    pub fn new() -> Self {
        Default::default()
    }
}

impl<K, V, ID> Default for BinHeap<K, V, ID> {
    fn default() -> Self {
        BinHeap {
            heap: vec![],
            data: vec![],
            free: None,
        }
    }
}

impl<K, V, ID> ItemPriQueue<K, V> for BinHeap<K, V, ID>
where
    K: Clone,
    V: PartialOrd + Clone,
    ID: FromPrimitive + ToPrimitive + Copy + Eq,
{
    type Item = ID;

    fn clear(&mut self) {
        self.heap.clear();
        self.data.clear();
        self.free = None;
    }

    fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    fn value(&self, item: &ID) -> &V {
        &self.data[item.to_usize().unwrap()].value
    }

    fn push(&mut self, key: K, value: V) -> ID {
        let item = if let Some(item) = self.free {
            let idx = item.to_usize().unwrap();
            // take from free list
            let next = self.data[idx].pos;
            if next == item {
                self.free = None
            } else {
                self.free = Some(next)
            }
            // store data
            self.data[idx] = BinHeapItem {
                key,
                value,
                pos: ID::from_usize(self.heap.len()).unwrap(),
            };
            item
        } else {
            let item = ID::from_usize(self.data.len()).unwrap();
            self.data.push(BinHeapItem {
                key,
                value,
                pos: ID::from_usize(self.heap.len()).unwrap(),
            });
            item
        };
        self.heap.push(item);
        self.upheap(item);
        item
    }

    fn decrease_key(&mut self, item: &mut ID, value: V) -> bool {
        let idx = item.to_usize().unwrap();
        if self.data[idx].value > value {
            self.data[idx].value = value;
            self.upheap(*item);
            true
        } else {
            false
        }
    }

    fn pop_min(&mut self) -> Option<(K, V)> {
        if self.heap.is_empty() {
            return None;
        }

        // remove the smallest element from the heap
        let min_item = self.heap.swap_remove(0);
        let min_idx = min_item.to_usize().unwrap();
        // put its data slot in the free list
        if let Some(next) = self.free {
            // free list is not empty
            self.data[min_idx].pos = next;
        } else {
            // free list has been empty, this is the first element
            self.data[min_idx].pos = min_item;
        }
        self.free = Some(min_item);

        if !self.heap.is_empty() {
            let n = self.heap.len();
            let item = *self.heap.first().unwrap();
            let idx = item.to_usize().unwrap();
            let value = self.data[idx].value.clone();
            let mut cur_pos = 0;
            loop {
                let left_pos = 2 * cur_pos + 1;
                let right_pos = left_pos + 1;
                let (next_pos, next_idx) = if left_pos >= n {
                    break;
                } else if right_pos >= n {
                    (left_pos, self.heap[left_pos].to_usize().unwrap())
                } else {
                    let left_idx = self.heap[left_pos].to_usize().unwrap();
                    let right_idx = self.heap[right_pos].to_usize().unwrap();
                    if self.data[left_idx].value < self.data[right_idx].value {
                        (left_pos, left_idx)
                    } else {
                        (right_pos, right_idx)
                    }
                };

                if value <= self.data[next_idx].value {
                    break;
                }

                self.heap[cur_pos] = self.heap[next_pos];
                self.data[next_idx].pos = ID::from_usize(cur_pos).unwrap();
                cur_pos = next_pos;
            }
            self.heap[cur_pos] = item;
            self.data[idx].pos = ID::from_usize(cur_pos).unwrap();
        }
        Some((self.data[min_idx].key.clone(), self.data[min_idx].value.clone()))
    }
}

impl<K, V, ID> BinHeap<K, V, ID>
where
    V: PartialOrd + Clone,
    ID: FromPrimitive + ToPrimitive + Clone + Eq,
{
    /// Move the element `item` up in the heap until its parent does not have a
    /// larger key or the root node is reached.
    ///
    /// Note that this function assumes that its value is smaller than the value
    /// of its children.
    fn upheap(&mut self, item: ID) {
        let idx = item.to_usize().unwrap();
        let value = self.data[idx].value.clone();
        let mut cur_pos = self.data[idx].pos.to_usize().unwrap();
        while cur_pos > 0 {
            let parent_pos = (cur_pos - 1) / 2;
            let parent_idx = self.heap[parent_pos].to_usize().unwrap();
            // We could have used >=, too, but using >
            // moves the item up the heap as far as possible. This results the
            // last node touched with the same value to be considered next (to a
            // certain extend) making the search more dfs like.
            if value > self.data[parent_idx].value {
                break;
            }
            self.heap[cur_pos] = self.heap[parent_pos].clone();
            self.data[parent_idx].pos = ID::from_usize(cur_pos).unwrap();
            cur_pos = parent_pos;
        }
        self.data[idx].pos = ID::from_usize(cur_pos).unwrap();
        self.heap[cur_pos] = item;
    }
}
