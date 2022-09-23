/*
 * Copyright (c) 2018 Frank Fischer <frank-fischer@shadow-soft.de>
 *
 * This program is free software: you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see  <http://www.gnu.org/licenses/>
 */

mod binheap;
pub use self::binheap::BinHeap;

pub trait ItemPriQueue<K, V> {
    /// Handle for an item in the queue.
    type Item;

    /// Return `true` iff the queue contains no element.
    fn is_empty(&self) -> bool;

    /// Remove all elements from the queue.
    fn clear(&mut self);

    /// Push the element with given `key` and `value` onto the queue.
    ///
    /// Return a handle referencing the element. That handle can be used in a
    /// subsequent call to `decrease_key`.
    fn push(&mut self, key: K, value: V) -> Self::Item;

    /// Decrease the value of some item in the queue.
    ///
    /// Returns `true` if the new value is smaller than the old one.
    fn decrease_key(&mut self, item: &mut Self::Item, value: V) -> bool;

    /// Remove and return the element with the smallest value from the queue or `None` if
    /// the queue is empty.
    fn pop_min(&mut self) -> Option<(K, V)>;

    /// Return the current value associated with some item in the queue.
    fn value(&self, item: &Self::Item) -> &V;
}

impl<'a, P, K, V> ItemPriQueue<K, V> for &'a mut P
where
    P: ItemPriQueue<K, V>,
{
    type Item = P::Item;

    fn is_empty(&self) -> bool {
        (**self).is_empty()
    }

    fn clear(&mut self) {
        (**self).clear()
    }

    fn push(&mut self, key: K, value: V) -> Self::Item {
        (**self).push(key, value)
    }

    fn decrease_key(&mut self, item: &mut Self::Item, value: V) -> bool {
        (**self).decrease_key(item, value)
    }

    fn pop_min(&mut self) -> Option<(K, V)> {
        (**self).pop_min()
    }

    fn value(&self, item: &Self::Item) -> &V {
        (**self).value(item)
    }
}
