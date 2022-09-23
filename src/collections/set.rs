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

use std::collections::HashSet;
use std::hash::{BuildHasher, Hash};

/// A (finite) set of items (node or edges) of a graph.
pub trait ItemSet<I>
where
    I: Copy,
{
    /// Return `true` if this set is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return the number of items in this set.
    fn len(&self) -> usize;

    /// Remove all nodes from the set.
    fn clear(&mut self);

    /// Add one item to the set.
    ///
    /// Return `true` iff `u` had not been contained in this set before.
    fn insert(&mut self, u: I) -> bool;

    /// Remove one item from the set.
    ///
    /// Returns `true` if the item had been contained in the set, otherwise
    /// false.
    fn remove(&mut self, u: I) -> bool;

    /// Return `true` iff item `u` is contained in this set.
    fn contains(&self, u: I) -> bool;
}

impl<'a, N, S> ItemSet<N> for &'a mut S
where
    S: ItemSet<N>,
    N: Copy,
{
    fn is_empty(&self) -> bool {
        (**self).is_empty()
    }

    fn len(&self) -> usize {
        (**self).len()
    }

    fn clear(&mut self) {
        (**self).clear()
    }

    fn insert(&mut self, u: N) -> bool {
        (**self).insert(u)
    }

    fn remove(&mut self, u: N) -> bool {
        (**self).remove(u)
    }

    fn contains(&self, u: N) -> bool {
        (**self).contains(u)
    }
}

impl<N, B> ItemSet<N> for HashSet<N, B>
where
    N: Copy + Eq + Hash,
    B: BuildHasher,
{
    fn is_empty(&self) -> bool {
        HashSet::is_empty(self)
    }

    fn len(&self) -> usize {
        HashSet::len(self)
    }

    fn clear(&mut self) {
        HashSet::clear(self)
    }

    fn insert(&mut self, u: N) -> bool {
        HashSet::insert(self, u)
    }

    fn remove(&mut self, u: N) -> bool {
        HashSet::remove(self, &u)
    }

    fn contains(&self, u: N) -> bool {
        HashSet::contains(self, &u)
    }
}
