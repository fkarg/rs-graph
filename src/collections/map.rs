/*
 * Copyright (c) 2018, 2020, 2021, 2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

use crate::traits::IndexGraph;
use std::collections::HashMap;
use std::hash::{BuildHasher, Hash};

/// A (finite) map of items (node or edges) of a graph to some value.
pub trait ItemMap<K, V>
where
    K: Copy,
{
    /// Return `true` if this map is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return the number of items in this map.
    fn len(&self) -> usize;

    /// Remove all items from the map.
    fn clear(&mut self);

    /// Add one item to the map.
    ///
    /// Return `true` iff `u` had not been contained in this map before. Otherwise
    /// case the value is *not* updated.
    fn insert(&mut self, key: K, value: V) -> bool;

    /// Add one item to the map.
    ///
    /// Return `true` iff `key` had not been contained in this map before. In this
    /// case the value *is* updated.
    fn insert_or_replace(&mut self, key: K, value: V) -> bool;

    /// Remove one item from the map.
    ///
    /// Returns `true` if the item had been contained in the map, otherwise
    /// false.
    fn remove(&mut self, key: K) -> bool;

    /// Return a read-only reference to the element with the given key.
    fn get(&self, key: K) -> Option<&V>;

    /// Return a mutable reference to the element with the given key.
    fn get_mut(&mut self, key: K) -> Option<&mut V>;

    /// Return `true` iff item `u` is contained in this map.
    fn contains(&self, key: K) -> bool;
}

impl<'a, K, V, S> ItemMap<K, V> for &'a mut S
where
    K: Copy,
    S: ItemMap<K, V>,
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

    fn insert(&mut self, key: K, value: V) -> bool {
        (**self).insert(key, value)
    }

    fn insert_or_replace(&mut self, key: K, value: V) -> bool {
        (**self).insert_or_replace(key, value)
    }

    fn remove(&mut self, key: K) -> bool {
        (**self).remove(key)
    }

    fn get(&self, key: K) -> Option<&V> {
        (**self).get(key)
    }

    fn get_mut(&mut self, key: K) -> Option<&mut V> {
        (**self).get_mut(key)
    }

    fn contains(&self, key: K) -> bool {
        (**self).contains(key)
    }
}

impl<K, V, S> ItemMap<K, V> for HashMap<K, V, S>
where
    K: Copy + Eq + Hash,
    S: BuildHasher,
{
    fn is_empty(&self) -> bool {
        HashMap::is_empty(self)
    }

    fn len(&self) -> usize {
        HashMap::len(self)
    }

    fn clear(&mut self) {
        HashMap::clear(self)
    }

    fn insert(&mut self, key: K, value: V) -> bool {
        let mut new = false;
        HashMap::entry(self, key).or_insert_with(|| {
            new = true;
            value
        });
        new
    }

    fn insert_or_replace(&mut self, key: K, value: V) -> bool {
        HashMap::insert(self, key, value).is_some()
    }

    fn remove(&mut self, key: K) -> bool {
        HashMap::remove(self, &key).is_some()
    }

    fn get(&self, key: K) -> Option<&V> {
        HashMap::get(self, &key)
    }

    fn get_mut(&mut self, key: K) -> Option<&mut V> {
        HashMap::get_mut(self, &key)
    }

    fn contains(&self, key: K) -> bool {
        HashMap::contains_key(self, &key)
    }
}

pub struct NodeVecMap<'a, G, V> {
    graph: &'a G,
    data: Vec<Option<V>>,
    nitems: usize,
}

impl<'a, G, V> NodeVecMap<'a, G, V>
where
    G: IndexGraph<'a>,
    V: Clone,
{
    pub fn new(g: &'a G) -> Self {
        NodeVecMap {
            graph: g,
            data: vec![None; g.num_nodes()],
            nitems: 0,
        }
    }
}

impl<'a, G, V> ItemMap<G::Node, V> for NodeVecMap<'a, G, V>
where
    G: IndexGraph<'a>,
    V: Clone,
{
    fn is_empty(&self) -> bool {
        self.nitems == 0
    }

    fn len(&self) -> usize {
        self.nitems
    }

    fn clear(&mut self) {
        self.nitems = 0;
        self.data.fill(None)
    }

    fn insert(&mut self, key: G::Node, value: V) -> bool {
        let i = self.graph.node_id(key);
        if self.data[i].is_none() {
            self.data[i] = Some(value);
            true
        } else {
            false
        }
    }

    fn insert_or_replace(&mut self, key: G::Node, value: V) -> bool {
        self.data[self.graph.node_id(key)].replace(value).is_none()
    }

    fn remove(&mut self, key: G::Node) -> bool {
        self.data[self.graph.node_id(key)].take().is_some()
    }

    fn get(&self, key: G::Node) -> Option<&V> {
        self.data[self.graph.node_id(key)].as_ref()
    }

    fn get_mut(&mut self, key: G::Node) -> Option<&mut V> {
        self.data[self.graph.node_id(key)].as_mut()
    }

    fn contains(&self, key: G::Node) -> bool {
        self.data[self.graph.node_id(key)].is_some()
    }
}
