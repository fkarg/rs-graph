/*
 * Copyright (c) 2017, 2018, 2020, 2021 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! Depth-first-search.
//!
//! # Example
//!
//! ```
//! use rs_graph::LinkedListGraph;
//! use rs_graph::traits::*;
//! use rs_graph::classes;
//! use rs_graph::search::dfs;
//!
//! let g: LinkedListGraph = classes::peterson();
//! let mut cnt = 0;
//! for (u, e) in dfs::start(g.neighbors(), g.id2node(0)) {
//!     assert_ne!(g.node_id(u), 0);
//!     cnt += 1;
//! }
//! assert_eq!(cnt, g.num_nodes() - 1);
//! ```

use crate::adjacencies::Adjacencies;
use crate::collections::{ItemMap, ItemStack};
use crate::traits::{GraphIterator, GraphType};
use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;

/// DFS iterator with default data structures.
pub type DFSDefault<'a, A> = DFS<
    'a,
    A,
    HashMap<<A as GraphType<'a>>::Node, <A as GraphType<'a>>::Edge>,
    Vec<<A as Adjacencies<'a>>::IncidenceIt>,
>;

pub type DefaultData<N, E, I> = (HashMap<N, E>, Vec<I>);

/// Start and return a DFS iterator using default data structures.
///
/// This is a convenience wrapper around [`start_with_data`] using the default
/// data structures [`DefaultData`].
///
/// # Parameter
/// - `adj`: adjacency information for the graph
/// - `src`: the source node at which the search should start.
pub fn start<'a, A>(adj: A, src: A::Node) -> DFSDefault<'a, A>
where
    A: Adjacencies<'a>,
    A::Node: Hash,
{
    start_with_data(adj, src, DefaultData::default())
}

/// Start and return a DFS iterator with user defined data structures.
///
/// The returned iterator traverses the edges in depth-first order. The
/// iterator returns the next node and its incoming edge.
///
/// Note that the start node is *not* returned by the iterator.
///
/// The algorithm requires a pair `(M, S)` with `M` implementing [`ItemMap<Node,
/// Edge>`][crate::collections::ItemMap], and `S` implementing
/// [`ItemStack<_>`][crate::collections::ItemStack] as internal data
/// structures. The map is used to store the last edge of the path from the
/// source to each reachable node. The stack is used to handle the nodes in
/// depth-first order. The data structures can be reused for multiple
/// searches.
///
/// # Parameter
/// - `adj`: adjacency information for the graph
/// - `src`: the source node at which the search should start.
/// - `data`: the data structures used in the algorithm
///
/// # Example
///
/// ```
/// use rs_graph::LinkedListGraph;
/// use rs_graph::traits::*;
/// use rs_graph::classes;
/// use rs_graph::search::dfs;
/// use std::collections::HashMap;
///
/// let g: LinkedListGraph = classes::peterson();
/// let mut cnt = 0;
/// for (u, e) in dfs::start_with_data(g.neighbors(), g.id2node(0),
///                                    (HashMap::new(), Vec::new()))
/// {
///     assert_ne!(g.node_id(u), 0);
///     cnt += 1;
/// }
/// assert_eq!(cnt, g.num_nodes() - 1);
/// ```
pub fn start_with_data<'a, A, S, St>(adj: A, src: A::Node, data: (S, St)) -> DFS<'a, A, S, St>
where
    A: Adjacencies<'a>,
    S: ItemMap<A::Node, A::Edge>,
    St: ItemStack<A::IncidenceIt>,
{
    let (mut seen, mut stack) = data;
    seen.clear();
    stack.clear();

    stack.push(adj.neigh_iter(src));

    DFS {
        adj,
        src,
        seen,
        stack,
        phantom: PhantomData,
    }
}

pub struct DFS<'a, A, S, St>
where
    A: Adjacencies<'a>,
    S: ItemMap<A::Node, A::Edge>,
    St: ItemStack<A::IncidenceIt>,
{
    adj: A,
    src: A::Node,
    seen: S,
    stack: St,
    phantom: PhantomData<&'a ()>,
}

impl<'a, A, S, St> Iterator for DFS<'a, A, S, St>
where
    A: Adjacencies<'a>,
    S: ItemMap<A::Node, A::Edge>,
    St: ItemStack<A::IncidenceIt>,
{
    type Item = (A::Node, A::Edge);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut it) = self.stack.pop() {
            if let Some((e, v)) = it.next(&self.adj) {
                self.stack.push(it);
                if v != self.src && self.seen.insert(v, e) {
                    self.stack.push(self.adj.neigh_iter(v));
                    return Some((v, e));
                }
            }
        }
        None
    }
}

impl<'a, A, S, St> DFS<'a, A, S, St>
where
    A: Adjacencies<'a>,
    S: ItemMap<A::Node, A::Edge>,
    St: ItemStack<A::IncidenceIt>,
{
    /// Run the dfs completely.
    ///
    /// Note that this method may run forever on an infinite graph.
    pub fn run(&mut self) {
        while self.next().is_some() {}
    }

    /// Return the data structures used in the search.
    pub fn into_data(self) -> (S, St) {
        (self.seen, self.stack)
    }

    /// Return the incoming edge of a node.
    pub fn incoming_edge(&self, u: A::Node) -> Option<A::Edge> {
        self.seen.get(u).cloned()
    }
}
