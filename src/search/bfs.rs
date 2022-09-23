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

//! Breadth-first-search.
//!
//! # Example
//!
//! ```
//! use rs_graph::LinkedListGraph;
//! use rs_graph::traits::*;
//! use rs_graph::classes;
//! use rs_graph::search::bfs;
//!
//! let g: LinkedListGraph = classes::peterson();
//! let mut cnt = 0;
//! for (u, e) in bfs::start(g.neighbors(), g.id2node(0)) {
//!     assert_ne!(g.node_id(u), 0);
//!     cnt += 1;
//! }
//! assert_eq!(cnt, g.num_nodes() - 1);
//! ```

use crate::adjacencies::Adjacencies;
use crate::collections::{ItemMap, ItemQueue};
use crate::traits::{GraphIterator, GraphType};
use std::collections::{HashMap, VecDeque};
use std::hash::Hash;

/// BFS iterator with default data structures.
pub type BFSDefault<'a, A> =
    BFS<'a, A, HashMap<<A as GraphType<'a>>::Node, <A as GraphType<'a>>::Edge>, VecDeque<<A as GraphType<'a>>::Node>>;

/// The default data structures for BFS.
pub type DefaultData<N, E> = (HashMap<N, E>, VecDeque<N>);

/// Start and return a BFS iterator using default data structures.
///
/// This is a convenience wrapper around [`start_with_data`] using the default
/// data structures [`DefaultData`].
///
/// # Parameter
/// - `adj`: adjacency information for the graph
/// - `src`: the source node at which the search should start.
pub fn start<'a, A>(adj: A, src: A::Node) -> BFSDefault<'a, A>
where
    A: Adjacencies<'a>,
    A::Node: Hash,
{
    start_with_data(adj, src, DefaultData::default())
}

/// Start and return a BFS iterator with user defined data structures.
///
/// The returned iterator traverses the edges in breadth-first order. The
/// iterator returns the next node and its incoming edge.
///
/// Note that the start node is *not* returned by the iterator.
///
/// The algorithm requires a pair `(M, Q)` with `M` implementing [`ItemMap<Node,
/// Edge>`][crate::collections::ItemMap], and `Q` implementing
/// [`ItemQueue<Node>`][crate::collections::ItemQueue] as internal data
/// structures. The map is used to store the last edge of the path from the
/// source to each reachable node. The queue is used to handle the nodes in
/// breadth-first order. The data structures can be reused for multiple
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
/// use rs_graph::search::bfs;
/// use std::collections::{HashMap, VecDeque};
///
/// let g: LinkedListGraph = classes::peterson();
/// let mut cnt = 0;
/// for (u, e) in bfs::start_with_data(g.neighbors(), g.id2node(0),
///                                    (HashMap::new(), VecDeque::new()))
/// {
///     assert_ne!(g.node_id(u), 0);
///     cnt += 1;
/// }
/// assert_eq!(cnt, g.num_nodes() - 1);
/// ```
pub fn start_with_data<'a, A, S, Q>(adj: A, src: A::Node, data: (S, Q)) -> BFS<'a, A, S, Q>
where
    A: Adjacencies<'a>,
    S: ItemMap<A::Node, A::Edge>,
    Q: ItemQueue<A::Node>,
{
    let (mut seen, mut queue) = data;
    queue.clear();
    seen.clear();
    let it = adj.neigh_iter(src);

    BFS {
        adj,
        src,
        seen,
        queue,
        it,
    }
}

/// The BFS iterator.
pub struct BFS<'a, A, S, Q>
where
    A: Adjacencies<'a>,
    S: ItemMap<A::Node, A::Edge>,
    Q: ItemQueue<A::Node>,
{
    adj: A,
    src: A::Node,
    seen: S,
    queue: Q,
    it: A::IncidenceIt,
}

impl<'a, A, S, Q> Iterator for BFS<'a, A, S, Q>
where
    A: Adjacencies<'a>,
    S: ItemMap<A::Node, A::Edge>,
    Q: ItemQueue<A::Node>,
{
    type Item = (A::Node, A::Edge);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            while let Some((e, v)) = self.it.next(&self.adj) {
                if v != self.src && self.seen.insert(v, e) {
                    self.queue.push(v);
                    return Some((v, e));
                }
            }
            if let Some(u) = self.queue.pop() {
                self.it = self.adj.neigh_iter(u);
            } else {
                return None;
            }
        }
    }
}

impl<'a, A, S, Q> BFS<'a, A, S, Q>
where
    A: Adjacencies<'a>,
    S: ItemMap<A::Node, A::Edge>,
    Q: ItemQueue<A::Node>,
{
    /// Run the bfs completely.
    ///
    /// Note that this method may run forever on an infinite graph.
    pub fn run(&mut self) {
        while self.next().is_some() {}
    }

    /// Return the data structures used in the search.
    pub fn into_data(self) -> (S, Q) {
        (self.seen, self.queue)
    }

    /// Return the incoming edge of a node.
    pub fn incoming_edge(&self, u: A::Node) -> Option<A::Edge> {
        self.seen.get(u).cloned()
    }
}
