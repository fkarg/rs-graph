/*
 * Copyright (c) 2019 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! # Graph search algorithms.
//!
//! This module contains several standard search algorithms on graphs. These are
//! algorithms that visit the nodes of a graph in some specific order.
//!
//! All search algorithms are implemented as iterators. The iterators produce a
//! sequence of nodes (together with algorithm specific additional information)
//! in the order in which they are visited by the particular search strategy.
//! This allows search algorithms to be used on infinite graphs (represented by
//! implementors of [`Adjacencies`][crate::adjacencies::Adjacencies]), in which
//! case the iterator is infinite.

pub mod astar;
pub mod bfs;
pub mod biastar;
pub mod dfs;

use std::iter::Iterator;
use std::marker::PhantomData;

/// Compute a path from a map of incoming edges for each node.
///
/// # Parameters
/// - `dst`: the destination node
/// - `incomings(v)`: return the incoming edge and preceding node for node `v`
///   (or `None` if it does not exist)
///
/// # Return
/// An iterator over the incoming edges starting from the last one.
///
/// # Example
///
/// ```
/// // Breadth-first-search on a directed with 7 nodes.
///
/// use rs_graph::LinkedListGraph;
/// use rs_graph::traits::*;
/// use rs_graph::classes;
/// use rs_graph::search::{path_from_incomings, bfs};
/// use std::collections::{HashMap, VecDeque};
///
/// let g: LinkedListGraph = classes::cycle(7);
///
/// let mut incomings = HashMap::new();
/// let mut bfs = bfs::start_with_data(g.outgoing(), g.id2node(0), (&mut incomings, VecDeque::new()));
/// for _ in bfs {}
///
/// {
///     let mut path = path_from_incomings(g.id2node(3), |u| incomings.get(&u).map(|&e| (e, g.src(e))));
///
///     assert_eq!(path.next().map(|e| g.edge_id(e)), Some(2));
///     assert_eq!(path.next().map(|e| g.edge_id(e)), Some(1));
///     assert_eq!(path.next().map(|e| g.edge_id(e)), Some(0));
///     assert_eq!(path.next().map(|e| g.edge_id(e)), None);
/// }
///
/// {
///     let mut path = path_from_incomings(g.id2node(4), |u| incomings.get(&u).map(|&e| (e, g.src(e))));
///
///     assert_eq!(path.next().map(|e| g.edge_id(e)), Some(3));
///     assert_eq!(path.next().map(|e| g.edge_id(e)), Some(2));
///     assert_eq!(path.next().map(|e| g.edge_id(e)), Some(1));
///     assert_eq!(path.next().map(|e| g.edge_id(e)), Some(0));
///     assert_eq!(path.next().map(|e| g.edge_id(e)), None);
/// }
/// ```
pub fn path_from_incomings<N, E, I>(dst: N, incomings: I) -> impl Iterator<Item = E>
where
    N: Copy,
    E: Clone,
    I: Fn(N) -> Option<(E, N)>,
{
    PathIter {
        incomings,
        u: dst,
        phantom: PhantomData,
    }
}

#[doc(hidden)]
struct PathIter<N, E, I>
where
    I: Fn(N) -> Option<(E, N)>,
{
    incomings: I,
    u: N,
    phantom: PhantomData<E>,
}

impl<N, E, I> Iterator for PathIter<N, E, I>
where
    N: Clone,
    I: Fn(N) -> Option<(E, N)>,
{
    type Item = E;

    fn next(&mut self) -> Option<E> {
        if let Some((e, v)) = (self.incomings)(self.u.clone()) {
            self.u = v;
            Some(e)
        } else {
            None
        }
    }
}
