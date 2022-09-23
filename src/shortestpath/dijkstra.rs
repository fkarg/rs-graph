/*
 * Copyright (c) 2017, 2018, 2021, 2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! Dijkstra's shortest path algorithm.
//!
//! Dijkstra's algorithm computes the shortest path from some start node $s \in
//! V$ to all other nodes in (directed or undirected) graph. Each edge is
//! assigned a non-negative weight (or length) $w \colon E \to \mathbb{R}_+$.
//!
//! Dijkstra's algorithm is essentially an [A*-search][crate::search::astar]
//! using the zero potential (heuristic) for all nodes.
//!
//! # Example
//!
//! ```
//! use rs_graph::{LinkedListGraph, Builder, traits::*};
//! use rs_graph::adjacencies::Neighbors;
//! use rs_graph::shortestpath::dijkstra;
//! use rs_graph::string::from_ascii;
//!
//! let data = from_ascii::<LinkedListGraph>(r"
//!     a-----9-----b
//!    / \           \
//!   |   2           6
//!   |    \           \
//!  14     c-----8-----d
//!   |    / \         /
//!   |   9  10      15
//!    \ /     \     /
//!     e----7--f----
//! ").unwrap();
//! let g = data.graph;
//! let weights = data.weights;
//! let nodes = data.nodes;
//! let a = nodes[&'a'];
//! let b = nodes[&'b'];
//! let c = nodes[&'c'];
//! let d = nodes[&'d'];
//! let e = nodes[&'e'];
//! let f = nodes[&'f'];
//!
//! let mut preds: Vec<_> = dijkstra::start(&Neighbors(&g), e, |e| weights[e.index()])
//!     .map(|(u, e, d)| {
//!         let uv = g.enodes(e);
//!         if uv.0 == u { (uv.1, u, d) } else { (uv.0, u, d) }
//!     })
//!     .collect();
//!
//! assert_eq!(preds, vec![(e,f,7), (e,c,9), (c,a,11), (c,d,17), (a,b,20)]);
//!
//! let (path, dist) = dijkstra::find_undirected_path(&g, e, b, |e| weights[e.index()]).unwrap();
//!
//! assert_eq!(dist, 20);
//!
//! let path = path
//!     .into_iter()
//!     .map(|e| g.enodes(e))
//!     .map(|(u,v)| if g.node_id(u) < g.node_id(v) { (u,v) } else { (v,u) })
//!     .collect::<Vec<_>>();
//! assert_eq!(path, vec![(c,e), (a,c), (a,b)]);
//! ```

use crate::adjacencies::{Adjacencies, Neighbors, OutEdges};
use crate::collections::{ItemMap, ItemPriQueue};
use crate::search::astar::{
    self, AStar, AStarHeuristic, Accumulator, Data, DefaultMap, DefaultPriQueue, SumAccumulator,
};
use crate::traits::{Digraph, Graph};

use crate::num::traits::Zero;
use std::hash::Hash;
use std::ops::{Add, Neg, Sub};

/// Internal type used when no heuristic is required.
///
/// Used for standard Dijkstra.
#[derive(Clone, Copy, Default)]
pub struct NoHeur;

impl<N> AStarHeuristic<N> for NoHeur {
    type Result = NoHeur;

    fn call(&self, _u: N) -> NoHeur {
        NoHeur
    }
}

impl<T> Add<T> for NoHeur {
    type Output = T;
    fn add(self, x: T) -> T {
        x
    }
}

impl Neg for NoHeur {
    type Output = NoHeur;
    fn neg(self) -> Self {
        self
    }
}

/// Dijkstra search iterator.
pub type Dijkstra<'a, A, D, W, M, P, Accum> = AStar<'a, A, D, W, M, P, NoHeur, Accum>;

/// The Dijkstra-iterator with default types.
pub type DijkstraDefault<'a, A, D, W> =
    Dijkstra<'a, A, D, W, DefaultMap<'a, A, D, NoHeur>, DefaultPriQueue<'a, A, D, NoHeur>, SumAccumulator>;

/// Start and return an Dijkstra-iterator using default data structures.
///
/// This is a convenience wrapper around [`start_with_data`] using the default
/// data structures [`DefaultData`][crate::search::astar::DefaultData].
///
/// # Parameters
///
/// - `adj`: adjacency information for the graph
/// - `src`: the source node at which the search should start.
/// - `weights`: the weight function for each edge
pub fn start<'a, A, D, W>(adj: A, src: A::Node, weights: W) -> DijkstraDefault<'a, A, D, W>
where
    A: Adjacencies<'a>,
    A::Node: Hash,
    D: Copy + PartialOrd + Zero,
    W: Fn(A::Edge) -> D,
{
    start_with_data(adj, src, weights, astar::DefaultData::default())
}

/// Start and return an Dijkstra-iterator with custom data structures.
///
/// The returned iterator traverses the edges in the order of an Dijkstra-search. The
/// iterator returns the next node, its incoming edge and the distance to the
/// start node.
///
/// Note that the start node is *not* returned by the iterator.
///
/// The algorithm requires a pair `(M, P)` with `M` implementing [`ItemMap<Node,
/// Item>`][crate::collections::ItemMap], and `P` implementing
/// [`ItemPriQueue<Node, D>`][crate::collections::ItemStack] as internal data
/// structures. The map is used to store information about the last edge on a
/// shortest path for each reachable node. The priority queue is used the handle
/// the nodes in the correct order. The data structures can be reused for
/// multiple searches.
///
/// # Parameters
///
/// - `adj`: adjacency information for the graph
/// - `src`: the source node at which the search should start.
/// - `weights`: the weight function for each edge
/// - `data`: the custom data structures
pub fn start_with_data<'a, A, D, W, M, P>(
    adj: A,
    src: A::Node,
    weights: W,
    data: (M, P),
) -> Dijkstra<'a, A, D, W, M, P, SumAccumulator>
where
    A: Adjacencies<'a>,
    D: Copy + PartialOrd + Zero,
    W: Fn(A::Edge) -> D,
    M: ItemMap<A::Node, Option<P::Item>>,
    P: ItemPriQueue<A::Node, Data<A::Edge, D, NoHeur>>,
{
    start_generic(adj, src, weights, data)
}

/// Start and return an Dijkstra-iterator with a custom accumulator and custom
/// data structures.
///
/// This function differs from [`start_with_data`] in the additional type
/// parameter `Accum`. The type parameter is the accumulation function for
/// combining the length to the previous node with the weight of the current
/// edge. It is usually just the sum ([`SumAccumulator`]). One possible use is
/// the Prim's algorithm for the minimum spanning tree problem (see
/// [`mst::prim`](crate::mst::prim())).
pub fn start_generic<'a, A, D, W, M, P, Accum>(
    adj: A,
    src: A::Node,
    weights: W,
    data: (M, P),
) -> Dijkstra<'a, A, D, W, M, P, Accum>
where
    A: Adjacencies<'a>,
    D: Copy + PartialOrd + Zero,
    W: Fn(A::Edge) -> D,
    M: ItemMap<A::Node, Option<P::Item>>,
    P: ItemPriQueue<A::Node, Data<A::Edge, D, NoHeur>>,
    Accum: Accumulator<D>,
{
    astar::start_generic(adj, src, weights, NoHeur, data)
}

/// Start a Dijkstra-search on a undirected graph.
///
/// Each edge can be traversed in both directions with the same weight.
///
/// This is a convenience wrapper to start the search on an undirected graph
/// with the default data structures.
///
/// # Parameter
/// - `g`: the graph
/// - `weights`: the (non-negative) edge weights
/// - `src`: the source node
/// - `heur`: the lower bound heuristic
pub fn start_undirected<'a, G, D, W>(g: &'a G, src: G::Node, weights: W) -> DijkstraDefault<'a, Neighbors<'a, G>, D, W>
where
    G: Graph<'a>,
    G::Node: Hash,
    D: Copy + PartialOrd + Zero,
    W: Fn(G::Edge) -> D,
{
    start(Neighbors(g), src, weights)
}

/// Run a Dijkstra-search on an undirected graph and return the path.
///
/// Each edge can be traversed in both directions with the same weight.
///
/// This is a convenience wrapper to run the search on an undirected graph with
/// the default data structures and return the resulting path from `src` to
/// `snk`.
///
/// # Parameter
/// - `g`: the graph
/// - `weights`: the (non-negative) edge weights
/// - `src`: the source node
/// - `snk`: the sink node
///
/// The function returns the edges on the path and its length.
pub fn find_undirected_path<'a, G, D, W>(g: &'a G, src: G::Node, snk: G::Node, weights: W) -> Option<(Vec<G::Edge>, D)>
where
    G: Graph<'a>,
    G::Node: Hash,
    D: 'a + Copy + PartialOrd + Zero + Add<D, Output = D> + Sub<D, Output = D>,
    W: Fn(G::Edge) -> D,
{
    astar::find_undirected_path(g, src, snk, weights, NoHeur)
}

/// Start a Dijkstra-search on a directed graph.
///
/// This is a convenience wrapper to start the search on an directed graph
/// with the default data structures.
///
/// # Parameter
/// - `g`: the graph
/// - `weights`: the (non-negative) edge weights
/// - `src`: the source node
pub fn start_directed<'a, G, D, W>(g: &'a G, src: G::Node, weights: W) -> DijkstraDefault<'a, OutEdges<'a, G>, D, W>
where
    G: Digraph<'a>,
    G::Node: Hash,
    D: Copy + PartialOrd + Zero,
    W: Fn(G::Edge) -> D,
{
    start(OutEdges(g), src, weights)
}

/// Run a Dijkstra-search on a directed graph and return the path.
///
/// This is a convenience wrapper to run the search on an directed graph with
/// the default data structures and return the resulting path from `src` to
/// `snk`.
///
/// # Parameter
/// - `g`: the graph
/// - `weights`: the (non-negative) edge weights
/// - `src`: the source node
/// - `snk`: the sink node
///
/// The function returns the edges on the path and its length.
pub fn find_directed_path<'a, G, D, W>(g: &'a G, src: G::Node, snk: G::Node, weights: W) -> Option<(Vec<G::Edge>, D)>
where
    G: Digraph<'a>,
    G::Node: Hash,
    D: 'a + Copy + PartialOrd + Zero + Add<D, Output = D> + Sub<D, Output = D>,
    W: Fn(G::Edge) -> D,
{
    astar::find_directed_path(g, src, snk, weights, NoHeur)
}
