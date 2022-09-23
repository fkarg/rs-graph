// Copyright (c) 2016, 2017, 2018, 2021, 2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

#![allow(clippy::type_complexity)]

//! Dijkstra's bidirectional shortest path algorithm.
//!
//! The bidirectional Dijkstra algorithm starts the search at the start and the
//! end node simultaneously. The shortest path is found if the two searches
//! meet.
//!
//! This is actually a [bidirectional A*-search][crate::search::biastar] with
//! the all zero node potential.
//!
//! # Example
//!
//! ```
//! use rs_graph::{LinkedListGraph, Builder, traits::*};
//! use rs_graph::adjacencies::Neighbors;
//! use rs_graph::shortestpath::bidijkstra;
//! use rs_graph::string::from_ascii;
//!
//! let data = from_ascii::<LinkedListGraph>(r"
//!     a-----9-----b
//!    / \           \
//!   |   2           6
//!   |    \           \
//!  14     c-----8-----d
//!   |    / \         /
//!   |  10  12      15
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
//! // ensure that the nodes are visited in the correct order
//! let visited = bidijkstra::start(&Neighbors(&g), &Neighbors(&g), e, b, |e| weights[e.index()])
//!     .map(|(u, _ , d)| (u, d))
//!     .collect::<Vec<_>>();
//! assert_eq!(visited, vec![(d, 6), (f, 7), (a, 9), (c, 10), (a, 12)]);
//!
//! // obtain the shortest path directly.
//! let (path, dist) = bidijkstra::find_undirected_path(&g, e, b, |e| weights[e.index()]).unwrap();
//!
//! assert_eq!(dist, 21);
//!
//! let path = path.into_iter()
//!     .map(|e| g.enodes(e))
//!     .map(|(u,v)| if g.node_id(u) > g.node_id(v) { (v,u) } else { (u,v) })
//!     .collect::<Vec<_>>();
//! assert_eq!(path, vec![(c,e), (a,c), (a,b)]);
//! ```

use crate::adjacencies::{Adjacencies, InEdges, Neighbors, OutEdges};
use crate::collections::{ItemMap, ItemPriQueue};
use crate::search::biastar::{self, BiAStar, BiData, DefaultMap, DefaultPriQueue, Direction};
pub use crate::shortestpath::dijkstra::NoHeur;
use crate::traits::{Digraph, Graph};

use either::Either;
use num_traits::Zero;
use std::hash::Hash;
use std::ops::{Add, Sub};

/// Bi-Dijkstra search iterator.
pub type BiDijkstra<'a, Aout, Ain, D, W, M, P> = BiAStar<'a, Aout, Ain, D, W, M, P, NoHeur>;

/// Bi-Dijkstra search iterator with default data structures.
pub type BiDijkstraDefault<'a, Aout, Ain, D, W> =
    BiDijkstra<'a, Aout, Ain, D, W, DefaultMap<'a, Aout, D, NoHeur>, DefaultPriQueue<'a, Aout, D, NoHeur>>;

/// Compute a shortest path with bidirectional Dijkstra algorithm using default data structures.
///
/// This is a convenience wrapper around [`start_with_data`] using the default
/// data structures returned by
/// [`DefaultData`][crate::search::biastar::DefaultData].
///
/// # Parameters
/// - `adjout`: adjacency information for the forward search (i.e outgoing edges)
/// - `adjin`: adjacency information for the backward search (i.e incoming edges)
/// - `src`: the source node at which the path should start.
/// - `snk`: the snk node at which the path should end.
/// - `weights`: the (non-negative) weight function for each edge
pub fn start<'a, Aout, Ain, D, W>(
    adjout: Aout,
    adjin: Ain,
    src: Aout::Node,
    snk: Aout::Node,
    weights: W,
) -> BiDijkstraDefault<'a, Aout, Ain, D, W>
where
    Aout: Adjacencies<'a>,
    Aout::Node: Hash,
    Ain: Adjacencies<'a, Node = Aout::Node, Edge = Aout::Edge>,
    D: Copy + PartialOrd + Zero,
    W: Fn(Aout::Edge) -> D,
{
    start_with_data(adjout, adjin, src, snk, weights, biastar::DefaultData::default())
}

/// Run bidirectional Dijkstra on a generic graph with custom data structures.
///
/// The returned iterator traverses the edges in the order of a bidirectional
/// Dijkstra-search. The iterator returns the next node, its incoming edge with
/// direction information and the distance to the start node or end node
/// depending on the direction.
///
/// Note that the start and end nodes are *not* returned by the iterator.
///
/// The algorithm requires a pair `(M, P)` with `M` implementing
/// [`ItemMap<Direction<Node>, Item>`][crate::collections::ItemMap], and `P`
/// implementing [`ItemPriQueue<Direction<Node>,
/// D>`][crate::collections::ItemStack] as internal data structures. The map is
/// used to store information about the last edge on a shortest path for each
/// reachable node. The priority queue is used the handle the nodes in the
/// correct order. The data structures can be reused for multiple searches.
///
/// # Parameters
/// - `adjout`: adjacency information for the forward search (i.e outgoing edges)
/// - `adjin`: adjacency information for the backward search (i.e incoming edges)
/// - `src`: the source node at which the path should start.
/// - `snk`: the snk node at which the path should end.
/// - `weights`: the (non-negative) weight function for each edge
/// - `heur`: the heuristic used in the search
/// - `data`: the data structures
pub fn start_with_data<'a, Aout, Ain, D, W, M, P>(
    adjout: Aout,
    adjin: Ain,
    src: Aout::Node,
    snk: Aout::Node,
    weights: W,
    data: (M, P),
) -> BiDijkstra<'a, Aout, Ain, D, W, M, P>
where
    Aout: Adjacencies<'a>,
    Ain: Adjacencies<'a, Node = Aout::Node, Edge = Aout::Edge>,
    D: Copy + PartialOrd + Zero,
    W: Fn(Aout::Edge) -> D,
    M: ItemMap<Direction<Aout::Node>, Either<P::Item, D>>,
    P: ItemPriQueue<Direction<Aout::Node>, BiData<Aout::Edge, D, NoHeur>>,
{
    biastar::start_with_data(adjout, adjin, src, snk, weights, NoHeur, data)
}

/// Start a bidirectional Dijkstra-search on an undirected graph.
///
/// Each edge can be traversed in both directions with the same weight.
///
/// This is a convenience wrapper to start the search on an undirected graph
/// with the default data structures.
///
/// # Parameters
///
/// - `g`: the undirected graph
/// - `src`: the source node at which the path should start.
/// - `snk`: the snk node at which the path should end.
/// - `weights`: the weight function for each edge
pub fn start_undirected<'a, G, D, W>(
    g: &'a G,
    src: G::Node,
    snk: G::Node,
    weights: W,
) -> BiDijkstraDefault<'a, Neighbors<'a, G>, Neighbors<'a, G>, D, W>
where
    G: Graph<'a>,
    G::Node: Hash,
    D: Copy + PartialOrd + Zero,
    W: Fn(G::Edge) -> D,
{
    start(Neighbors(g), Neighbors(g), src, snk, weights)
}

/// Run a bidirectional Dijkstra-search on an undirected graph and return the path.
///
/// Each edge can be traversed in both directions with the same weight.
///
/// This is a convenience wrapper to run the search on an undirected graph
/// with the default data structures and obtain the shortest path.
///
/// # Parameters
///
/// - `g`: the undirected graph
/// - `src`: the source node at which the path should start.
/// - `snk`: the snk node at which the path should end.
/// - `weights`: the weight function for each edge
///
/// The function returns the edges on the path and its length.
pub fn find_undirected_path<'a, G, D, W>(g: &'a G, src: G::Node, snk: G::Node, weights: W) -> Option<(Vec<G::Edge>, D)>
where
    G: Graph<'a>,
    G::Node: Hash,
    D: Copy + PartialOrd + Zero + Add<D, Output = D> + Sub<D, Output = D>,
    W: Fn(G::Edge) -> D,
{
    biastar::find_undirected_path(g, src, snk, weights, NoHeur)
}

/// Start a bidirectional Dijkstra-search on a directed graph.
///
/// This is a convenience wrapper to start the search on an directed graph
/// with the default data structures.
///
/// # Parameters
///
/// - `g`: the directed graph
/// - `src`: the source node at which the path should start.
/// - `snk`: the snk node at which the path should end.
/// - `weights`: the weight function for each edge
/// - `heur`: the heuristic used in the search
pub fn start_directed<'a, G, D, W>(
    g: &'a G,
    src: G::Node,
    snk: G::Node,
    weights: W,
) -> BiDijkstraDefault<'a, OutEdges<'a, G>, InEdges<'a, G>, D, W>
where
    G: Digraph<'a>,
    G::Node: Hash,
    D: Copy + PartialOrd + Zero,
    W: Fn(G::Edge) -> D,
{
    start(OutEdges(g), InEdges(g), src, snk, weights)
}

/// Run a bidirectional Dijkstra-search on an directed graph and return the path.
///
/// This is a convenience wrapper to run the search on an directed graph
/// with the default data structures and obtain the shortest path.
///
/// # Parameters
///
/// - `g`: the directed graph
/// - `src`: the source node at which the path should start.
/// - `snk`: the snk node at which the path should end.
/// - `weights`: the weight function for each edge
///
/// The function returns the edges on the path and its length.
pub fn find_directed_path<'a, G, D, W>(g: &'a G, src: G::Node, snk: G::Node, weights: W) -> Option<(Vec<G::Edge>, D)>
where
    G: Digraph<'a>,
    G::Node: Hash,
    D: Copy + PartialOrd + Zero + Add<D, Output = D> + Sub<D, Output = D>,
    W: Fn(G::Edge) -> D,
{
    biastar::find_directed_path(g, src, snk, weights, NoHeur)
}
