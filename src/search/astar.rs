/*
 * Copyright (c) 2018, 2021 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! A* search.
//!
//! This module implements an A*-search for finding a shortest paths
//! from some node to all other nodes. Each node may be assigned a
//! potential (or "heuristic value") estimating the distance to the target
//! node. The potential $h\colon V \to \mathbb{R}$ must satisfy
//! \\[ w(u,v) - h(u) + h(v) \ge 0, (u,v) \in E \\]
//! where $w\colon E \to \mathbb{R}$ are the weights (or lengths) of the edges.
//! (The relation must hold for both directions in case the graph is
//! undirected).
//!
//! If $s \in V$ is the start node and $t$ some destination node, then
//! $h(u) - h(t)$ is a lower bound on the distance from $u$ to $t$ for all nodes $u \in V$.
//! Hence, f the shortest path to some specific destination node $t$ should be
//! found the canonical choice for $h$ is such that $h(t) = 0$ and $h(u)$ is a
//! lower bound on the distance from $u$ to $t$.
//!
//! # Example
//!
//! ```
//! use rs_graph::traits::*;
//! use rs_graph::search::astar;
//! use rs_graph::string::{from_ascii, Data};
//! use rs_graph::LinkedListGraph;
//!
//! let Data {
//!     graph: g,
//!     weights,
//!     nodes,
//! } = from_ascii::<LinkedListGraph>(
//!     r"
//!     *--1--*--1--*--1--*--1--*--1--*--1--*--1--*
//!     |     |     |     |     |     |     |     |
//!     1     1     1     1     1     1     1     1
//!     |     |     |     |     |     |     |     |
//!     *--1--*--2--*--1--*--2--e--1--f--1--t--1--*
//!     |     |     |     |     |     |     |     |
//!     1     1     1     1     1     2     1     1
//!     |     |     |     |     |     |     |     |
//!     *--1--*--1--*--2--c--1--d--1--*--2--*--1--*
//!     |     |     |     |     |     |     |     |
//!     1     1     1     1     1     1     1     1
//!     |     |     |     |     |     |     |     |
//!     *--1--s--1--a--1--b--2--*--1--*--1--*--1--*
//!     |     |     |     |     |     |     |     |
//!     1     1     1     1     1     1     1     1
//!     |     |     |     |     |     |     |     |
//!     *--1--*--1--*--1--*--1--*--1--*--1--*--1--*
//!     ",
//! )
//! .unwrap();
//!
//! let s = nodes[&'s'];
//! let t = nodes[&'t'];
//!
//! // nodes are numbered row-wise -> get node coordinates
//! let coords = |u| ((g.node_id(u) % 8) as isize, (g.node_id(u) / 8) as isize);
//!
//! let (xs, ys) = coords(s);
//! let (xt, yt) = coords(t);
//!
//! // manhatten distance heuristic
//! let manh_heur = |u| {
//!     let (x, y) = coords(u);
//!     ((x - xt).abs() + (y - yt).abs()) as usize
//! };
//!
//! // verify that we do not go in the "wrong" direction
//! for (v, _, _) in astar::start(g.neighbors(), s, |e| weights[e.index()], manh_heur) {
//!     let (x, y) = coords(v);
//!     assert!(x >= xs && x <= xt && y >= yt && y <= ys);
//!     if v == t {
//!         break;
//!     }
//! }
//!
//! // obtain the shortest path directly
//! let (path, dist) = astar::find_undirected_path(&g, s, t, |e| weights[e.index()], manh_heur).unwrap();
//!
//! assert_eq!(dist, 7);
//!
//! let mut pathnodes = vec![s];
//! for e in path {
//!     let uv = g.enodes(e);
//!     if uv.0 == *pathnodes.last().unwrap() {
//!         pathnodes.push(uv.1);
//!     } else {
//!         pathnodes.push(uv.0);
//!     }
//! }
//! assert_eq!(pathnodes, "sabcdeft".chars().map(|c| nodes[&c]).collect::<Vec<_>>());
//! ```

use crate::adjacencies::{Adjacencies, Neighbors, OutEdges};
use crate::collections::BinHeap;
use crate::collections::{ItemMap, ItemPriQueue};
use crate::search::path_from_incomings;
use crate::traits::{Digraph, Graph, GraphType};

use num_traits::Zero;

use std::cmp::Ordering;
use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::{Add, Sub};

/// A* search iterator.
pub struct AStar<'a, A, D, W, M, P, H, Accum>
where
    A: Adjacencies<'a>,
    M: ItemMap<A::Node, Option<P::Item>>,
    P: ItemPriQueue<A::Node, Data<A::Edge, D, H::Result>>,
    D: Copy,
    W: Fn(A::Edge) -> D,
    H: AStarHeuristic<A::Node>,
    H::Result: Copy,
    Accum: Accumulator<D>,
{
    adj: A,
    nodes: M,
    pqueue: P,
    weights: W,
    heur: H,
    phantom: PhantomData<&'a (D, Accum)>,
}

/// The data stored with an edge during the search.
#[derive(Clone)]
pub struct Data<E, D, H> {
    /// incoming edge on currently best path
    pub incoming_edge: E,
    /// currently best known distance
    pub distance: D,
    /// the lower bound of this node
    lower: H,
}

impl<E, D, H> PartialEq for Data<E, D, H>
where
    D: PartialEq,
{
    fn eq(&self, data: &Self) -> bool {
        self.distance.eq(&data.distance)
    }
}

impl<E, D, H> PartialOrd for Data<E, D, H>
where
    D: PartialOrd + Clone,
    H: Add<D, Output = D> + Clone,
{
    fn partial_cmp(&self, data: &Self) -> Option<Ordering> {
        (self.lower.clone() + self.distance.clone()).partial_cmp(&(data.lower.clone() + data.distance.clone()))
    }
}

/// A heuristic providing a node potential.
///
/// The node potential must satisfy that $w(u,v) - h(u) + h(v) \ge 0$ for all
/// edges $(u,v) \in E$. This means that $h(u) - h(t)$ must be a lower bound for
/// the distance from $u$ to the destination node $t$. Usually one chooses $h(t)
/// = 0$ for the destination node $t$.
pub trait AStarHeuristic<N> {
    type Result: Copy + Default;

    fn call(&self, u: N) -> Self::Result;
}

impl<F, N, H> AStarHeuristic<N> for F
where
    F: Fn(N) -> H,
    H: Copy + Default,
{
    type Result = H;

    fn call(&self, u: N) -> H {
        (*self)(u)
    }
}

/// A binary operation used to accumulate edge weight and distance.
///
/// The default operation for Dijkstra's algorithm is the sum, for Prim's
/// algorithm it is simply the edge weight ignoring the "distance".
pub trait Accumulator<T> {
    fn accum(dist: T, weight: T) -> T;
}

/// Accumulates by adding distance and weight.
pub struct SumAccumulator;

impl<T> Accumulator<T> for SumAccumulator
where
    T: Add<Output = T>,
{
    fn accum(dist: T, weight: T) -> T {
        dist + weight
    }
}

/// Default map type to be used in an A* search.
///
/// - `A` is the graph type information
/// - `D` is the type of distance values
/// - `H` is the type of heuristic values
pub type DefaultMap<'a, A, D, H> = HashMap<
    <A as GraphType<'a>>::Node,
    Option<
        <BinHeap<<A as GraphType<'a>>::Node, Data<<A as GraphType<'a>>::Edge, D, H>> as ItemPriQueue<
            <A as GraphType<'a>>::Node,
            Data<<A as GraphType<'a>>::Edge, D, H>,
        >>::Item,
    >,
>;

/// Default priority queue type to be used in an A* search.
///
/// - `A` is the graph type information
/// - `D` is the type of distance values
/// - `H` is the type of heuristic values
pub type DefaultPriQueue<'a, A, D, H> = BinHeap<<A as GraphType<'a>>::Node, Data<<A as GraphType<'a>>::Edge, D, H>>;

/// The default data structures to be used in an A* search.
pub type DefaultData<ID, N, I, D> = (HashMap<N, I>, BinHeap<N, D, ID>);

/// The A*-iterator with default types.
pub type AStarDefault<'a, A, D, W, H> = AStar<
    'a,
    A,
    D,
    W,
    DefaultMap<'a, A, D, <H as AStarHeuristic<<A as GraphType<'a>>::Node>>::Result>,
    DefaultPriQueue<'a, A, D, <H as AStarHeuristic<<A as GraphType<'a>>::Node>>::Result>,
    H,
    SumAccumulator,
>;

/// Start and return an A*-iterator using default data structures.
///
/// This is a convenience wrapper around [`start_with_data`] using the default
/// data structures [`DefaultData`].
///
/// # Parameter
/// - `adj`: adjacency information for the graph
/// - `src`: the source node at which the search should start.
/// - `weights`: the weight function for each edge
/// - `heur`: the heuristic used in the search
pub fn start<'a, A, D, W, H>(adj: A, src: A::Node, weights: W, heur: H) -> AStarDefault<'a, A, D, W, H>
where
    A: Adjacencies<'a>,
    A::Node: Hash,
    D: Copy + PartialOrd + Zero,
    W: Fn(A::Edge) -> D,
    H: AStarHeuristic<A::Node>,
    H::Result: Add<D, Output = D>,
{
    start_with_data(adj, src, weights, heur, DefaultData::default())
}

/// Start and return an A*-iterator with custom data structures.
///
/// The returned iterator traverses the edges in the order of an A*-search. The
/// iterator returns the next node, its incoming edge and the distance to the
/// start node.
///
/// The heuristic is a assigning a potential to each node. The potential of all
/// nodes must be so that $w(u,v) - h(u) + h(v) \ge 0$ for all edges $(u,v) \in
/// E$. If $t$ is the destination node of the path then $h(u) - h(t)$ is a lower
/// bound on the distance from $u$ to $t$ for each node $u \in V$ (in this case
/// one usually chooses $h(t) = 0$). The value returned by the heuristic must be
/// compatible with the distance type, i.e., is must be possible to compute the
/// sum of both.
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
/// This function uses the default data structures [`DefaultData`].
///
/// # Parameter
/// - `adj`: adjacency information for the graph
/// - `src`: the source node at which the search should start.
/// - `weights`: the weight function for each edge
/// - `heur`: the heuristic used in the search
/// - `data`: the custom data structures
pub fn start_with_data<'a, A, D, W, H, M, P>(
    adj: A,
    src: A::Node,
    weights: W,
    heur: H,
    data: (M, P),
) -> AStar<'a, A, D, W, M, P, H, SumAccumulator>
where
    A: Adjacencies<'a>,
    D: Copy + PartialOrd + Zero,
    W: Fn(A::Edge) -> D,
    H: AStarHeuristic<A::Node>,
    H::Result: Add<D, Output = D>,
    M: ItemMap<A::Node, Option<P::Item>>,
    P: ItemPriQueue<A::Node, Data<A::Edge, D, H::Result>>,
{
    start_generic(adj, src, weights, heur, data)
}

/// Start and return an A*-iterator with a custom accumulator and custom data structures.
///
/// This function differs from [`start_with_data`] in the additional type
/// parameter `Accum`. The type parameter is the accumulation function for
/// combining the length to the previous node with the weight of the current
/// edge. It is usually just the sum ([`SumAccumulator`]). One possible use is
/// the Prim's algorithm for the minimum spanning tree problem (see
/// [`mst::prim`](crate::mst::prim())).
pub fn start_generic<'a, A, D, W, H, Accum, M, P>(
    adj: A,
    src: A::Node,
    weights: W,
    heur: H,
    data: (M, P),
) -> AStar<'a, A, D, W, M, P, H, Accum>
where
    A: Adjacencies<'a>,
    D: Copy + PartialOrd + PartialOrd + Zero,
    W: Fn(A::Edge) -> D,
    H: AStarHeuristic<A::Node>,
    H::Result: Add<D, Output = D>,
    M: ItemMap<A::Node, Option<P::Item>>,
    P: ItemPriQueue<A::Node, Data<A::Edge, D, H::Result>>,
    Accum: Accumulator<D>,
{
    let (mut nodes, mut pqueue) = data;
    pqueue.clear();
    nodes.clear();
    nodes.insert(src, None);

    // insert neighbors of source
    for (e, v) in adj.neighs(src) {
        let dist = Accum::accum(D::zero(), (weights)(e));
        match nodes.get_mut(v) {
            Some(Some(vitem)) => {
                // node is known but unhandled
                let (olddist, lower) = {
                    let data = pqueue.value(vitem);
                    (data.distance, data.lower)
                };
                if dist < olddist {
                    pqueue.decrease_key(
                        vitem,
                        Data {
                            incoming_edge: e,
                            distance: dist,
                            lower,
                        },
                    );
                }
            }
            None => {
                // node is unknown
                let item = pqueue.push(
                    v,
                    Data {
                        incoming_edge: e,
                        distance: dist,
                        lower: heur.call(v),
                    },
                );
                nodes.insert(v, Some(item));
            }
            _ => (), // node has been handled
        };
    }

    AStar {
        adj,
        nodes,
        pqueue,
        weights,
        heur,
        phantom: PhantomData,
    }
}

impl<'a, A, D, W, M, P, H, Accum> Iterator for AStar<'a, A, D, W, M, P, H, Accum>
where
    A: Adjacencies<'a>,
    D: Copy + PartialOrd + Add<D, Output = D> + Sub<D, Output = D>,
    W: Fn(A::Edge) -> D,
    M: ItemMap<A::Node, Option<P::Item>>,
    P: ItemPriQueue<A::Node, Data<A::Edge, D, H::Result>>,
    H: AStarHeuristic<A::Node>,
    H::Result: Add<D, Output = D>,
    Accum: Accumulator<D>,
{
    type Item = (A::Node, A::Edge, D);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((u, data)) = self.pqueue.pop_min() {
            // node is not in the queue anymore, forget its item
            self.nodes.insert_or_replace(u, None);
            let (d, incoming_edge) = (data.distance, data.incoming_edge);
            for (e, v) in self.adj.neighs(u) {
                let dist = Accum::accum(d, (self.weights)(e));
                match self.nodes.get_mut(v) {
                    Some(Some(vitem)) => {
                        // node is known but unhandled
                        let (olddist, lower) = {
                            let data = self.pqueue.value(vitem);
                            (data.distance, data.lower)
                        };
                        if dist < olddist {
                            self.pqueue.decrease_key(
                                vitem,
                                Data {
                                    incoming_edge: e,
                                    distance: dist,
                                    lower,
                                },
                            );
                        }
                    }
                    None => {
                        // node is unknown
                        let item = self.pqueue.push(
                            v,
                            Data {
                                incoming_edge: e,
                                distance: dist,
                                lower: self.heur.call(v),
                            },
                        );
                        self.nodes.insert(v, Some(item));
                    }
                    _ => (), // node has been handled
                };
            }
            Some((u, incoming_edge, d))
        } else {
            None
        }
    }
}

impl<'a, A, D, W, M, P, H, Accum> AStar<'a, A, D, W, M, P, H, Accum>
where
    A: Adjacencies<'a>,
    D: Copy + PartialOrd + Add<D, Output = D> + Sub<D, Output = D>,
    W: Fn(A::Edge) -> D,
    M: ItemMap<A::Node, Option<P::Item>>,
    P: ItemPriQueue<A::Node, Data<A::Edge, D, H::Result>>,
    H: AStarHeuristic<A::Node>,
    H::Result: Add<D, Output = D>,
    Accum: Accumulator<D>,
{
    /// Run the search completely.
    ///
    /// Note that this method may run forever on an infinite graph.
    pub fn run(&mut self) {
        while self.next().is_some() {}
    }

    /// Return the data structures used during the algorithm
    pub fn into_data(self) -> (M, P) {
        (self.nodes, self.pqueue)
    }
}

/// Start an A*-search on a undirected graph.
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
pub fn start_undirected<'a, G, D, W, H>(
    g: &'a G,
    src: G::Node,
    weights: W,
    heur: H,
) -> AStarDefault<'a, Neighbors<'a, G>, D, W, H>
where
    G: Graph<'a>,
    G::Node: Hash,
    D: Copy + PartialOrd + Zero,
    W: Fn(G::Edge) -> D,
    H: AStarHeuristic<G::Node>,
    H::Result: Add<D, Output = D>,
{
    start(Neighbors(g), src, weights, heur)
}

/// Run an A*-search on an undirected graph and return the path.
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
/// - `heur`: the lower bound heuristic
///
/// The function returns the edges on the path and its length.
pub fn find_undirected_path<'a, G, D, W, H>(
    g: &'a G,
    src: G::Node,
    snk: G::Node,
    weights: W,
    heur: H,
) -> Option<(Vec<G::Edge>, D)>
where
    G: Graph<'a>,
    G::Node: Hash,
    D: 'a + Copy + PartialOrd + Zero + Add<D, Output = D> + Sub<D, Output = D>,
    W: Fn(G::Edge) -> D,
    H: AStarHeuristic<G::Node>,
    H::Result: Add<D, Output = D>,
{
    if src == snk {
        return Some((vec![], D::zero()));
    }
    // run search until sink node has been found
    let mut incoming_edges = HashMap::new();
    for (u, e, d) in start_undirected(g, src, weights, heur) {
        incoming_edges.insert(u, e);
        if u == snk {
            let mut path = path_from_incomings(snk, |u| {
                incoming_edges
                    .get(&u)
                    .map(|&e| (e, g.enodes(e)))
                    .map(|(e, (v, w))| (e, if v == u { w } else { v }))
            })
            .collect::<Vec<_>>();
            path.reverse();
            return Some((path, d));
        }
    }
    None
}

/// Start an A*-search on a directed graph.
///
/// This is a convenience wrapper to start the search on an directed graph
/// with the default data structures.
///
/// # Parameter
/// - `g`: the graph
/// - `weights`: the (non-negative) edge weights
/// - `src`: the source node
/// - `heur`: the lower bound heuristic
pub fn start_directed<'a, G, D, W, H>(
    g: &'a G,
    src: G::Node,
    weights: W,
    heur: H,
) -> AStarDefault<'a, OutEdges<'a, G>, D, W, H>
where
    G: Digraph<'a>,
    G::Node: Hash,
    D: Copy + PartialOrd + Zero,
    W: Fn(G::Edge) -> D,
    H: AStarHeuristic<G::Node>,
    H::Result: Add<D, Output = D>,
{
    start(OutEdges(g), src, weights, heur)
}

/// Run an A*-search on a directed graph and return the path.
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
/// - `heur`: the lower bound heuristic
///
/// The function returns the edges on the path and its length.
pub fn find_directed_path<'a, G, D, W, H>(
    g: &'a G,
    src: G::Node,
    snk: G::Node,
    weights: W,
    heur: H,
) -> Option<(Vec<G::Edge>, D)>
where
    G: Digraph<'a>,
    G::Node: Hash,
    D: 'a + Copy + PartialOrd + Zero + Add<D, Output = D> + Sub<D, Output = D>,
    W: Fn(G::Edge) -> D,
    H: AStarHeuristic<G::Node>,
    H::Result: Add<D, Output = D>,
{
    if src == snk {
        return Some((vec![], D::zero()));
    }
    // run search until sink node has been found
    let mut incoming_edges = HashMap::new();
    for (u, e, d) in start_directed(g, src, weights, heur) {
        incoming_edges.insert(u, e);
        if u == snk {
            let mut path =
                path_from_incomings(snk, |u| incoming_edges.get(&u).map(|&e| (e, g.src(e)))).collect::<Vec<_>>();
            path.reverse();
            return Some((path, d));
        }
    }
    None
}
