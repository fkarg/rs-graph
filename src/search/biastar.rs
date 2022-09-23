/*
 * Copyright (c) 2019, 2021 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! Bidirectional A*-search.
//!
//! This module implements a bidirectional A*-search for finding a shortest path
//! between two nodes starting from both endpoints. Each node may be assigned a
//! potential (or "heuristic value") estimating the distance to the target
//! nodes. The potential $h\colon V \to \mathbb{R}$ must satisfy
//! \\[ w(u,v) - h(u) + h(v) \ge 0, (u,v) \in E \\]
//! where $w\colon E \to \mathbb{R}$ are the weights (or lengths) of the edges.
//! (The relation must hold for both directions in case the graph is
//! undirected).
//!
//! If $s,t \in V$ are the start and destination nodes of the path,
//! respectively, and $h_s\colon V \to \mathbb{R}$ and $h_t\colon V \to
//! \mathbb{R}$ are lower bounds for the distance from each node $u \in V$ to
//! $s$ and $t$, then the canonical choice of $h$ is \\[ h\colon u \to
//! \mathbb{R}, u \mapsto \frac12 (h_s(u) - h_t(u)). \\]
//!
//! # Example
//!
//! ```
//! use rs_graph::traits::*;
//! use rs_graph::search::biastar;
//! use rs_graph::string::{from_ascii, Data};
//! use rs_graph::LinkedListGraph;
//!
//! let Data {
//!     graph: g,
//!     weights,
//!     nodes,
//! } = from_ascii::<LinkedListGraph>(
//!     r"
//! *--2--*--2--*--2--*--2--*--2--*--2--*--2--*--2--*--2--*
//! |     |     |     |     |     |     |     |     |     |
//! 2     2     2     2     2     2     2     2     2     2
//! |     |     |     |     |     |     |     |     |     |
//! *--2--*--2--*--2--*--2--*--3--e--2--f--2--t--2--*--2--*
//! |     |     |     |     |     |     |     |     |     |
//! 2     2     2     2     2     2     3     2     2     2
//! |     |     |     |     |     |     |     |     |     |
//! *--2--*--2--*--3--*--3--c--2--d--2--*--3--*--2--*--2--*
//! |     |     |     |     |     |     |     |     |     |
//! 2     2     2     2     2     3     2     2     2     2
//! |     |     |     |     |     |     |     |     |     |
//! *--2--*--2--s--2--a--2--b--2--*--2--*--3--*--2--*--2--*
//! |     |     |     |     |     |     |     |     |     |
//! 2     2     2     2     2     2     2     2     2     2
//! |     |     |     |     |     |     |     |     |     |
//! *--2--*--2--*--2--*--2--*--2--*--2--*--2--*--2--*--2--*
//! ",
//! )
//! .unwrap();
//!
//! let s = nodes[&'s'];
//! let t = nodes[&'t'];
//!
//! // nodes are numbered row-wise -> get node coordinates
//! let coords = |u| ((g.node_id(u) % 10) as isize, (g.node_id(u) / 10) as isize);
//!
//! let (xs, ys) = coords(s);
//! let (xt, yt) = coords(t);
//!
//! // Manhatten distance heuristic
//! let manh_heur = |u| {
//!     let (x, y) = coords(u);
//!     0.5 * (((x - xt).abs() + (y - yt).abs()) as f64 - ((x - xs).abs() + (y - ys).abs()) as f64)
//! };
//!
//! let (path, dist) = biastar::find_undirected_path(&g, s, t, |e| weights[e.index()] as f64, manh_heur).unwrap();
//!
//! assert!((dist - 14.0).abs() < 1e-6);
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
//!
//! assert_eq!(pathnodes, "sabcdeft".chars().map(|c| nodes[&c]).collect::<Vec<_>>());
//!
//! // verify that we did not go too far in the "wrong" direction
//! for (v, _, _) in biastar::start_undirected(&g, s, t, |e| weights[e.index()] as f64, manh_heur) {
//!     let (x, y) = coords(v);
//!     assert!(x + 1 >= xs && x <= xt + 1 && y + 1 >= yt && y <= ys + 1);
//! }
//! ```

use crate::adjacencies::{Adjacencies, InEdges, Neighbors, OutEdges};
use crate::collections::{BinHeap, ItemMap, ItemPriQueue};
pub use crate::search::astar::AStarHeuristic as Heuristic;
use crate::search::path_from_incomings;
use crate::traits::{Digraph, Graph, GraphType};

use either::Either::{self, Left, Right};
use num_traits::Zero;

use std::cmp::Ordering;
use std::collections::HashMap;
use std::hash::Hash;
use std::ops::{Add, Neg, Sub};

pub use super::astar::DefaultData;

/// Direction of search.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Direction<E> {
    /// Edge in forward search.
    Forward(E),
    /// Edge in backward search.
    Backward(E),
}

/// Predecessor edge information.
#[derive(Clone, Copy, Debug)]
pub struct BiData<E, D, H> {
    /// adjacent edge
    edge: E,
    /// distance to source or sink (None if never seen).
    distance: D,
    /// the lower bound of this node
    lower: H,
}

impl<E, D, H> PartialEq for BiData<E, D, H>
where
    D: PartialEq,
{
    fn eq(&self, data: &Self) -> bool {
        self.distance.eq(&data.distance)
    }
}

impl<E, D, H> PartialOrd for BiData<E, D, H>
where
    D: PartialOrd + Clone,
    H: Add<D, Output = D> + Clone,
{
    fn partial_cmp(&self, data: &Self) -> Option<Ordering> {
        (self.lower.clone() + self.distance.clone()).partial_cmp(&(data.lower.clone() + data.distance.clone()))
    }
}

/// Information about the meeting edge.
struct Meet<N, E, D> {
    /// The destination node of the connecting edge.
    node: N,
    /// The connecting edge.
    edge: E,
    /// The forward distance of the node.
    fwd_distance: D,
    /// The total distance of the path.
    total_distance: D,
}

/// Iterator for visiting edges in A*-order.
pub struct BiAStar<'a, Aout, Ain, D, W, M, P, H>
where
    Aout: Adjacencies<'a>,
    Ain: Adjacencies<'a, Node = Aout::Node, Edge = Aout::Edge>,
    M: ItemMap<Direction<Aout::Node>, Either<P::Item, D>>,
    P: ItemPriQueue<Direction<Aout::Node>, BiData<Aout::Edge, D, H::Result>>,
    D: Copy,
    W: Fn(Aout::Edge) -> D,
    H: Heuristic<Aout::Node>,
    H::Result: Copy,
{
    adjout: Aout,
    adjin: Ain,
    nodes: M,
    pqueue: P,
    weights: W,
    heur: H,
    /// The meet information, i.e. the final connecting edge.
    meet: Option<Meet<Aout::Node, Aout::Edge, D>>,
    /// The currently top-most (i.e. smallest) value in forward direction on the heap.
    top_fwd: D,
    /// The currently top-most (i.e. smallest) value in backward direction on the heap.
    top_bwd: D,
}

/// Default map type to be used in an A* search.
///
/// - `A` is the graph type information
/// - `D` is the type of distance values
/// - `H` is the type of heuristic values
pub type DefaultMap<'a, A, D, H> = HashMap<
    Direction<<A as GraphType<'a>>::Node>,
    Either<
        <BinHeap<Direction<<A as GraphType<'a>>::Node>, BiData<<A as GraphType<'a>>::Edge, D, H>> as ItemPriQueue<
            Direction<<A as GraphType<'a>>::Node>,
            BiData<<A as GraphType<'a>>::Edge, D, H>,
        >>::Item,
        D,
    >,
>;

/// Default priority queue type to be used in an A* search.
///
/// - `A` is the graph type information
/// - `D` is the type of distance values
/// - `H` is the type of heuristic values
/// - `ID` is used for identifying items on the heap internally
pub type DefaultPriQueue<'a, A, D, H, ID = u32> =
    BinHeap<Direction<<A as GraphType<'a>>::Node>, BiData<<A as GraphType<'a>>::Edge, D, H>, ID>;

/// BiAStar iterator with default data structures.
pub type BiAStarDefault<'a, Aout, Ain, D, W, H> = BiAStar<
    'a,
    Aout,
    Ain,
    D,
    W,
    DefaultMap<'a, Aout, D, <H as Heuristic<<Aout as GraphType<'a>>::Node>>::Result>,
    DefaultPriQueue<'a, Aout, D, <H as Heuristic<<Aout as GraphType<'a>>::Node>>::Result>,
    H,
>;

/// Start and return a bidirectional A*-iterator using default data structures.
///
/// This is a convenience wrapper around [`start_with_data`] using the default
/// data structures [`DefaultData`].
///
/// # Parameters
/// - `adjout`: adjacency information for the forward search (i.e outgoing edges)
/// - `adjin`: adjacency information for the backward search (i.e incoming edges)
/// - `src`: the source node at which the path should start.
/// - `snk`: the snk node at which the path should end.
/// - `weights`: the weight function for each edge
/// - `heur`: the heuristic used in the search
pub fn start<'a, Aout, Ain, D, W, H>(
    adjout: Aout,
    adjin: Ain,
    src: Aout::Node,
    snk: Aout::Node,
    weights: W,
    heur: H,
) -> BiAStarDefault<'a, Aout, Ain, D, W, H>
where
    Aout: Adjacencies<'a>,
    Aout::Node: Hash + Eq,
    Ain: Adjacencies<'a, Node = Aout::Node, Edge = Aout::Edge>,
    D: Copy + Zero + PartialOrd,
    W: Fn(Aout::Edge) -> D,
    H: Heuristic<Aout::Node>,
    H::Result: Add<D, Output = D> + Add<H::Result, Output = H::Result> + Neg<Output = H::Result>,
{
    start_with_data(adjout, adjin, src, snk, weights, heur, DefaultData::default())
}

/// Start and return a bidirectional A*-iterator.
///
/// The returned iterator traverses the edges in the order of a bidirectional
/// A*-search. The iterator returns the next node, its incoming edge with
/// direction information and the distance to the start node or end node
/// depending on the direction.
///
/// The heuristic is a assigning a potential to each node. The potential of all
/// nodes must be so that $w(u,v) - h(u) + h(v) \ge 0$ for all edges $(u,v) \in
/// E$. The value returned by the heuristic must be compatible with the distance
/// type, i.e., is must be possible to compute the sum of both.
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
/// - `weights`: the weight function for each edge
/// - `heur`: the heuristic used in the search
/// - `data`: the data structures
pub fn start_with_data<'a, Aout, Ain, D, W, H, M, P>(
    adjout: Aout,
    adjin: Ain,
    src: Aout::Node,
    snk: Aout::Node,
    weights: W,
    heur: H,
    data: (M, P),
) -> BiAStar<'a, Aout, Ain, D, W, M, P, H>
where
    Aout: Adjacencies<'a>,
    Ain: Adjacencies<'a, Node = Aout::Node, Edge = Aout::Edge>,
    D: Copy + PartialOrd + Zero,
    W: Fn(Aout::Edge) -> D,
    M: ItemMap<Direction<Aout::Node>, Either<P::Item, D>>,
    P: ItemPriQueue<Direction<Aout::Node>, BiData<Aout::Edge, D, H::Result>>,
    H: Heuristic<Aout::Node>,
    H::Result: Add<D, Output = D> + Add<H::Result, Output = H::Result> + Neg<Output = H::Result>,
{
    let (mut nodes, mut pqueue) = data;
    pqueue.clear();
    nodes.clear();

    if src == snk {
        // if src == snk then we do not start the search at all
        return BiAStar {
            adjout,
            adjin,
            nodes,
            pqueue,
            weights,
            heur,
            meet: None,
            top_fwd: D::zero(),
            top_bwd: D::zero(),
        };
    }

    nodes.insert(Direction::Forward(src), Right(D::zero()));
    nodes.insert(Direction::Backward(snk), Right(D::zero()));

    // insert neighbors of source
    for (e, v) in adjout.neighs(src) {
        let dir_v = Direction::Forward(v);
        let d = (weights)(e);
        match nodes.get_mut(dir_v) {
            Some(Left(item_v)) => {
                // node is known but unhandled
                let (distance, lower) = {
                    let data = pqueue.value(item_v);
                    (data.distance, data.lower)
                };

                if d < distance {
                    pqueue.decrease_key(
                        item_v,
                        BiData {
                            edge: e,
                            distance: d,
                            lower,
                        },
                    );
                }
            }
            None => {
                // node is unknown
                let item_v = pqueue.push(
                    dir_v,
                    BiData {
                        edge: e,
                        distance: d,
                        lower: heur.call(v),
                    },
                );
                nodes.insert(dir_v, Left(item_v));
            }
            _ => (), // node has already been handled
        }
    }

    let mut meet: Option<Meet<_, _, _>> = None;
    // insert neighbors of sink
    for (e, v) in adjin.neighs(snk) {
        let dir_v = Direction::Backward(v);
        let d = (weights)(e);
        if v == src {
            // found a possible first path, this is only possible for (src, snk)
            // edges and the length of this path is the edge weight
            if meet.as_ref().map(|m| d < m.total_distance).unwrap_or(true) {
                // found a better path -> save
                meet = Some(Meet {
                    node: snk,
                    edge: e,
                    fwd_distance: d,
                    total_distance: d,
                });
            }
        }
        match nodes.get_mut(dir_v) {
            Some(Left(item_v)) => {
                // node is known but unhandled
                let (distance, lower) = {
                    let data = pqueue.value(item_v);
                    (data.distance, data.lower)
                };
                if d < distance {
                    pqueue.decrease_key(
                        item_v,
                        BiData {
                            edge: e,
                            distance: d,
                            lower,
                        },
                    );
                }
            }
            None => {
                // node is unknown
                let item_v = pqueue.push(
                    dir_v,
                    BiData {
                        edge: e,
                        distance: d,
                        lower: -heur.call(v),
                    },
                );
                nodes.insert(dir_v, Left(item_v));
            }
            _ => (), // node has already been handled
        }
    }

    BiAStar {
        adjout,
        adjin,
        nodes,
        pqueue,
        weights,
        heur,
        meet,
        top_fwd: D::zero(),
        top_bwd: D::zero(),
    }
}

impl<'a, Aout, Ain, D, W, M, P, H> Iterator for BiAStar<'a, Aout, Ain, D, W, M, P, H>
where
    Aout: Adjacencies<'a>,
    Ain: Adjacencies<'a, Node = Aout::Node, Edge = Aout::Edge>,
    D: Copy + PartialOrd + Add<D, Output = D> + Sub<D, Output = D> + Zero,
    W: Fn(Aout::Edge) -> D,
    M: ItemMap<Direction<Aout::Node>, Either<P::Item, D>>,
    P: ItemPriQueue<Direction<Aout::Node>, BiData<Aout::Edge, D, H::Result>>,
    H: Heuristic<Aout::Node>,
    H::Result: Add<D, Output = D> + Add<H::Result, Output = H::Result> + Neg<Output = H::Result>,
{
    type Item = (Aout::Node, Direction<Aout::Edge>, D);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((dir_u, data)) = self.pqueue.pop_min() {
            // node is not in the queue anymore, forget its item
            self.nodes.insert_or_replace(dir_u, Right(data.distance));
            let (distance, edge) = (data.distance, data.edge);

            // stopping test, first update forward or backward bound
            //
            // Note: `top_fwd` and `top_bwd` are actually lower bounds on the
            // values on the heap because the value with that value has just
            // been removed ... anyway, it is good enough for us
            if let Direction::Forward(_) = dir_u {
                self.top_fwd = data.lower + data.distance;
            } else {
                self.top_bwd = data.lower + data.distance;
            };

            if self
                .meet
                .as_ref()
                .map(|m| m.total_distance <= self.top_fwd + self.top_bwd)
                .unwrap_or(false)
            {
                // stopping condition met, we cannot find a better path
                self.pqueue.clear();

                // return the final connecting edge
                let meet = self.meet.as_ref().unwrap();
                return Some((meet.node, Direction::Forward(meet.edge), meet.fwd_distance));
            }

            match dir_u {
                // forward search
                Direction::Forward(u) => {
                    // look for neighbors
                    for (e, v) in self.adjout.neighs(u) {
                        let dir_v = Direction::Forward(v);
                        let edge_weight = (self.weights)(e);
                        let d = distance + edge_weight;
                        if let Some(Right(rdistance)) = self.nodes.get(Direction::Backward(v)) {
                            // check whether we found a better path
                            let new_dist = *rdistance + distance + edge_weight;
                            if self.meet.as_ref().map(|m| new_dist < m.total_distance).unwrap_or(true) {
                                // found a better path -> save
                                self.meet = Some(Meet {
                                    node: v,
                                    edge: e,
                                    fwd_distance: d,
                                    total_distance: new_dist,
                                });
                            }
                        }
                        match self.nodes.get_mut(dir_v) {
                            Some(Left(item_v)) => {
                                // node is known but unhandled
                                let (distance, lower) = {
                                    let data = self.pqueue.value(item_v);
                                    (data.distance, data.lower)
                                };
                                if d < distance {
                                    self.pqueue.decrease_key(
                                        item_v,
                                        BiData {
                                            edge: e,
                                            distance: d,
                                            lower,
                                        },
                                    );
                                }
                            }
                            None => {
                                // node is unknown
                                let item_v = self.pqueue.push(
                                    dir_v,
                                    BiData {
                                        edge: e,
                                        distance: d,
                                        lower: self.heur.call(v),
                                    },
                                );
                                self.nodes.insert(dir_v, Left(item_v));
                            }
                            _ => (), // node has already been handled
                        }
                    }
                }
                // backward search
                Direction::Backward(u) => {
                    // look for neighbors
                    for (e, v) in self.adjin.neighs(u) {
                        assert!((-self.heur.call(v) + self.heur.call(u)) + (self.weights)(e) >= D::zero());
                        let dir_v = Direction::Backward(v);
                        let edge_weight = (self.weights)(e);
                        let d = distance + edge_weight;
                        if let Some(Right(rdistance)) = self.nodes.get(Direction::Forward(v)) {
                            // check whether we found a better path
                            let new_dist = *rdistance + distance + edge_weight;
                            if self.meet.as_ref().map(|m| new_dist < m.total_distance).unwrap_or(true) {
                                // found a better path -> save
                                self.meet = Some(Meet {
                                    node: u,
                                    edge: e,
                                    fwd_distance: *rdistance + edge_weight,
                                    total_distance: new_dist,
                                });
                            }
                        }
                        match self.nodes.get_mut(dir_v) {
                            Some(Left(item_v)) => {
                                // node is known but unhandled
                                let (distance, lower) = {
                                    let data = self.pqueue.value(item_v);
                                    (data.distance, data.lower)
                                };
                                if d < distance {
                                    self.pqueue.decrease_key(
                                        item_v,
                                        BiData {
                                            edge: e,
                                            distance: d,
                                            lower,
                                        },
                                    );
                                }
                            }
                            None => {
                                // node is unknown
                                let item_v = self.pqueue.push(
                                    dir_v,
                                    BiData {
                                        edge: e,
                                        distance: d,
                                        lower: -self.heur.call(v),
                                    },
                                );
                                self.nodes.insert(dir_v, Left(item_v));
                            }
                            _ => (), // node has already been handled
                        }
                    }
                }
            }

            match dir_u {
                Direction::Forward(u) => Some((u, Direction::Forward(edge), distance)),
                Direction::Backward(u) => Some((u, Direction::Backward(edge), distance)),
            }
        } else {
            None
        }
    }
}

impl<'a, Aout, Ain, D, W, M, P, H> BiAStar<'a, Aout, Ain, D, W, M, P, H>
where
    Aout: Adjacencies<'a>,
    Ain: Adjacencies<'a, Node = Aout::Node, Edge = Aout::Edge>,
    D: Copy + PartialOrd + Add<D, Output = D> + Sub<D, Output = D>,
    W: Fn(Aout::Edge) -> D,
    M: ItemMap<Direction<Aout::Node>, Either<P::Item, D>>,
    P: ItemPriQueue<Direction<Aout::Node>, BiData<Aout::Edge, D, H::Result>>,
    H: Heuristic<Aout::Node>,
    H::Result: Add<D, Output = D> + Neg<Output = H::Result>,
{
    /// Return the meet node.
    ///
    /// This is the node where forward and backward search met.
    fn meet(&self) -> Option<Aout::Node> {
        self.meet.as_ref().map(|m| m.node)
    }

    /// Return the value of the shortest path.
    fn value(&self) -> Option<D> {
        self.meet.as_ref().map(|m| m.total_distance)
    }
}

/// Start a bidirectional A*-search on an undirected graph.
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
/// - `heur`: the heuristic used in the search
pub fn start_undirected<'a, G, D, W, H>(
    g: &'a G,
    src: G::Node,
    snk: G::Node,
    weights: W,
    heur: H,
) -> BiAStarDefault<'a, Neighbors<'a, G>, Neighbors<'a, G>, D, W, H>
where
    G: Graph<'a>,
    G::Node: Hash,
    D: Copy + PartialOrd + Zero,
    W: Fn(G::Edge) -> D,
    H: Heuristic<G::Node>,
    H::Result: Add<D, Output = D> + Add<H::Result, Output = H::Result> + Neg<Output = H::Result>,
{
    start(Neighbors(g), Neighbors(g), src, snk, weights, heur)
}

/// Run a bidirectional A*-search on an undirected graph and return the path.
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
/// - `heur`: the heuristic used in the search
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
    D: Copy + PartialOrd + Zero + Add<D, Output = D> + Sub<D, Output = D>,
    W: Fn(G::Edge) -> D,
    H: Heuristic<G::Node>,
    H::Result: Add<D, Output = D> + Add<H::Result, Output = H::Result> + Neg<Output = H::Result>,
{
    if src == snk {
        return Some((vec![], D::zero()));
    }
    // run search until a node has been seen from both sides
    let mut incoming_edges = HashMap::new();
    let mut it = start_undirected(g, src, snk, weights, heur);
    while let Some((u, dir_e, _)) = it.next() {
        match dir_e {
            Direction::Forward(e) => incoming_edges.insert(Direction::Forward(u), e),
            Direction::Backward(e) => incoming_edges.insert(Direction::Backward(u), e),
        };
    }

    it.meet().map(|meet| {
        let mut path = path_from_incomings(meet, |u| {
            incoming_edges
                .get(&Direction::Forward(u))
                .map(|&e| (e, g.enodes(e)))
                .map(|(e, (v, w))| (e, if v == u { w } else { v }))
        })
        .collect::<Vec<_>>();
        path.reverse();
        path.extend(path_from_incomings(meet, |u| {
            incoming_edges
                .get(&Direction::Backward(u))
                .map(|&e| (e, g.enodes(e)))
                .map(|(e, (v, w))| (e, if v == u { w } else { v }))
        }));
        (path, it.value().unwrap())
    })
}

/// Start a bidirectional A*-search on a directed graph.
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
pub fn start_directed<'a, G, D, W, H>(
    g: &'a G,
    src: G::Node,
    snk: G::Node,
    weights: W,
    heur: H,
) -> BiAStarDefault<'a, OutEdges<'a, G>, InEdges<'a, G>, D, W, H>
where
    G: Digraph<'a>,
    G::Node: Hash,
    D: Copy + PartialOrd + Zero,
    W: Fn(G::Edge) -> D,
    H: Heuristic<G::Node>,
    H::Result: Add<D, Output = D> + Add<H::Result, Output = H::Result> + Neg<Output = H::Result>,
{
    start(OutEdges(g), InEdges(g), src, snk, weights, heur)
}

/// Run a bidirectional A*-search on an directed graph and return the path.
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
/// - `heur`: the heuristic used in the search
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
    D: Copy + PartialOrd + Zero + Add<D, Output = D> + Sub<D, Output = D>,
    W: Fn(G::Edge) -> D,
    H: Heuristic<G::Node>,
    H::Result: Add<D, Output = D> + Add<H::Result, Output = H::Result> + Neg<Output = H::Result>,
{
    if src == snk {
        return Some((vec![], D::zero()));
    }
    // run search until a node has been seen from both sides
    let mut incoming_edges = HashMap::new();
    let mut it = start_directed(g, src, snk, weights, heur);
    while let Some((u, dir_e, _)) = it.next() {
        match dir_e {
            Direction::Forward(e) => incoming_edges.insert(Direction::Forward(u), e),
            Direction::Backward(e) => incoming_edges.insert(Direction::Backward(u), e),
        };
    }

    it.meet().map(|meet| {
        let mut path = path_from_incomings(meet, |u| {
            incoming_edges.get(&Direction::Forward(u)).map(|&e| (e, g.src(e)))
        })
        .collect::<Vec<_>>();
        path.reverse();
        path.extend(path_from_incomings(meet, |u| {
            incoming_edges.get(&Direction::Backward(u)).map(|&e| (e, g.snk(e)))
        }));

        (path, it.value().unwrap())
    })
}

#[test]
fn test_biastar() {
    use crate::search::biastar;
    use crate::string::{from_ascii, Data};
    use crate::traits::*;
    use crate::LinkedListGraph;

    let Data {
        graph: g,
        weights,
        nodes,
    } = from_ascii::<LinkedListGraph>(
        r"
    *--2--*--2--*--2--*--2--*--2--*--2--*--2--*--2--*--2--*
    |     |     |     |     |     |     |     |     |     |
    2     2     2     2     2     2     2     2     2     2
    |     |     |     |     |     |     |     |     |     |
    *--2--*--2--*--2--*--2--*--3--e--2--f--2--t--2--*--2--*
    |     |     |     |     |     |     |     |     |     |
    2     2     2     2     2     2     3     2     2     2
    |     |     |     |     |     |     |     |     |     |
    *--2--*--2--*--3--*--3--c--2--d--2--*--3--*--2--*--2--*
    |     |     |     |     |     |     |     |     |     |
    2     2     2     2     2     3     2     2     2     2
    |     |     |     |     |     |     |     |     |     |
    *--2--*--2--s--2--a--2--b--2--*--2--*--3--*--2--*--2--*
    |     |     |     |     |     |     |     |     |     |
    2     2     2     2     2     2     2     2     2     2
    |     |     |     |     |     |     |     |     |     |
    *--2--*--2--*--2--*--2--*--2--*--2--*--2--*--2--*--2--*
    ",
    )
    .unwrap();

    let s = nodes[&'s'];
    let t = nodes[&'t'];

    // nodes are numbered row-wise -> get node coordinates
    let coords = |u| ((g.node_id(u) % 10) as isize, (g.node_id(u) / 10) as isize);

    let (xs, ys) = coords(s);
    let (xt, yt) = coords(t);

    // Manhatten distance heuristic
    let manh_heur = |u| {
        let (x, y) = coords(u);
        0.5 * (((x - xt).abs() + (y - yt).abs()) as f64 - ((x - xs).abs() + (y - ys).abs()) as f64)
    };

    let (path, dist) = biastar::find_undirected_path(&g, s, t, |e| weights[e.index()] as f64, manh_heur).unwrap();

    assert!((dist - 14.0).abs() < 1e-6);

    let mut pathnodes = vec![s];
    for e in path {
        let uv = g.enodes(e);
        if uv.0 == *pathnodes.last().unwrap() {
            pathnodes.push(uv.1);
        } else {
            pathnodes.push(uv.0);
        }
    }

    assert_eq!(pathnodes, "sabcdeft".chars().map(|c| nodes[&c]).collect::<Vec<_>>());

    // verify that we did not go too far in the "wrong" direction
    for (v, _, _) in biastar::start_undirected(&g, s, t, |e| weights[e.index()] as f64, manh_heur) {
        let (x, y) = coords(v);
        assert!(x + 1 >= xs && x <= xt + 1 && y + 1 >= yt && y <= ys + 1);
    }
}

#[test]
fn test_biastar_correct() {
    use crate::search::biastar;
    use crate::string::{from_ascii, Data};
    use crate::traits::*;
    use crate::LinkedListGraph;

    let Data {
        graph: g,
        weights,
        nodes,
    } = from_ascii::<LinkedListGraph>(
        r"
          b--11--c---1--t
          |      |
          1      8
          |      |
    s--1--a--10--*
    ",
    )
    .unwrap();

    let s = nodes[&'s'];
    let t = nodes[&'t'];
    let a = nodes[&'a'];
    let b = nodes[&'b'];
    let c = nodes[&'c'];

    let (path, dist) = biastar::find_undirected_path(&g, s, t, |e| weights[e.index()] as isize, |_| 0).unwrap();

    let length: usize = path.iter().map(|e| weights[e.index()]).sum();
    assert_eq!(dist, 14);
    assert_eq!(length, 14);

    let path = path
        .into_iter()
        .map(|e| g.enodes(e))
        .map(|(u, v)| if g.node_id(u) < g.node_id(v) { (u, v) } else { (v, u) })
        .collect::<Vec<_>>();
    assert_eq!(path, vec![(s, a), (b, a), (b, c), (c, t)]);
}
