// Copyright (c) 2015-2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! This module implements Dinic' max flow algorithm
//!
//! # Example
//!
//! ```
//! use rs_graph::traits::*;
//! use rs_graph::maxflow::dinic;
//! use rs_graph::Net;
//! use rs_graph::string::{Data, from_ascii};
//!
//! let Data { graph: g, weights: upper, nodes } = from_ascii::<Net>(r"
//!      a---2-->b
//!     @|\      ^\
//!    / | \     | 4
//!   5  |  \    |  \
//!  /   |   |   |   @
//! s    1   1   2    t
//!  \   |   |   |   @
//!   5  |    \  |  /
//!    \ |     \ | 5
//!     @v      @|/
//!      c---2-->d
//!     ").unwrap();
//!
//! let s = nodes[&'s'];
//! let t = nodes[&'t'];
//! let v1 = nodes[&'a'];
//! let v2 = nodes[&'b'];
//! let v3 = nodes[&'c'];
//! let v4 = nodes[&'d'];
//!
//! let (value, flow, mut mincut) = dinic(&g, s, t, |e| upper[e.index()]);
//!
//! assert_eq!(value, 5);
//! assert!(flow.iter().all(|&(e, f)| f >= 0 && f <= upper[e.index()]));
//! assert!(g.nodes().filter(|&u| u != s && u != t).all(|u| {
//!     g.outedges(u).map(|(e,_)| flow[g.edge_id(e)].1).sum::<usize>() ==
//!     g.inedges(u).map(|(e,_)| flow[g.edge_id(e)].1).sum::<usize>()
//! }));
//!
//! mincut.sort_by_key(|u| u.index());
//! assert_eq!(mincut, vec![v1, s, v3]);
//! ```
//!
//! ```
//! use rs_graph::traits::*;
//! use rs_graph::maxflow::dinic;
//! use rs_graph::Net;
//! use rs_graph::string::{Data, from_ascii};
//!
//! let Data { graph: g, weights: upper, nodes } = from_ascii::<Net>(r"
//!                ---8-->a---10---
//!               /       |        \
//!              /        1  --3--  |
//!             /         | /     \ |
//!            /          v@       \v
//!      ---->b-----9---->c----8--->d----
//!     /      \         @         @^    \
//!   18        ---6--  /         / |     33
//!   /               \/         /  |      \
//!  /                /\    -----   |       @
//! s           --5--- |   /        |        t
//!  \         /       |  /         |       @
//!   27      |  ----2-|--         /       /
//!    \      | /      |  /----8---       6
//!     \     |/       @  |              /
//!      ---->e----9-->f------6---->g----
//!            \          |        @
//!             \         |       /
//!              --5----->h---4---
//!     ").unwrap();
//!
//! let s = nodes[&'s'];
//! let t = nodes[&'t'];
//!
//! assert_eq!(g.num_edges(), 18);
//!
//! let (value, flow, mut mincut) = dinic(&g, s, t, |e| upper[e.index()]);
//! assert_eq!(value, 29);
//!
//! mincut.sort_by_key(|u| u.index());
//! assert_eq!(mincut, "bcsef".chars().map(|v| nodes[&v]).collect::<Vec<_>>());
//! ```

use crate::traits::IndexDigraph;

use std::cmp::min;
use std::collections::VecDeque;

use crate::num::traits::NumAssign;

/// The dinic max-flow algorithm.
pub struct Dinic<'a, G, F>
where
    G: 'a + IndexDigraph<'a>,
{
    g: &'a G,
    nodes: Vec<NodeInfo>,
    neighs: Vec<Vec<(usize, usize)>>,
    edges: Vec<EdgeInfo<F>>,
    queue: VecDeque<usize>,
    value: F,
}

#[derive(Clone)]
struct NodeInfo {
    dist: usize,
    first_lvl: (usize, usize),
}

#[derive(Clone)]
struct EdgeInfo<F> {
    flow: F,
    next_lvl: (usize, usize),
}

impl<'a, G, F> Dinic<'a, G, F>
where
    G: IndexDigraph<'a>,
    F: NumAssign + Ord + Copy,
{
    /// Create a new Dinic algorithm instance for a graph.
    pub fn new(g: &'a G) -> Self {
        Dinic {
            g,
            nodes: vec![
                NodeInfo {
                    dist: 0,
                    first_lvl: (usize::max_value(), usize::max_value()),
                };
                g.num_nodes()
            ],
            neighs: g
                .nodes()
                .map(|u| {
                    g.outedges(u)
                        .map(|(e, v)| (g.edge_id(e) << 1, g.node_id(v)))
                        .chain(g.inedges(u).map(|(e, v)| ((g.edge_id(e) << 1) | 1, g.node_id(v))))
                        .collect()
                })
                .collect(),
            edges: vec![
                EdgeInfo {
                    flow: F::zero(),
                    next_lvl: (usize::max_value(), usize::max_value()),
                };
                g.num_edges() * 2
            ],
            queue: VecDeque::with_capacity(g.num_nodes()),
            value: F::zero(),
        }
    }

    /// Return the underlying graph.
    pub fn as_graph(&self) -> &'a G {
        self.g
    }

    /// Return the value of the latest computed maximum flow.
    pub fn value(&self) -> F {
        self.value
    }

    /// Return the flow value on edge `e`
    pub fn flow(&self, e: G::Edge) -> F {
        self.edges[self.g.edge_id(e) << 1].flow
    }

    /// Solve the maxflow problem.
    ///
    /// The method solved the max flow problem from the source node
    /// `src` to the sink node `snk` with the given `upper` bounds on
    /// the edges.
    pub fn solve<Us>(&mut self, src: G::Node, snk: G::Node, upper: Us)
    where
        Us: Fn(G::Edge) -> F,
    {
        let src = self.g.node_id(src);
        let snk = self.g.node_id(snk);
        assert_ne!(src, snk, "Source and sink node must not be equal");

        // initialize network flow of reverse edges
        for (e, einfo) in self.edges.iter_mut().enumerate() {
            einfo.flow = if (e & 1) == 0 {
                F::zero()
            } else {
                upper(self.g.id2edge(e >> 1))
            };
        }

        self.value = F::zero();
        while self.search(src, snk) {
            let v = self.augment(src, snk, None);
            self.value += v;
        }
    }

    /// Return the minimal cut associated with the last maximum flow.
    pub fn mincut(&self) -> Vec<G::Node> {
        let n = self.g.num_nodes();
        self.g
            .nodes()
            .filter(|&u| self.nodes[self.g.node_id(u)].dist < n)
            .collect()
    }

    fn search(&mut self, src: usize, snk: usize) -> bool {
        let n = self.g.num_nodes();

        for node in &mut self.nodes {
            node.dist = n;
            node.first_lvl = (usize::max_value(), usize::max_value());
        }
        self.nodes[src].dist = 0;

        self.queue.clear();
        self.queue.push_back(src);

        let mut snk_d = n;
        while let Some(u) = self.queue.pop_front() {
            let d = self.nodes[u].dist;

            if d >= snk_d {
                return true;
            }

            for &(e, v) in &self.neighs[u] {
                if self.edges[e ^ 1].flow > F::zero() {
                    if self.nodes[v].dist == n {
                        self.nodes[v].dist = d + 1;
                        self.queue.push_back(v);
                        if v == snk {
                            snk_d = d + 1
                        }
                    } else if self.nodes[v].dist != d + 1 {
                        continue;
                    }
                    self.edges[e].next_lvl = self.nodes[u].first_lvl;
                    self.nodes[u].first_lvl = (e, v);
                }
            }
        }

        false
    }

    fn augment(&mut self, src: usize, snk: usize, target_flow: Option<F>) -> F {
        if src == snk {
            return target_flow.expect("Unbounded flow (are source and sink the same?)");
        }

        let mut df = F::zero();

        loop {
            let (e, v) = self.nodes[src].first_lvl;
            if e == usize::max_value() {
                break;
            }
            let f = e ^ 1;
            let rem_cap = match target_flow {
                Some(target_flow) => min(self.edges[f].flow, target_flow - df),
                None => self.edges[f].flow,
            };
            if rem_cap > F::zero() {
                let cf = self.augment(v, snk, Some(rem_cap));
                self.edges[e].flow += cf;
                self.edges[f].flow -= cf;
                df += cf;
                if target_flow.map(|t| df == t).unwrap_or(false) {
                    break;
                }
            }

            // edge is saturated or blocked
            self.nodes[src].first_lvl = self.edges[e].next_lvl;
        }

        if df.is_zero() {
            // nothing can be sent from this node, delete the node and
            // all adjacent edges (we just remove the outgoing edges
            // so that they won't be seen)
            self.nodes[src].first_lvl = (usize::max_value(), usize::max_value());
        }

        df
    }
}

/// Solve the maxflow problem using the algorithm of Dinic.
///
/// The function solves the max flow problem from the source nodes
/// `src` to the sink node `snk` with the given `upper` bounds on
/// the edges.
///
/// The function returns the flow value, the flow on each edge and the
/// nodes in a minimal cut.
pub fn dinic<'a, G, F, Us>(g: &'a G, src: G::Node, snk: G::Node, upper: Us) -> (F, Vec<(G::Edge, F)>, Vec<G::Node>)
where
    G: IndexDigraph<'a>,
    F: 'a + NumAssign + Ord + Copy,
    Us: Fn(G::Edge) -> F,
{
    let mut maxflow = Dinic::new(g);
    maxflow.solve(src, snk, upper);
    (
        maxflow.value(),
        g.edges().map(|e| (e, maxflow.flow(e))).collect(),
        maxflow.mincut(),
    )
}
