/*
 * Copyright (c) 2017-2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! This module implements the max flow algorithm of Edmonds-Karp.
//!
//! # Example
//!
//! ```
//! use rs_graph::traits::*;
//! use rs_graph::maxflow::edmondskarp;
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
//! let (value, flow, mut mincut) = edmondskarp(&g, s, t, |e| upper[e.index()]);
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
//! use rs_graph::maxflow::edmondskarp;
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
//! let (value, flow, mut mincut) = edmondskarp(&g, s, t, |e| upper[e.index()]);
//! assert_eq!(value, 29);
//!
//! mincut.sort_by_key(|u| u.index());
//! assert_eq!(mincut, "bcsef".chars().map(|v| nodes[&v]).collect::<Vec<_>>());
//! ```

use crate::traits::IndexDigraph;

use std::cmp::min;
use std::collections::VecDeque;

use crate::num::traits::NumAssign;

/// Max-flow algorithm of Edmonds and Karp.
pub struct EdmondsKarp<'a, G, F>
where
    G: 'a + IndexDigraph<'a>,
{
    g: &'a G,
    neighs: Vec<Vec<(usize, usize)>>,
    pred: Vec<(usize, usize)>,
    flow: Vec<F>,
    queue: VecDeque<usize>,
    value: F,
}

impl<'a, G, F> EdmondsKarp<'a, G, F>
where
    G: IndexDigraph<'a>,
    F: NumAssign + Ord + Copy,
{
    /// Create a new Dinic algorithm instance for a graph.
    pub fn new(g: &'a G) -> Self {
        EdmondsKarp {
            g,
            neighs: g
                .nodes()
                .map(|u| {
                    g.outedges(u)
                        .map(|(e, v)| (g.edge_id(e) << 1, g.node_id(v)))
                        .chain(g.inedges(u).map(|(e, v)| ((g.edge_id(e) << 1) | 1, g.node_id(v))))
                        .collect()
                })
                .collect(),
            pred: vec![(usize::max_value(), usize::max_value()); g.num_nodes()],
            flow: vec![F::zero(); g.num_edges() * 2],
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
        self.flow[self.g.edge_id(e) << 1]
    }

    pub fn solve<Us>(&mut self, src: G::Node, snk: G::Node, upper: Us)
    where
        Us: Fn(G::Edge) -> F,
    {
        let src = self.g.node_id(src);
        let snk = self.g.node_id(snk);
        assert_ne!(src, snk, "Source and sink node must not be equal");

        // initialize network flow
        for (e, flw) in self.flow.iter_mut().enumerate() {
            *flw = if (e & 1) == 0 {
                F::zero()
            } else {
                upper(self.g.id2edge(e >> 1))
            };
        }
        self.value = F::zero();

        // nothing to do if there is no edge
        if self.g.num_edges() == 0 {
            return;
        }

        loop {
            // do bfs from source to sink
            self.pred.fill((usize::max_value(), usize::max_value()));

            // just some dummy edge
            self.pred[src] = (0, 0);
            self.queue.clear();
            self.queue.push_back(src);
            'bfs: while let Some(u) = self.queue.pop_front() {
                for &(e, v) in &self.neighs[u] {
                    if self.pred[v].0 == usize::max_value() && !self.flow[e ^ 1].is_zero() {
                        self.pred[v] = (e, u);
                        self.queue.push_back(v);
                        if v == snk {
                            break 'bfs;
                        }
                    }
                }
            }

            // sink cannot be reached -> stop
            if self.pred[snk].0 == usize::max_value() {
                break;
            }

            // compute augmentation value
            let mut v = snk;
            let mut df = self.flow[self.pred[v].0 ^ 1];
            while v != src {
                let (e, u) = self.pred[v];
                df = min(df, self.flow[e ^ 1]);
                v = u;
            }

            debug_assert!(!df.is_zero());

            // now augment the flow
            let mut v = snk;
            while v != src {
                let (e, u) = self.pred[v];
                self.flow[e] += df;
                self.flow[e ^ 1] -= df;
                v = u;
            }

            self.value += df;
        }
    }

    /// Return the minimal cut associated with the last maximum flow.
    pub fn mincut(&self) -> Vec<G::Node> {
        self.g
            .nodes()
            .filter(|&u| self.pred[self.g.node_id(u)].0 != usize::max_value())
            .collect()
    }
}

/// Solve the maxflow problem using the algorithm of Edmonds-Karp.
///
/// The function solves the max flow problem from the source nodes
/// `src` to the sink node `snk` with the given `upper` bounds on
/// the edges.
///
/// The function returns the flow value, the flow on each edge and the
/// nodes in a minimal cut.
pub fn edmondskarp<'a, G, F, Us>(
    g: &'a G,
    src: G::Node,
    snk: G::Node,
    upper: Us,
) -> (F, Vec<(G::Edge, F)>, Vec<G::Node>)
where
    G: IndexDigraph<'a>,
    F: 'a + NumAssign + Ord + Copy,
    Us: Fn(G::Edge) -> F,
{
    let mut maxflow = EdmondsKarp::new(g);
    maxflow.solve(src, snk, upper);
    (
        maxflow.value(),
        g.edges().map(|e| (e, maxflow.flow(e))).collect(),
        maxflow.mincut(),
    )
}
