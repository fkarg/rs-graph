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

//! This module implements a push relabel algorithm for solving max
//! flow problems.
//!
//! This implementation uses the gap heuristic and the global
//! relabelling heuristic.
//!
//! # Example
//!
//! ```
//! use rs_graph::traits::*;
//! use rs_graph::maxflow::pushrelabel;
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
//! let (value, flow, mut mincut) = pushrelabel(&g, s, t, |e| upper[e.index()]);
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
//! use rs_graph::maxflow::pushrelabel;
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
//!    \      | /      |  /----8---       7
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
//! let (value, flow, mut mincut) = pushrelabel(&g, s, t, |e| upper[e.index()]);
//! assert_eq!(value, 29);
//!
//! let mincutval = g
//!     .edges()
//!     .filter(|&e| mincut.contains(&g.src(e)) && !mincut.contains(&g.snk(e)))
//!     .map(|e| upper[e.index()])
//!     .sum::<usize>();
//! assert_eq!(value, mincutval);
//!
//! mincut.sort_by_key(|u| u.index());
//! assert_eq!(mincut, "bcsef".chars().map(|v| nodes[&v]).collect::<Vec<_>>());
//!
//! assert!(flow.iter().all(|&(e, f)| f >= 0 && f <= upper[e.index()]));
//! assert!(g.nodes().filter(|&u| u != s && u != t).all(|u| {
//!     g.outedges(u).map(|(e,_)| flow[g.edge_id(e)].1).sum::<usize>() ==
//!     g.inedges(u).map(|(e,_)| flow[g.edge_id(e)].1).sum::<usize>()
//! }));
//! ```

use crate::traits::IndexDigraph;

use std::cmp::min;
use std::collections::VecDeque;

use crate::num::traits::NumAssign;

/// The push-relabel algorithm.
///
/// This struct contains all algorithmic working data.
pub struct PushRelabel<'a, G, F>
where
    G: 'a + IndexDigraph<'a>,
{
    /// The underlying graph (extended to a network) the flow problem is solved
    /// on.
    g: &'a G,

    /// Data associated with each node.
    nodes: Vec<NodeInfo<F>>,
    /// The list of adjacent edges for each node.
    edges: Vec<Vec<(usize, usize)>>,
    /// Current flow on each edge.
    flow: Vec<F>,
    /// The buckets containing the nodes of a specific height.
    buckets: Vec<Bucket>,
    /// The queue of nodes for a BFS.
    queue: VecDeque<usize>,
    /// The largest height of an active node.
    largest_act: usize,
    /// The flow value.
    value: F,
    /// The number of relabel operations performed during the algorithm.
    pub cnt_relabel: usize,
    /// Whether to use the global relabelling heuristic.
    pub use_global_relabelling: bool,
}

/// Data associated with a node.
#[derive(Clone)]
struct NodeInfo<Flow> {
    /// The current height of the node.
    height: usize,
    /// The excess of flow of the node.
    excess: Flow,
    /// The next active node in the linked list for the current height.
    next_act: usize,
    /// The next edge to be considered
    iter: usize,
}

impl<Flow> NodeInfo<Flow>
where
    Flow: NumAssign,
{
    fn reset(&mut self) {
        self.height = 0;
        self.excess = Flow::zero();
        self.next_act = usize::max_value();
        self.iter = 0;
    }
}

/// A bucket containing nodes of some height.
#[derive(Clone)]
struct Bucket {
    /// The first active node of this height.
    ///
    /// The active nodes are kept in a singly linked list, this is the first
    /// node in that list.
    first_act: usize,
    /// Number of inactive nodes of this height.
    num_inact: usize,
}

impl Bucket {
    /// Returns `true` if the bucket is empty.
    ///
    /// This means that there are neither active nor inactive nodes of the
    /// buckets height.
    fn is_empty(&self) -> bool {
        self.first_act == usize::max_value() && self.num_inact == 0
    }
}

impl<'a, G, F> PushRelabel<'a, G, F>
where
    G: IndexDigraph<'a>,
    F: NumAssign + Ord + Copy,
{
    /// Return a new push-relabel algorithm data structure for the digraph `g`.
    pub fn new(g: &'a G) -> Self {
        let n = g.num_nodes();
        PushRelabel {
            g,
            nodes: vec![
                NodeInfo {
                    height: 0,
                    excess: F::zero(),
                    next_act: usize::max_value(),
                    iter: 0,
                };
                n
            ],
            edges: g
                .nodes()
                .map(|u| {
                    g.outedges(u)
                        .map(|(e, v)| (g.edge_id(e) << 1, g.node_id(v)))
                        .chain(g.inedges(u).map(|(e, v)| (((g.edge_id(e) << 1) | 1), g.node_id(v))))
                        .collect()
                })
                .collect(),
            flow: vec![F::zero(); g.num_edges() * 2],
            buckets: vec![
                Bucket {
                    first_act: usize::max_value(),
                    num_inact: 0,
                };
                n * 2
            ],
            queue: VecDeque::with_capacity(n),
            largest_act: 0,
            value: F::zero(),

            cnt_relabel: 0,
            use_global_relabelling: true,
        }
    }

    /// Return a reference to the underlying graph.
    pub fn as_graph(&self) -> &'a G {
        self.g
    }

    /// Return the flow value.
    ///
    /// The function returns 0 if the flow has not been computed, yet.
    pub fn value(&self) -> F {
        self.value
    }

    /// Return the flow value over some edge.
    ///
    /// The function returns 0 if the flow has not been computed, yet.
    pub fn flow(&self, e: G::Edge) -> F {
        self.flow[self.g.edge_id(e) << 1]
    }

    /// Run the push-relabel algorithm from some source to some sink node.
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

        let n = self.g.num_nodes();
        self.cnt_relabel = 0;
        self.init_preflow(src, upper);

        self.update_heights(src, snk, false);

        let mut lvl_relabel = if self.use_global_relabelling {
            n
        } else {
            usize::max_value()
        };

        while self.largest_act != 0 && self.largest_act != n {
            let l = self.largest_act;
            let u = self.buckets[l].first_act;
            self.buckets[l].first_act = self.nodes[u].next_act;
            self.discharge(u);
            if self.cnt_relabel >= lvl_relabel && self.largest_act < n {
                self.update_heights(src, snk, false);
                lvl_relabel += n;
            }

            if self.largest_act == 0 {
                // End of phase I. Compute exact labels one last time, this time
                // from the source.
                self.update_heights(src, snk, true);
            }
        }

        self.value = self.nodes[snk].excess;
    }

    /// Return the minimal cut associated with the last maximum flow.
    pub fn mincut(&self) -> Vec<G::Node> {
        // The minimal cut consists of the nodes with height >= n
        let n = self.g.num_nodes();
        self.g
            .nodes()
            .filter(|u| self.nodes[self.g.node_id(*u)].height >= n)
            .collect()
    }

    /// Initialize preflow algorithm.
    ///
    /// All edges leaving the source node are saturated, the source's
    /// height is set to `n`, all other heights are set to `0`.
    fn init_preflow<Us>(&mut self, src: usize, upper: Us)
    where
        Us: Fn(G::Edge) -> F,
    {
        for node in &mut self.nodes {
            node.reset();
        }
        for (e, flw) in self.flow.iter_mut().enumerate() {
            if e & 1 == 0 {
                *flw = F::zero();
            } else {
                *flw = upper(self.g.id2edge(e >> 1));
            }
        }

        // send maximal flow out of source
        for &(e, v) in &self.edges[src] {
            let f = e ^ 1;
            let ub = self.flow[f];
            self.flow[e] = ub;
            self.flow[f] = F::zero();
            self.nodes[v].excess += ub;
        }

        self.nodes[src].height = self.g.num_nodes();
    }

    /// Compute exact labels.
    ///
    /// This function does a bfs from the sink (phase I) or source (phase II) to
    /// compute exact labels.
    fn update_heights(&mut self, src: usize, snk: usize, from_src: bool) {
        let n = self.g.num_nodes();

        // Put all nodes to height 2*n
        for node in &mut self.nodes {
            node.height = n + n;
            // we need to reset the iterators for correctness
            node.iter = 0;
        }

        // Except for the source and and the sink
        self.nodes[snk].height = 0;
        self.nodes[src].height = n;

        for b in if from_src {
            &mut self.buckets[n + 1..]
        } else {
            &mut self.buckets[..n]
        } {
            b.first_act = usize::max_value();
            b.num_inact = 0;
        }

        // source and sink count as inactive, just in case
        self.buckets[0].num_inact = 1;
        self.buckets[n].num_inact = 1;

        // find correct labels by BFS from sink
        self.queue.clear();
        self.queue.push_back(snk);

        self.largest_act = 0;
        loop {
            while let Some(v) = self.queue.pop_front() {
                let h = self.nodes[v].height + 1;
                for &(e, u) in &self.edges[v] {
                    let udata = &mut self.nodes[u];
                    if udata.height > h && self.flow[e] > F::zero() {
                        udata.height = h;
                        self.queue.push_back(u);
                        // add node to appropriate bucket
                        if udata.excess > F::zero() {
                            // u is active
                            udata.next_act = self.buckets[h].first_act;
                            self.buckets[h].first_act = u;
                            self.largest_act = h;
                            debug_assert!(from_src || self.largest_act < n);
                        } else {
                            // u is inactive
                            self.buckets[h].num_inact += 1;
                        }
                    }
                }
            }
            // possibly start again from the source to find the perfect
            // labels for phase II
            if self.largest_act >= n || !from_src {
                break;
            }
            self.largest_act = n;
            self.queue.push_back(src);
        }
    }

    /// Discharges node `u`.
    ///
    /// This function does a sequence of push and relabel operations for an
    /// active node `u` until its excess reaches 0.
    ///
    /// In phase I, the function may also with `u` having nonzero excess if the
    /// height of u is at least `n`. In this case `u` gets disconnected from the
    /// sink and will not be considered again until phase II.
    #[allow(clippy::many_single_char_names)]
    fn discharge(&mut self, u: usize) {
        let n = self.g.num_nodes();

        loop {
            // The minimal height of the reachable neighbors.
            // If `u` gets relabelled, it gets height `n_neighbor + 1`.
            let mut h_neighbor = 2 * n;
            let h_u = self.nodes[u].height;
            let edges = &self.edges[u];

            // Start at current edge (if any) or restart at beginning.
            let first_iter = self.nodes[u].iter;
            let mut cur = first_iter;

            loop {
                let (e, v) = edges[cur];
                // skip non-admissible edges
                let f = e ^ 1;
                if !self.flow[f].is_zero() {
                    if h_u == self.nodes[v].height + 1 {
                        // Push along edge e
                        let df = min(self.nodes[u].excess, self.flow[f]);

                        debug_assert_eq!(h_u, self.nodes[v].height + 1);
                        debug_assert!(df > F::zero());

                        if self.nodes[v].excess.is_zero() {
                            // sink node becomes active
                            let h = self.nodes[v].height;
                            self.nodes[v].next_act = self.buckets[h].first_act;
                            self.buckets[h].first_act = v;
                            debug_assert!(self.buckets[h].num_inact > 0, "height:{} n:{}", h, n);
                            self.buckets[h].num_inact -= 1;
                        }

                        self.flow[e] += df;
                        self.flow[f] -= df;
                        self.nodes[u].excess -= df;
                        self.nodes[v].excess += df;

                        // check if node is fully discharged
                        if self.nodes[u].excess.is_zero() {
                            // node is inactive now
                            self.buckets[h_u].num_inact += 1;
                            self.largest_act = (0..h_u + 1)
                                .rev()
                                .find(|&h| self.buckets[h].first_act != usize::max_value())
                                .unwrap_or(0);
                            // save current edge
                            self.nodes[u].iter = cur;
                            return;
                        }
                    } else {
                        h_neighbor = h_neighbor.min(self.nodes[v].height);
                    }
                }

                // edge is full, go to next
                cur += 1;
                if cur == edges.len() {
                    break;
                }
            }

            // Update new height for neighbors before `first_edge`.
            self.nodes[u].iter = 0;
            for &(e, v) in &edges[..first_iter] {
                if !self.flow[e ^ 1].is_zero() {
                    h_neighbor = h_neighbor.min(self.nodes[v].height);
                }
            }

            // we ran out of admissible edges but node still has positive excess, relabel node
            if !self.relabel(u, h_neighbor + 1) {
                // node has not got active again (i.e. its label is too high now), stop
                break;
            }
        }
    }

    /// The relabel operation.
    ///
    /// Relabel `u` to height `h_new`.
    ///
    /// The function returns `true` iff the node remains active (i.e. if it
    /// could be discharged again).
    ///
    /// In phase I the function returns `false` if the height of `u` gets at
    /// least `n`. In this case `u` is disconnected from the sink and will not
    /// be discharged again until phase II.
    fn relabel(&mut self, u: usize, h_new: usize) -> bool {
        debug_assert!(self.nodes[u].excess > F::zero());

        // count number of relabellings
        self.cnt_relabel += 1;

        let n = self.g.num_nodes();
        let h_old = self.nodes[u].height;
        debug_assert_eq!(
            h_new,
            self.edges[u]
                .iter()
                .filter_map(|&(e, v)| {
                    if self.flow[e ^ 1] > F::zero() {
                        Some(self.nodes[v].height)
                    } else {
                        None
                    }
                })
                .min()
                .unwrap()
                + 1
        );

        debug_assert!(h_new > h_old);

        // *** The GAP heuristic ***

        // Check if we are still in phase I.
        if h_old < n {
            let mut h_new = h_new;

            // Test whether the node's old bucket is empty now.
            // This would create a gap.
            if self.buckets[h_old].is_empty() {
                // It is empty now, so u is disconnected from the sink.
                // We remove all nodes with higher label from all buckets.
                for h in h_old + 1..n {
                    if self.buckets[h].is_empty() {
                        // all higher buckets are empty, too
                        break;
                    }
                    self.buckets[h].first_act = usize::max_value();
                    self.buckets[h].num_inact = 0;
                }

                // Relabel all nodes to n+1
                //
                // Actually, this is not very fast. We could keep a list of *all*
                // nodes of each height, then this would be possible in O(1)
                // amortized time (each node is relabelled to n+1 at most once).
                //
                // However, because each node can be the cause of the disconnection
                // at most once (when it is relabelled and creates a gap), the
                // running time is at most O(n^2) anyway.
                for node in &mut self.nodes {
                    if h_old < node.height {
                        node.height = n + 1;
                    }
                }

                // The node has now label n + 1.
                h_new = n + 1;
            }

            // This node has now a too large label for phase I.
            // There is no need to discharge the node again. Instead we look for
            // a new active node.
            if h_new >= n {
                debug_assert_eq!(self.largest_act, h_old);

                self.nodes[u].height = h_new;

                // Find largest remaining bucket with an active node.
                //
                // Phase I ends once this reaches 0.
                self.largest_act = (0..h_old + 1)
                    .rev()
                    .find(|&h| self.buckets[h].first_act != usize::max_value())
                    .unwrap_or(0);

                // The current node has been relabelled to n+1, so no further discharge is necessary.
                return false;
            }
        }

        // The node remains active, is must have the largest height now.
        self.nodes[u].height = h_new;
        self.largest_act = h_new;
        true
    }
}

#[cfg(test)]
mod tests {
    use crate::maxflow::pushrelabel;
    use crate::traits::*;
    use crate::{Buildable, Builder, Net};

    #[test]
    fn test_pushrelabel() {
        let mut g = Net::new_builder();
        let mut upper = vec![];
        let s = g.add_node();
        let t = g.add_node();
        let v1 = g.add_node();
        let v2 = g.add_node();
        let v3 = g.add_node();
        let v4 = g.add_node();
        g.add_edge(s, v1);
        upper.push(15);
        g.add_edge(s, v3);
        upper.push(10);
        g.add_edge(v1, v2);
        upper.push(6);
        g.add_edge(v1, v3);
        upper.push(7);
        g.add_edge(v2, t);
        upper.push(5);
        g.add_edge(v2, v4);
        upper.push(2);
        g.add_edge(v3, v2);
        upper.push(11);
        g.add_edge(v3, v4);
        upper.push(4);
        g.add_edge(v4, v2);
        upper.push(4);
        g.add_edge(v4, t);
        upper.push(20);

        let g = g.into_graph();
        let (value, flow, _) = pushrelabel(&g, s, t, |e| upper[e.index()]);

        assert_eq!(value, 11);
        assert!(flow.iter().all(|&(e, f)| f >= 0 && f <= upper[e.index()]));
        assert!(g.nodes().filter(|&u| u != s && u != t).all(|u| g
            .outedges(u)
            .map(|(e, _)| flow[e.index()].1)
            .sum::<isize>()
            == g.inedges(u).map(|(e, _)| flow[e.index()].1).sum::<isize>()));
    }
}

/// Solve the maxflow problem using the push-relabel algorithm.
///
/// The function solves the max flow problem from the source nodes
/// `src` to the sink node `snk` with the given `upper` bounds on
/// the edges.
///
/// The function returns the flow value, the flow on each edge and the
/// nodes in a minimal cut.
pub fn pushrelabel<'a, G, F, Us>(
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
    let mut maxflow = PushRelabel::new(g);
    maxflow.solve(src, snk, upper);
    (
        maxflow.value(),
        g.edges().map(|e| (e, maxflow.flow(e))).collect(),
        maxflow.mincut(),
    )
}
