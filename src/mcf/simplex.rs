/*
 * Copyright (c) 2021, 2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! A primal network simplex implementation.

use super::SolutionState;
use crate::adjacencies::Adjacencies;
use crate::collections::NodeVecMap;
use crate::search::dfs;
use crate::traits::{GraphType, IndexDigraph};
use num_traits::{Bounded, FromPrimitive, NumAssign, NumCast, Signed, ToPrimitive, Zero};

type ID = u32;

pub enum Pricing {
    RoundRobin,
    Complete,
    Block,
    MultiplePartial,
}

/// A primal network simplex algorithm.
pub struct NetworkSimplex<'a, G, F> {
    graph: &'a G,

    balances: Vec<F>,
    potentials: Vec<F>,
    subtrees: Vec<ID>,
    parent_edges: Vec<ID>,
    parent_nodes: Vec<ID>,

    prev_preorder: Vec<ID>, // Previous node in preorder node list
    next_preorder: Vec<ID>, // Next node in preorder node list
    last_preorder: Vec<ID>, // Last successor in preorder node list that is a child node

    sources: Vec<ID>,
    sinks: Vec<ID>,
    lower: Vec<F>,
    upper: Vec<F>,
    costs: Vec<F>,
    caps: Vec<F>,
    flows: Vec<F>,
    state: Vec<i8>,

    pub pricing: Pricing,
    current_edge: ID,
    block_size: usize,
    /// The (flow) value to be considered zero. Defaults to `F::zero()`.
    pub zero: F,

    niter: usize,
    solution_state: SolutionState,
    need_new_basis: bool,

    /// The artificial cost value.
    ///
    /// Should be larger than the value of any augmenting cycle. If
    /// `None` (the default) the artificial cost is set to
    /// `(max(max(cost), 0) + 1) * n`, which should be large enough.
    pub artificial_cost: Option<F>,
    /// The infinite flow value.
    ///
    /// Capacities greater than or equal to this are considered
    /// unbounded and flows are considered infinite. The default is
    /// `F::max_value()`. For floating-point types `F::infinity()` can
    /// be used as well.
    pub infinite: F,
}

impl<'a, G, F> NetworkSimplex<'a, G, F>
where
    G: IndexDigraph<'a>,
    F: Bounded + NumCast + NumAssign + PartialOrd + Copy + FromPrimitive + Signed,
{
    pub fn new(g: &'a G) -> Self {
        let mut spx = NetworkSimplex {
            graph: g,
            balances: vec![F::zero(); g.num_nodes()],
            potentials: vec![F::zero(); g.num_nodes() + 1],
            subtrees: vec![0; g.num_nodes() + 1],
            parent_edges: vec![0; g.num_nodes() + 1],
            parent_nodes: vec![0; g.num_nodes() + 1],

            prev_preorder: vec![0; g.num_nodes() + 1],
            next_preorder: vec![0; g.num_nodes() + 1],
            last_preorder: vec![0; g.num_nodes() + 1],

            sources: vec![0; g.num_edges() + g.num_nodes()],
            sinks: vec![0; g.num_edges() + g.num_nodes()],
            lower: vec![F::zero(); g.num_edges() + g.num_nodes()],
            upper: vec![F::zero(); g.num_edges() + g.num_nodes()],
            costs: vec![F::zero(); g.num_edges() + g.num_nodes()],
            caps: vec![F::zero(); g.num_edges() + g.num_nodes()],
            flows: vec![F::zero(); g.num_edges() + g.num_nodes()],
            state: vec![0; g.num_edges() + g.num_nodes()],

            pricing: Pricing::Block,
            current_edge: 0,
            block_size: 0,
            zero: F::zero(),

            niter: 0,
            solution_state: SolutionState::Unknown,
            need_new_basis: true,

            artificial_cost: None,
            infinite: F::max_value(),
        };
        spx.init();
        spx
    }

    pub fn as_graph(&self) -> &'a G {
        self.graph
    }

    pub fn balance(&self, u: <G as GraphType<'a>>::Node) -> F {
        self.balances[self.graph.node_id(u)]
    }

    pub fn set_balance(&mut self, u: <G as GraphType<'a>>::Node, balance: F) {
        self.need_new_basis = true;
        self.balances[self.graph.node_id(u)] = balance;
    }

    pub fn set_balances<B>(&mut self, balance: B)
    where
        B: Fn(<G as GraphType<'a>>::Node) -> F,
    {
        for uid in 0..self.as_graph().num_nodes() {
            let u = self.as_graph().id2node(uid);
            self.set_balance(u, (balance)(u));
        }
    }

    pub fn lower(&self, e: <G as GraphType<'a>>::Edge) -> F {
        self.lower[self.graph.edge_id(e)]
    }

    pub fn set_lower(&mut self, e: <G as GraphType<'a>>::Edge, lb: F) {
        self.need_new_basis = true;
        self.lower[self.graph.edge_id(e)] = lb;
    }

    pub fn set_lowers<L>(&mut self, lower: L)
    where
        L: Fn(<G as GraphType<'a>>::Edge) -> F,
    {
        for eid in 0..self.as_graph().num_edges() {
            let e = self.as_graph().id2edge(eid);
            self.set_lower(e, (lower)(e));
        }
    }

    pub fn upper(&self, e: <G as GraphType<'a>>::Edge) -> F {
        self.upper[self.graph.edge_id(e)]
    }

    pub fn set_uppers<U>(&mut self, upper: U)
    where
        U: Fn(<G as GraphType<'a>>::Edge) -> F,
    {
        for eid in 0..self.as_graph().num_edges() {
            let e = self.as_graph().id2edge(eid);
            self.set_upper(e, (upper)(e));
        }
    }

    pub fn set_upper(&mut self, e: <G as GraphType<'a>>::Edge, ub: F) {
        self.need_new_basis = true;
        self.upper[self.graph.edge_id(e)] = ub;
    }

    pub fn cost(&self, e: <G as GraphType<'a>>::Edge) -> F {
        self.costs[self.graph.edge_id(e)]
    }

    pub fn set_cost(&mut self, e: <G as GraphType<'a>>::Edge, cost: F) {
        self.costs[self.graph.edge_id(e)] = cost;
    }

    pub fn set_costs<C>(&mut self, cost: C)
    where
        C: Fn(<G as GraphType<'a>>::Edge) -> F,
    {
        for eid in 0..self.as_graph().num_edges() {
            let e = self.as_graph().id2edge(eid);
            self.set_cost(e, (cost)(e));
        }
    }

    /// Return the value of the latest computed flow value.
    pub fn value(&self) -> F {
        let mut v = F::zero();
        for e in self.graph.edges() {
            v += self.flow(e) * self.costs[self.graph.edge_id(e)];
        }
        v
    }

    /// The flow of an Edge.
    pub fn flow(&self, a: <G as GraphType<'a>>::Edge) -> F {
        let eid = self.graph.edge_id(a);
        self.flows[eid] + self.lower[eid]
    }

    /// Solve the min-cost-flow problem.
    pub fn solve(&mut self) -> SolutionState {
        self.niter = 0;
        self.solution_state = SolutionState::Unknown;

        // check trivial cases
        if self.graph.num_nodes().is_zero() {
            self.solution_state = SolutionState::Optimal;
            return self.solution_state;
        }

        if self.graph.num_edges().is_zero() {
            // check if all balances are zero, that's the only way to be feasible
            self.solution_state = if self.balances.iter().all(Zero::is_zero) {
                SolutionState::Optimal
            } else {
                SolutionState::Infeasible
            };
            return self.solution_state;
        }

        self.initialize_pricing();

        if self.need_new_basis && !self.prepare_initial_basis() {
            self.solution_state = SolutionState::Infeasible;
            return self.solution_state;
        }

        self.initialize_node_potentials();

        // heuristic initial pivot
        if !self.compute_initial_pivots() {
            self.solution_state = SolutionState::Unbounded;
            return self.solution_state;
        }

        loop {
            self.niter += 1;
            if let Some(eid) = self.find_entering_edge() {
                if !self.augment_cycle(eid) {
                    self.solution_state = SolutionState::Unbounded;
                    return self.solution_state;
                }
            } else {
                break;
            }
        }

        self.solution_state = if self.check_feasibility() {
            SolutionState::Optimal
        } else {
            SolutionState::Infeasible
        };

        self.solution_state
    }

    /// Return the solution state of the latest computation.
    pub fn solution_state(&self) -> SolutionState {
        if self.need_new_basis {
            SolutionState::Unknown
        } else {
            self.solution_state
        }
    }

    fn init(&mut self) {
        let m = self.graph.num_edges();
        // Initialize edges
        for eid in 0..m {
            self.sources[eid] = NumCast::from(self.graph.node_id(self.graph.src(self.graph.id2edge(eid)))).unwrap();
            self.sinks[eid] = NumCast::from(self.graph.node_id(self.graph.snk(self.graph.id2edge(eid)))).unwrap();
        }

        // The artificial edges will be initialized when the initial
        // basis is prepared.
    }

    pub fn num_iterations(&self) -> usize {
        self.niter
    }

    fn initialize_pricing(&mut self) {
        match self.pricing {
            Pricing::RoundRobin => self.current_edge = 0,
            Pricing::Complete => (),
            Pricing::Block => {
                self.current_edge = 0;
                // The following code is analogous to my Pascal implementation.
                // We could also use
                self.block_size = ((self.graph.num_edges() as f64).sqrt() * 0.5)
                    .round()
                    .to_usize()
                    .unwrap()
                    .max(10);
            }
            Pricing::MultiplePartial => todo!(),
        }
    }

    fn prepare_initial_basis(&mut self) -> bool {
        let n = self.graph.num_nodes();
        let m = self.graph.num_edges() * 2;
        // The artificial node is always the root of the basis tree
        let uid = self.graph.num_nodes();

        // modified balances of each node
        let mut balances = self.balances.clone();
        balances.push(F::zero());

        // compute the cost value for the artificial nodes
        let artificial_cost = self.artificial_cost.unwrap_or_else(|| {
            let mut value = F::zero();
            for &c in &self.costs[0..self.graph.num_edges()] {
                if c > value {
                    value = c;
                }
            }
            F::from(n).unwrap() * (F::one() + value)
        });

        self.subtrees[uid] = n as ID + 1;
        self.parent_edges[uid] = ID::max_value();
        self.parent_nodes[uid] = ID::max_value();

        self.prev_preorder[uid] = ID::max_value();
        self.next_preorder[uid] = 0;
        self.last_preorder[uid] = n as ID - 1;

        // Initial flow on all non-artificial edges is at lower or upper bound depending on the cost
        for e in self.graph.edges() {
            let eid = self.graph.edge_id(e);
            // We set the initial flow on edges with non-negative costs at the lower bound ...
            let cap = self.upper[eid] - self.lower[eid];

            // The current edge is always infeasible.
            if cap < self.zero {
                return false;
            }

            let flw: F;
            if self.costs[eid] >= F::zero() {
                self.state[eid] = 1;
                flw = F::zero();
            } else {
                self.state[eid] = -1;
                flw = cap;
            }

            self.flows[eid] = flw;
            self.caps[eid] = cap;

            // Update artificial balances
            let flw = flw + self.lower[eid];
            balances[self.graph.node_id(self.graph.src(e))] -= flw;
            balances[self.graph.node_id(self.graph.snk(e))] += flw;
        }

        // The initial basis consists of the artificial edges only
        for vid in 0..n {
            self.subtrees[vid] = 1;
            // Set the initial flow on the artificial edges
            let eid = m + vid * 2;
            let fid; // the parent edge, oriented from the artificial node (the root) to v
            let b; // the balance / initial flow on the artificial edge
            if balances[vid] >= F::zero() {
                fid = eid ^ 1;
                b = balances[vid];
                self.costs[eid / 2] = F::zero();
                // this edge is oriented from v the artificial node
                self.sources[eid / 2] = ID::from_usize(eid - m).unwrap();
                self.sinks[eid / 2] = ID::from_usize(n).unwrap();
            } else {
                fid = eid;
                b = -balances[vid];
                self.costs[eid / 2] = artificial_cost;
                // this edge is oriented from the artificial node to v
                self.sources[eid / 2] = ID::from_usize(n).unwrap();
                self.sinks[eid / 2] = ID::from_usize(eid - m).unwrap();
            }

            self.caps[eid / 2] = self.infinite;
            self.flows[eid / 2] = b;
            self.state[eid / 2] = 0;

            self.parent_nodes[vid] = uid as ID;
            self.parent_edges[vid] = fid as ID;
            self.prev_preorder[vid] = if vid > 0 { vid as ID - 1 } else { n as ID };
            self.next_preorder[vid] = if vid + 1 < n { vid as ID + 1 } else { ID::max_value() };
            self.last_preorder[vid] = vid as ID; // all subtrees are empty
        }

        self.need_new_basis = false;

        true
    }

    /// Heuristic initial pivots
    ///
    /// Returns `false` if unboundedness has been detected and `true` otherwise.
    fn compute_initial_pivots(&mut self) -> bool {
        let n = self.graph.num_nodes();
        let mut supply_nodes = Vec::new();
        let mut demand_nodes = Vec::new();
        let mut total_supply = F::zero();
        for uid in 0..n {
            let b = self.balances[uid];
            if b > F::zero() {
                total_supply += b;
                supply_nodes.push(uid);
            } else if b < F::zero() {
                demand_nodes.push(uid);
            }
        }

        // No supply -> no flow
        if total_supply.is_zero() {
            return true;
        }

        let edges: Vec<usize> = if supply_nodes.len() == 1 && demand_nodes.len() == 1 {
            // special case: exactly one source and one sink.
            // do a DFS from sink to source
            let s = self.graph.id2node(supply_nodes[0]);
            let t = self.graph.id2node(demand_nodes[0]);
            let mut edges = Vec::new();
            for (_, e) in dfs::start_with_data(
                self.graph
                    .incoming()
                    .filter(|&(e, _)| self.caps[self.graph.edge_id(e)] >= total_supply && self.graph.snk(e) != s),
                t,
                (NodeVecMap::new(self.graph), Vec::new()),
            ) {
                edges.push(self.graph.edge_id(e));
            }
            edges
        } else {
            // Find the minimal cost incoming edge for each demand node
            demand_nodes
                .iter()
                .filter_map(|&vid| {
                    self.graph
                        .inedges(self.graph.id2node(vid))
                        .map(|(e, _)| self.graph.edge_id(e))
                        .min_by(|&eid, &fid| self.costs[eid].partial_cmp(&self.costs[fid]).unwrap())
                })
                .map(|eid| eid)
                .collect()
        };

        // Perform heuristic initial pivots
        for eid in edges {
            if self.reduced_cost(eid) >= F::zero() {
                continue;
            }
            let eid = self.oriented_edge(eid);
            if !self.augment_cycle(eid) {
                return false;
            }
        }

        true
    }

    fn initialize_node_potentials(&mut self) {
        let rootid = self.graph.num_nodes();
        self.potentials[rootid] = F::zero();

        let mut uid = self.next_preorder[rootid] as usize;
        while uid != ID::max_value() as usize {
            let eid = self.parent_edges[uid] as usize;
            let vid = self.parent_nodes[uid] as usize;
            self.potentials[uid] = self.potentials[vid] + oriented_flow(eid, self.costs[eid as usize / 2]);
            uid = self.next_preorder[uid] as usize;
        }
    }

    fn update_node_potentials(&mut self, uentering: usize) {
        let eid = self.parent_edges[uentering] as usize;
        let vid = self.parent_nodes[uentering] as usize;
        let sigma = self.potentials[vid] - self.potentials[uentering] + oriented_flow(eid, self.costs[eid / 2]);
        let uend = self.next_preorder[self.last_preorder[uentering] as usize] as usize;
        let mut uid = uentering;
        while uid != uend {
            self.potentials[uid] += sigma;
            uid = self.next_preorder[uid] as usize;
        }
    }

    fn augment_cycle(&mut self, e_in: ID) -> bool {
        let e_in = e_in as usize;

        // e = (u,v)
        let (mut u_in, mut v_in) = if (e_in & 1) == 0 {
            (self.sources[e_in / 2] as usize, self.sinks[e_in / 2] as usize)
        } else {
            (self.sinks[e_in / 2] as usize, self.sources[e_in / 2] as usize)
        };

        // Obtain free capacity on entering edge
        let mut d = self.caps[e_in / 2];

        // Compute maximal flow augmentation value and determine base-leaving-edge.
        let mut v_out = None;
        let mut e_out_fwd = true;
        let mut uid = u_in;
        let mut vid = v_in;
        while uid != vid {
            let fwd = self.subtrees[uid] < self.subtrees[vid];
            // Edges on the side of u are in forward direction on the cycle
            // Edges on the side of v are in backward direction on the cycle
            let nodeid = if fwd { uid } else { vid } as usize;

            let f = self.parent_edges[nodeid] as usize;

            let flw = if ((f & 1) != 0) == fwd {
                self.flows[f / 2]
            } else if self.caps[f / 2] != self.infinite {
                self.caps[f / 2] - self.flows[f / 2]
            } else {
                self.infinite
            };

            if flw < d {
                d = flw;
                v_out = Some(nodeid);
                e_out_fwd = fwd;
            }

            if fwd {
                uid = self.parent_nodes[uid] as usize
            } else {
                vid = self.parent_nodes[vid] as usize
            };
        }

        if d >= self.infinite {
            return false;
        }

        // vid is the common ancestor, i.e. the "top-most" node on the
        // cycle in the basis tree.
        let ancestorid = vid;

        // Augment the flow one the basis entering edge.
        self.flows[e_in / 2] = if self.state[e_in / 2] == 1 {
            d
        } else {
            self.caps[e_in / 2] - d
        };

        // Check if e_in stays in non-basis
        let v_out = if let Some(m) = v_out {
            m
        } else {
            // switch bound
            self.state[e_in / 2] = -self.state[e_in / 2];
            // update flow on cycle
            let mut uid = u_in;
            let mut vid = v_in;
            while uid != ancestorid {
                let f = self.parent_edges[uid] as usize;
                self.flows[f / 2] += oriented_flow(f, d);
                uid = self.parent_nodes[uid] as usize;
            }
            while vid != ancestorid {
                let f = self.parent_edges[vid] as usize;
                self.flows[f / 2] -= oriented_flow(f, d);
                vid = self.parent_nodes[vid] as usize;
            }
            // done
            return true;
        };
        let u_out = self.parent_nodes[v_out] as usize;

        // ************************************************************
        // update the basis tree
        // ************************************************************

        self.state[e_in / 2] = 0; // e_in enters the basis

        // The basis leaving edge e_in should be on the side of u, so possibly reverse e_in.
        let e_in = if e_out_fwd {
            let e_out = self.parent_edges[v_out] as usize;
            self.state[e_out / 2] = if (e_out & 1) == 0 { -1 } else { 1 };
            e_in
        } else {
            let e_out = self.parent_edges[v_out] as usize;
            self.state[e_out / 2] = if (e_out & 1) == 0 { 1 } else { -1 };
            // swap this edge
            d = -d;
            std::mem::swap(&mut u_in, &mut v_in);
            e_in ^ 1
        };

        let mut uid = u_in;
        let mut vid = v_in;
        let orig_v_out_last = self.last_preorder[v_out];
        let orig_v_out_prev = self.prev_preorder[v_out];
        let orig_v_in_last = self.last_preorder[v_in];
        let orig_ancestor_last = self.last_preorder[ancestorid];

        // Special case: entering and leaving edges are parallel
        if u_in == v_out && v_in == self.parent_nodes[v_out] as usize {
            let fid = self.parent_edges[v_out] as usize;
            self.flows[fid / 2] += oriented_flow(fid, d);
            self.parent_edges[u_in] = e_in as ID ^ 1;
            self.update_node_potentials(u_in);
            return true;
        }

        // All subtree sizes from v up to the ancestor are increased.
        // The flow on these edges is reduced.
        let subtreediff = self.subtrees[v_out];
        let mut childsubtree = 0;

        // Traverse all nodes u from u_in .. v_out. At the beginning
        // of each iteration
        //
        // - there are two successive nodes (w, u, v)
        // - u_last is the original last[u]
        // - u_prev is the original prev[u]
        // - e_add = (u, v) the edge to be added
        //
        // In each iteration
        //
        // - the edge (u, v) is added to basis.
        // - the edge (w, u) is removed from basis.
        // - the flow on (w, u) is increased
        // - the preorder list is updated
        // - EXCEPTION: last[v] might not be correct after each iteration
        let mut e_add = e_in;
        let mut orig_u_last = self.last_preorder[u_in] as usize;
        let mut orig_u_prev = self.prev_preorder[u_in] as usize;
        while vid != v_out {
            let wid = self.parent_nodes[uid] as usize;
            let w_last = self.last_preorder[wid] as usize;
            let w_prev = self.prev_preorder[wid] as usize;

            // First remove the (original) subtree of u from its parent w.
            // This need an update of last[w] if u was the "last" subtree of w
            if w_last == orig_u_last {
                self.last_preorder[wid] = orig_u_prev as ID;
            }

            // Remove u (and its subtree) from the preorder list ...
            let u_last = self.last_preorder[uid] as usize;
            let u_prev = self.prev_preorder[uid] as usize;
            self.next_preorder[u_prev] = self.next_preorder[u_last];
            if self.next_preorder[u_last] != ID::max_value() {
                self.prev_preorder[self.next_preorder[u_last] as usize] = u_prev as ID;
            }

            // Next attach u below v (between v and self.next_preorder[v])
            self.prev_preorder[uid] = vid as ID;
            self.next_preorder[u_last] = self.next_preorder[vid];
            if self.next_preorder[vid] != ID::max_value() {
                self.prev_preorder[self.next_preorder[vid] as usize] = u_last as ID;
            }
            self.next_preorder[vid] = uid as ID;

            let e_del = self.parent_edges[uid] as usize;
            self.parent_edges[uid] = e_add as ID ^ 1; // the edge is reversed to (v -> u)
            self.parent_nodes[uid] = vid as ID;

            self.flows[e_del / 2] += oriented_flow(e_del, d);

            // What is currently below u stays below u but is not added again
            // Everything else is added
            let usubtree = self.subtrees[uid];
            self.subtrees[uid] = subtreediff - childsubtree;
            childsubtree = usubtree;

            // Go up one edge.
            vid = uid;
            uid = wid;
            orig_u_last = w_last;
            orig_u_prev = w_prev;
            e_add = e_del;
        }

        // The last[v] information for nodes v_out .. u_in may be wrong, because
        // we added more nodes to their subtrees. We fix this now.
        {
            // v_out itself is actually correct because nothing has
            // been added below v_out, so we start with its (new)
            // parent.
            let mut vid = self.parent_nodes[v_out] as usize;
            let mut last = self.last_preorder[v_out];
            while vid != v_in {
                // Only nodes that had nothing below them must be
                // updated because now their subtree is not empty
                // anymore.
                if self.last_preorder[vid] as usize == vid {
                    self.last_preorder[vid] = last;
                } else {
                    last = self.last_preorder[vid];
                }
                vid = self.parent_nodes[vid] as usize;
            }
        }

        // Now update the nodes from u_out ... ancestor.
        //
        // These nodes may have lost a subtree. They must be updated
        // if and only if their last node was last[v_out].
        {
            let mut uid = u_out;
            while uid != ancestorid {
                if self.last_preorder[uid] == orig_v_out_last {
                    self.last_preorder[uid] = orig_v_out_prev;
                }
                // Update the flow and the subtree size.
                let eid = self.parent_edges[uid] as usize;
                self.flows[eid / 2] += oriented_flow(eid, d);
                self.subtrees[uid] -= subtreediff;
                uid = self.parent_nodes[uid] as usize;
            }
        }

        // Now update the nodes from v_in ... ancestor.
        //
        // These nodes may have got new nodes in their subtree. They
        // must be updated if and only if their last node was
        // last[v_in] and last[v_in] has changed.
        {
            let u_in_last = self.last_preorder[u_in];
            let bad_last = if v_in == orig_v_in_last as usize {
                orig_v_in_last
            } else {
                ID::max_value() // no not change if last[v_in] has not changed
            };
            let mut vid = v_in;
            while vid != ancestorid {
                if self.last_preorder[vid] == bad_last {
                    self.last_preorder[vid] = u_in_last;
                }
                let eid = self.parent_edges[vid] as usize;
                self.flows[eid / 2] -= oriented_flow(eid, d);
                self.subtrees[vid] += subtreediff;
                vid = self.parent_nodes[vid] as usize;
            }
        }

        // Finally it remains to update the nodes from ancestor
        // upwards.

        let (old, new) = if u_out == ancestorid && orig_ancestor_last == orig_v_out_last {
            // This is the only case in which ancestor may have lost a
            // subtree.
            if orig_v_out_prev as usize == v_in {
                self.last_preorder[ancestorid] = orig_ancestor_last;
                (orig_v_out_last, self.last_preorder[u_in])
            } else {
                self.last_preorder[ancestorid] = orig_ancestor_last;
                (orig_v_out_last, orig_v_out_prev)
            }
        } else if orig_ancestor_last == orig_v_out_last {
            (orig_v_out_last, orig_v_out_prev)
        } else if orig_ancestor_last == orig_v_in_last {
            if u_out == ancestorid {
                // Reset last[ancestor] because it has already been changed.
                self.last_preorder[ancestorid] = orig_ancestor_last;
            }
            (orig_v_in_last, self.last_preorder[v_in])
        } else {
            (ID::max_value(), ID::max_value())
        };

        if old != ID::max_value() {
            let mut uid = ancestorid;
            while uid != ID::max_value() as usize && self.last_preorder[uid] == old {
                self.last_preorder[uid] = new;
                uid = self.parent_nodes[uid] as usize;
            }
        }

        // Finally update the node potentials for the changed subtree
        self.update_node_potentials(u_in);

        true
    }

    fn check_feasibility(&mut self) -> bool {
        self.flows[self.graph.num_edges()..].iter().all(|&x| x <= self.zero)
    }

    fn find_entering_edge(&mut self) -> Option<ID> {
        match self.pricing {
            Pricing::RoundRobin => self.round_robin_pricing(),
            Pricing::Complete => self.complete_pricing(),
            Pricing::Block => self.block_pricing(),
            Pricing::MultiplePartial => self.multiple_partial_pricing(),
        }
    }

    fn round_robin_pricing(&mut self) -> Option<ID> {
        let mut eid = self.current_edge as usize;
        loop {
            if self.reduced_cost(eid) < F::zero() {
                self.current_edge = eid as ID;
                return Some(self.oriented_edge(eid));
            }
            eid = (eid + 1) % self.graph.num_edges();
            if eid == self.current_edge as usize {
                return None;
            }
        }
    }

    fn complete_pricing(&mut self) -> Option<ID> {
        let mut min_cost = F::zero();
        let mut min_edge = None;
        for eid in 0..self.graph.num_edges() {
            let c = self.reduced_cost(eid);
            if c < min_cost {
                min_cost = c;
                min_edge = Some(eid);
            }
        }

        min_edge.map(|eid| self.oriented_edge(eid))
    }

    fn block_pricing(&mut self) -> Option<ID> {
        let mut end = self.graph.num_edges();
        let mut eid = self.current_edge as usize % end;
        let mut min_edge = None;
        let mut min_cost = F::zero();
        let mut m = (eid + self.block_size).min(end);
        let mut cnt = self.block_size.min(end);

        loop {
            while eid < m {
                let c = self.reduced_cost(eid);
                if c < min_cost {
                    min_cost = c;
                    min_edge = Some(eid);
                }
                cnt -= 1;
                eid += 1;
            }

            if cnt == 0 {
                // reached regular end of the current block, start new block
                m = (eid + self.block_size).min(end);
                cnt = self.block_size.min(end);
            } else if eid != self.current_edge as usize {
                // reached non-regular end of the final block, start
                // from the beginning
                end = self.current_edge as usize;
                eid = 0;
                m = cnt.min(end);
                continue;
            }

            if let Some(enteringid) = min_edge {
                self.current_edge = eid as ID;
                return Some(self.oriented_edge(enteringid));
            }

            if eid == self.current_edge as usize {
                return None;
            }
        }
    }

    fn multiple_partial_pricing(&mut self) -> Option<ID> {
        todo!()
    }

    fn reduced_cost(&self, eid: usize) -> F {
        unsafe {
            F::from(*self.state.get_unchecked(eid)).unwrap()
                * (*self.costs.get_unchecked(eid)
                    - *self.potentials.get_unchecked(*self.sinks.get_unchecked(eid) as usize)
                    + *self.potentials.get_unchecked(*self.sources.get_unchecked(eid) as usize))
        }
    }

    fn oriented_edge(&self, eid: usize) -> ID {
        let eid = if self.state[eid] == 1 { eid * 2 } else { (eid * 2) | 1 };
        eid as ID
    }
}

fn oriented_flow<F>(eid: usize, d: F) -> F
where
    F: NumAssign + NumCast,
{
    (F::one() - F::from((eid & 1) * 2).unwrap()) * d
}

/// Solve a min-cost-flow problem with a network simplex algorithm.
///
/// The function returns the objective value and the optimal flow.
pub fn network_simplex<'a, G, F, Bs, Ls, Us, Cs>(
    g: &'a G,
    balances: Bs,
    lower: Ls,
    upper: Us,
    costs: Cs,
) -> Option<(F, Vec<(G::Edge, F)>)>
where
    G: IndexDigraph<'a>,
    F: NumAssign + NumCast + FromPrimitive + Ord + Signed + Bounded + Copy,
    Bs: Fn(G::Node) -> F,
    Ls: Fn(G::Edge) -> F,
    Us: Fn(G::Edge) -> F,
    Cs: Fn(G::Edge) -> F,
{
    let mut spx = NetworkSimplex::new(g);
    spx.set_balances(balances);
    spx.set_lowers(lower);
    spx.set_uppers(upper);
    spx.set_costs(costs);
    if spx.solve() == SolutionState::Optimal {
        Some((spx.value(), g.edges().map(|e| (e, spx.flow(e))).collect()))
    } else {
        None
    }
}
