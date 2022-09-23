/*
 * Copyright (c) 2020, 2021, 2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! A network graph adaptor.
//!
//! A network corresponds to a digraph where each of the digraph's
//! edges is represented by a pair of edges -- the edge and its
//! reverse edge. Hence, the network shares the node set with the
//! underlying graph but has twice the number of edges. Each digraph
//! can be turned into an network.
//!
//! # Example
//!
//! ```
//! use rs_graph::classes;
//! use rs_graph::adapters::Network;
//! use rs_graph::LinkedListGraph;
//! use rs_graph::traits::*;
//!
//! let g = classes::complete_bipartite::<LinkedListGraph>(3, 4);
//! let n = Network::new(&g);
//! assert_eq!(g.num_nodes(), n.num_nodes());
//! assert_eq!(g.num_edges() * 2, n.num_edges());
//! assert!(n.nodes().take(3).all(|u| n.inedges(u).count() == 4));
//! assert!(n.nodes().take(3).all(|u| n.outedges(u).count() == 4));
//! assert!(n.nodes().take(3).all(|u| n.neighs(u).count() == 8));
//! assert!(n.nodes().skip(3).all(|u| n.inedges(u).count() == 3));
//! assert!(n.nodes().skip(3).all(|u| n.outedges(u).count() == 3));
//! assert!(n.nodes().skip(3).all(|u| n.neighs(u).count() == 6));
//!
//! for u in n.nodes().take(3) {
//!     for v in n.nodes().skip(3) {
//!         assert_eq!(n.edges().filter(|&e| (n.src(e), n.snk(e)) == (u, v)).count(), 1);
//!         assert_eq!(n.edges().filter(|&e| (n.snk(e), n.src(e)) == (u, v)).count(), 1);
//!     }
//! }
//!```

use crate::traits::refs::{DirectedRef, FiniteDigraphRef, FiniteGraphRef, IndexGraphRef, UndirectedRef};
use crate::traits::{
    Directed, DirectedEdge, FiniteDigraph, FiniteGraph, GraphIterator, GraphType, IndexGraph, Indexable, Undirected,
};

/// The network graph adaptor.
///
/// It is meant to be used by borrowing the underlying graph.
/// (also see the module description [`adapters::network`](self)).
///
/// ```
/// # use rs_graph::adapters::Network;
/// # use rs_graph::LinkedListGraph;
/// # use rs_graph::classes;
/// let g = classes::cycle::<LinkedListGraph>(5);
/// let n = Network::new(&g);
/// ```
///
/// The network inherits all trait implementations from the underlying graph. In
/// particular, if the underlying graph implements `IndexGraph` then nodes and
/// edges of the network are numbered, too:
///
///   - The `node_id` is the same as in the underlying graph,
///   - the edge with id `i` is mapped to the edges `2*i` (forward edge) and
///     `2*i+1` (backward edge).
#[derive(Copy)]
pub struct Network<'a, G>(&'a G);

impl<'a, G> Clone for Network<'a, G> {
    fn clone(&self) -> Self {
        Network(self.0)
    }
}

/// A network edge.
///
/// This is either the forward or the backward edge of the original edge.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NetworkEdge<E> {
    Forward(E),
    Backward(E),
}

impl<E> NetworkEdge<E>
where
    E: Clone + Eq,
{
    /// Return the *forward* edge corresponding to the given underlying edge.
    pub fn new(e: E) -> Self {
        NetworkEdge::Forward(e)
    }

    /// Return `true` if this is the forward edge.
    pub fn is_forward(&self) -> bool {
        match self {
            NetworkEdge::Forward(_) => true,
            NetworkEdge::Backward(_) => false,
        }
    }

    /// Return `true` if this is the backward edge.
    pub fn is_backward(&self) -> bool {
        !self.is_forward()
    }

    /// Return `true` if `e` is the reverse edge of `self`.
    pub fn is_reverse(&self, e: Self) -> bool {
        use NetworkEdge::*;
        match (self, &e) {
            (Forward(a), Backward(b)) | (Backward(a), Forward(b)) => a == b,
            _ => false,
        }
    }

    /// Return the reverse edge of this edge.
    pub fn reverse(&self) -> Self {
        match self {
            NetworkEdge::Forward(e) => NetworkEdge::Backward(e.clone()),
            NetworkEdge::Backward(e) => NetworkEdge::Forward(e.clone()),
        }
    }

    /// Return the forward edge of `self`.
    ///
    /// If this is already the forward edge then `self` is returned and
    /// `self.reverse()` otherwise.
    pub fn forward(&self) -> Self {
        NetworkEdge::Forward(self.edge())
    }

    /// Return the backward edge of `self`.
    ///
    /// If this is already the backward edge then `self` is returned and
    /// `self.reverse()` otherwise.
    pub fn backward(&self) -> Self {
        NetworkEdge::Backward(self.edge())
    }

    /// Return the edge of the underlying graph.
    pub fn edge(&self) -> E {
        match self {
            NetworkEdge::Forward(e) | NetworkEdge::Backward(e) => e.clone(),
        }
    }
}

/// Graph iterator over all nodes of the [`Network`].
#[derive(Clone)]
pub struct NetworkNodeIt<I>(I);

impl<'a, G, I> GraphIterator<Network<'a, G>> for NetworkNodeIt<I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self, net: &Network<'a, G>) -> Option<Self::Item> {
        self.0.next(net.0)
    }

    fn size_hint(&self, net: &Network<'a, G>) -> (usize, Option<usize>) {
        self.0.size_hint(net.0)
    }

    fn count(self, net: &Network<'a, G>) -> usize {
        self.0.count(net.0)
    }
}

/// Graph iterator over all edges of the [`Network`].
pub struct NetworkEdgeIt<G, I>(I, Option<I::Item>)
where
    I: GraphIterator<G>;

impl<G, I> Clone for NetworkEdgeIt<G, I>
where
    I: GraphIterator<G>,
    I::Item: Clone,
{
    fn clone(&self) -> Self {
        NetworkEdgeIt(self.0.clone(), self.1.clone())
    }
}

impl<'a, G, I> GraphIterator<Network<'a, G>> for NetworkEdgeIt<G, I>
where
    I: GraphIterator<G>,
    I::Item: Clone,
{
    type Item = NetworkEdge<I::Item>;

    fn next(&mut self, net: &Network<'a, G>) -> Option<Self::Item> {
        if let Some(cur) = self.1.take() {
            Some(NetworkEdge::Backward(cur))
        } else if let Some(nxt) = self.0.next(net.0) {
            self.1 = Some(nxt.clone());
            Some(NetworkEdge::Forward(nxt))
        } else {
            None
        }
    }

    fn size_hint(&self, net: &Network<'a, G>) -> (usize, Option<usize>) {
        let (l, u) = self.0.size_hint(net.0);
        (l * 2, u.map(|u| u * 2))
    }

    fn count(self, net: &Network<'a, G>) -> usize {
        2 * self.0.count(net.0) + self.1.map(|_| 1).unwrap_or(0)
    }
}

/// A network edge with direction information.
///
/// This adapter is used by [`NetworkIncidentIt`] to return whether the next edge
/// is outgoing or incoming.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NetworkDirectedEdge<E> {
    Outgoing(E),
    Incoming(E),
}

impl<E> DirectedEdge for NetworkDirectedEdge<E>
where
    E: Clone,
{
    type Edge = E;

    fn is_incoming(&self) -> bool {
        matches!(self, NetworkDirectedEdge::Incoming(..))
    }

    fn edge(&self) -> E {
        match self {
            NetworkDirectedEdge::Incoming(e) | NetworkDirectedEdge::Outgoing(e) => e.clone(),
        }
    }
}

impl<'a, G> Network<'a, G>
where
    G: GraphType<'a>,
{
    /// Create a new network adapter wrapping `g`.
    pub fn new(g: &'a G) -> Self {
        Network(g)
    }

    /// Return a reference to the underlying graph.
    pub fn as_graph(&self) -> &'a G {
        self.0
    }

    /// Return the forward edge corresponding the edge `e` in the underlying graph.
    pub fn from_edge(&self, e: G::Edge) -> NetworkEdge<G::Edge> {
        NetworkEdge::Forward(e)
    }
}

impl<'a, 'g: 'a, G> GraphType<'a> for Network<'g, G>
where
    G: GraphType<'g>,
{
    type Node = G::Node;

    type Edge = NetworkEdge<G::Edge>;
}

impl<'a, 'g: 'a, G> FiniteGraph<'a> for Network<'g, G>
where
    G: FiniteGraph<'g>,
{
    type NodeIt = NetworkNodeIt<G::NodeIt>;

    type EdgeIt = NetworkEdgeIt<G, G::EdgeIt>;

    fn num_nodes(&self) -> usize {
        self.0.num_nodes()
    }

    fn num_edges(&self) -> usize {
        self.0.num_edges() * 2
    }

    fn nodes_iter(&self) -> Self::NodeIt {
        FiniteGraphRef::nodes_iter(self)
    }

    fn edges_iter(&self) -> Self::EdgeIt {
        FiniteGraphRef::edges_iter(self)
    }

    fn enodes(&self, e: Self::Edge) -> (Self::Node, Self::Node) {
        FiniteGraphRef::enodes(self, e)
    }
}

impl<'a, 'g: 'a, G> FiniteDigraph<'a> for Network<'g, G>
where
    G: FiniteDigraph<'g>,
{
    fn src(&self, e: Self::Edge) -> Self::Node {
        FiniteDigraphRef::src(self, e)
    }

    fn snk(&self, e: Self::Edge) -> Self::Node {
        FiniteDigraphRef::snk(self, e)
    }
}

pub struct NetworkNeighIt<G, I>(I, Option<I::Item>)
where
    I: GraphIterator<G>;

impl<'a, G, I> Clone for NetworkNeighIt<G, I>
where
    I: GraphIterator<G>,
    I::Item: Clone,
{
    fn clone(&self) -> Self {
        NetworkNeighIt(self.0.clone(), self.1.clone())
    }
}

impl<'a, G, I, N, E> GraphIterator<Network<'a, G>> for NetworkNeighIt<G, I>
where
    N: Clone,
    E: Clone,
    I: GraphIterator<G, Item = (E, N)>,
{
    type Item = (NetworkEdge<E>, N);

    fn next(&mut self, net: &Network<'a, G>) -> Option<Self::Item> {
        if let Some((e, v)) = self.1.take() {
            Some((NetworkEdge::Backward(e), v))
        } else if let Some((e, v)) = self.0.next(net.0) {
            self.1 = Some((e.clone(), v.clone()));
            Some((NetworkEdge::Forward(e), v))
        } else {
            None
        }
    }

    fn size_hint(&self, net: &Network<'a, G>) -> (usize, Option<usize>) {
        let (l, u) = self.0.size_hint(net.0);
        (l * 2, u.map(|u| u * 2))
    }

    fn count(self, net: &Network<'a, G>) -> usize {
        2 * self.0.count(net.0) + self.1.map(|_| 1).unwrap_or(0)
    }
}

impl<'a, 'g: 'a, G> Undirected<'a> for Network<'g, G>
where
    G: Undirected<'g>,
{
    type NeighIt = NetworkNeighIt<G, G::NeighIt>;

    fn neigh_iter(&self, u: Self::Node) -> Self::NeighIt {
        UndirectedRef::neigh_iter(self, u)
    }
}

#[derive(Clone)]
pub struct NetworkOutIt<I>(I);

impl<'a, G, I, N, D> GraphIterator<Network<'a, G>> for NetworkOutIt<I>
where
    I: GraphIterator<G, Item = (D, N)>,
    D: DirectedEdge,
{
    type Item = (NetworkEdge<D::Edge>, N);

    fn next(&mut self, net: &Network<'a, G>) -> Option<Self::Item> {
        self.0.next(net.0).map(|(e, v)| {
            if e.is_outgoing() {
                (NetworkEdge::Forward(e.edge()), v)
            } else {
                (NetworkEdge::Backward(e.edge()), v)
            }
        })
    }

    fn size_hint(&self, net: &Network<'a, G>) -> (usize, Option<usize>) {
        self.0.size_hint(net.0)
    }

    fn count(self, net: &Network<'a, G>) -> usize {
        self.0.count(net.0)
    }
}

#[derive(Clone)]
pub struct NetworkInIt<I>(I);

impl<'a, G, I, N, D> GraphIterator<Network<'a, G>> for NetworkInIt<I>
where
    I: GraphIterator<G, Item = (D, N)>,
    D: DirectedEdge,
{
    type Item = (NetworkEdge<D::Edge>, N);

    fn next(&mut self, net: &Network<'a, G>) -> Option<Self::Item> {
        self.0.next(net.0).map(|(e, v)| {
            if e.is_incoming() {
                (NetworkEdge::Forward(e.edge()), v)
            } else {
                (NetworkEdge::Backward(e.edge()), v)
            }
        })
    }

    fn size_hint(&self, net: &Network<'a, G>) -> (usize, Option<usize>) {
        self.0.size_hint(net.0)
    }

    fn count(self, net: &Network<'a, G>) -> usize {
        self.0.count(net.0)
    }
}

#[derive(Clone)]
pub struct NetworkIncidentIt<I, T>(I, Option<T>);

impl<'a, G, I, N, D> GraphIterator<Network<'a, G>> for NetworkIncidentIt<I, I::Item>
where
    I: GraphIterator<G, Item = (D, N)>,
    N: Clone,
    D: DirectedEdge + Clone,
{
    type Item = (NetworkDirectedEdge<NetworkEdge<D::Edge>>, N);

    fn next(&mut self, net: &Network<'a, G>) -> Option<Self::Item> {
        if let Some((e, v)) = self.1.take() {
            if e.is_outgoing() {
                Some((NetworkDirectedEdge::Incoming(NetworkEdge::Backward(e.edge())), v))
            } else {
                Some((NetworkDirectedEdge::Outgoing(NetworkEdge::Backward(e.edge())), v))
            }
        } else if let Some((e, v)) = self.0.next(net.0) {
            self.1 = Some((e.clone(), v.clone()));
            if e.is_outgoing() {
                Some((NetworkDirectedEdge::Outgoing(NetworkEdge::Forward(e.edge())), v))
            } else {
                Some((NetworkDirectedEdge::Incoming(NetworkEdge::Forward(e.edge())), v))
            }
        } else {
            None
        }
    }

    fn size_hint(&self, net: &Network<'a, G>) -> (usize, Option<usize>) {
        let (l, u) = self.0.size_hint(net.0);
        (l * 2, u.map(|u| u * 2))
    }

    fn count(self, net: &Network<'a, G>) -> usize {
        2 * self.0.count(net.0) + self.1.map(|_| 1).unwrap_or(0)
    }
}

impl<'a, 'g: 'a, G> Directed<'a> for Network<'g, G>
where
    G: Directed<'g>,
{
    type OutIt = NetworkOutIt<G::IncidentIt>;

    type InIt = NetworkInIt<G::IncidentIt>;

    type IncidentIt = NetworkIncidentIt<G::IncidentIt, (G::DirectedEdge, G::Node)>;

    type DirectedEdge = NetworkDirectedEdge<Self::Edge>;

    fn out_iter(&self, u: Self::Node) -> Self::OutIt {
        DirectedRef::out_iter(self, u)
    }

    fn in_iter(&self, u: Self::Node) -> Self::InIt {
        DirectedRef::in_iter(self, u)
    }

    fn incident_iter(&self, u: Self::Node) -> Self::IncidentIt {
        DirectedRef::incident_iter(self, u)
    }
}

impl<'a, 'g: 'a, G> IndexGraph<'a> for Network<'g, G>
where
    G: IndexGraph<'g>,
{
    fn node_id(&self, u: Self::Node) -> usize {
        self.0.node_id(u)
    }

    fn id2node(&self, id: usize) -> Self::Node {
        IndexGraphRef::id2node(self, id)
    }

    fn edge_id(&self, e: Self::Edge) -> usize {
        (self.0.edge_id(e.edge())) << 1 | (e.is_backward() as usize)
    }

    fn id2edge(&self, id: usize) -> Self::Edge {
        IndexGraphRef::id2edge(self, id)
    }
}

impl<E> Indexable for NetworkEdge<E>
where
    E: Indexable,
{
    fn index(&self) -> usize {
        match self {
            NetworkEdge::Forward(e) => e.index() << 1,
            NetworkEdge::Backward(e) => (e.index() << 1) | 1,
        }
    }
}

impl<'a, G> FiniteGraphRef<'a> for Network<'a, G>
where
    G: FiniteGraph<'a>,
{
    fn nodes_iter(&self) -> Self::NodeIt {
        NetworkNodeIt(self.0.nodes_iter())
    }

    fn edges_iter(&self) -> Self::EdgeIt {
        NetworkEdgeIt(self.0.edges_iter(), None)
    }

    fn enodes(&self, e: Self::Edge) -> (Self::Node, Self::Node) {
        self.0.enodes(e.edge())
    }
}

impl<'a, G> FiniteDigraphRef<'a> for Network<'a, G>
where
    G: FiniteDigraph<'a>,
{
    fn src(&self, e: Self::Edge) -> Self::Node {
        match e {
            NetworkEdge::Forward(e) => self.0.src(e),
            NetworkEdge::Backward(e) => self.0.snk(e),
        }
    }

    fn snk(&self, e: Self::Edge) -> Self::Node {
        match e {
            NetworkEdge::Forward(e) => self.0.snk(e),
            NetworkEdge::Backward(e) => self.0.src(e),
        }
    }
}

impl<'a, G> UndirectedRef<'a> for Network<'a, G>
where
    G: Undirected<'a>,
{
    fn neigh_iter(&self, u: Self::Node) -> Self::NeighIt {
        NetworkNeighIt(self.0.neigh_iter(u), None)
    }
}

impl<'a, G> DirectedRef<'a> for Network<'a, G>
where
    G: 'a + Directed<'a>,
{
    fn out_iter(&self, u: Self::Node) -> Self::OutIt {
        NetworkOutIt(self.0.incident_iter(u))
    }

    fn in_iter(&self, u: Self::Node) -> Self::InIt {
        NetworkInIt(self.0.incident_iter(u))
    }

    fn incident_iter(&self, u: Self::Node) -> Self::IncidentIt {
        NetworkIncidentIt(self.0.incident_iter(u), None)
    }
}

impl<'a, G> IndexGraphRef<'a> for Network<'a, G>
where
    G: IndexGraph<'a>,
{
    fn id2node(&self, id: usize) -> Self::Node {
        self.0.id2node(id)
    }

    fn id2edge(&self, id: usize) -> Self::Edge {
        match id & 1 {
            0 => NetworkEdge::Forward(self.0.id2edge(id >> 1)),
            _ => NetworkEdge::Backward(self.0.id2edge(id >> 1)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Network;
    use crate::classes::*;
    use crate::traits::{Directed, DirectedEdge, FiniteGraph, Undirected};
    use crate::LinkedListGraph;
    use std::collections::HashMap;

    #[test]
    fn test_network() {
        for g in [cycle::<LinkedListGraph>(7), peterson(), hypercube(5)].iter() {
            let n = Network(g);
            assert_eq!(2 * g.num_edges(), n.num_edges());
            for u in g.nodes() {
                assert_eq!(g.neighs(u).count(), n.outedges(u).count());
                assert_eq!(g.neighs(u).count(), n.inedges(u).count());
                assert_eq!(2 * g.neighs(u).count(), n.neighs(u).count());
                assert_eq!(2 * g.incident_edges(u).count(), n.incident_edges(u).count());

                {
                    let mut fwds = g.outedges(u).map(|e| (e, false)).collect::<HashMap<_, _>>();
                    let mut bwds = g.inedges(u).map(|e| (e, false)).collect::<HashMap<_, _>>();
                    for (e, v) in n.outedges(u) {
                        assert!(!e.is_forward() || !fwds.insert((e.edge(), v), true).unwrap_or(true));
                        assert!(!e.is_backward() || !bwds.insert((e.edge(), v), true).unwrap_or(true));
                    }
                    assert!(fwds.values().all(|x| *x));
                    assert!(bwds.values().all(|x| *x));
                }

                {
                    let mut fwds = g.inedges(u).map(|e| (e, false)).collect::<HashMap<_, _>>();
                    let mut bwds = g.outedges(u).map(|e| (e, false)).collect::<HashMap<_, _>>();
                    for (e, v) in n.inedges(u) {
                        assert!(!e.is_forward() || !fwds.insert((e.edge(), v), true).unwrap_or(true));
                        assert!(!e.is_backward() || !bwds.insert((e.edge(), v), true).unwrap_or(true));
                    }
                    assert!(fwds.values().all(|x| *x));
                    assert!(bwds.values().all(|x| *x));
                }

                {
                    let mut fwds = g.neighs(u).map(|e| (e, false)).collect::<HashMap<_, _>>();
                    let mut bwds = g.neighs(u).map(|e| (e, false)).collect::<HashMap<_, _>>();
                    for (e, v) in n.neighs(u) {
                        assert!(!e.is_forward() || !fwds.insert((e.edge(), v), true).unwrap_or(true));
                        assert!(!e.is_backward() || !bwds.insert((e.edge(), v), true).unwrap_or(true));
                    }
                    assert!(fwds.values().all(|x| *x));
                    assert!(bwds.values().all(|x| *x));
                }

                {
                    let mut out_fwds = g.outedges(u).map(|e| (e, false)).collect::<HashMap<_, _>>();
                    let mut out_bwds = g.inedges(u).map(|e| (e, false)).collect::<HashMap<_, _>>();
                    let mut in_fwds = g.inedges(u).map(|e| (e, false)).collect::<HashMap<_, _>>();
                    let mut in_bwds = g.outedges(u).map(|e| (e, false)).collect::<HashMap<_, _>>();
                    for (e, v) in n.incident_edges(u) {
                        if e.is_outgoing() {
                            let e = e.edge();
                            assert!(!e.is_forward() || !out_fwds.insert((e.edge(), v), true).unwrap_or(true));
                            assert!(!e.is_backward() || !out_bwds.insert((e.edge(), v), true).unwrap_or(true));
                        } else {
                            let e = e.edge();
                            assert!(!e.is_forward() || !in_fwds.insert((e.edge(), v), true).unwrap_or(true));
                            assert!(!e.is_backward() || !in_bwds.insert((e.edge(), v), true).unwrap_or(true));
                        }
                    }
                    assert!(out_fwds.values().all(|x| *x));
                    assert!(out_bwds.values().all(|x| *x));
                    assert!(in_fwds.values().all(|x| *x));
                    assert!(in_bwds.values().all(|x| *x));
                }
            }

            {
                let mut fwds = g.edges().map(|e| (e, false)).collect::<HashMap<_, _>>();
                let mut bwds = g.edges().map(|e| (e, false)).collect::<HashMap<_, _>>();
                for e in n.edges() {
                    assert!(!e.is_forward() || !fwds.insert(e.edge(), true).unwrap_or(true));
                    assert!(!e.is_backward() || !bwds.insert(e.edge(), true).unwrap_or(true));
                    assert!(e.is_reverse(e.reverse()));
                    assert!(e.is_forward() || e.reverse().is_forward());
                    assert!(e.is_backward() || e.reverse().is_backward());
                    assert!(!e.is_forward() || e.forward() == e);
                    assert!(!e.is_backward() || e.backward() == e);
                }
                assert!(fwds.values().all(|x| *x));
                assert!(bwds.values().all(|x| *x));
            }
        }
    }
}
