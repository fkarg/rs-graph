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

//! A linked-list based graph implementation.
//!
//! This is an efficient default implementation of a graph.
//!
//! `LinkedListGraph` provides directed arc access (i.e. implements
//! `Network`).
//!
//! Node and edge data are stored in an array (Vec), nodes and edges
//! are identified by indices. Forward edges have even indices,
//! backward edges have the odd indices directly following the
//! corresponding forward edge. The external edge index is the edge
//! index shifted right by one bit (the lsb is removed), but a user
//! should not rely on that. The node and edge indices can be
//! retrieved using the `IndexGraph` and `IndexNetwork` traits.
//!
//! `LinkedListGraph` takes additional parameters for node, edge
//! and biedge attributes, thus, it implements `NodeAttributes`,
//! `EdgeAttributes` and `BiEdgeAttributes`.
//!
//! `LinkedListGraph` can be constructed (it implements `Builder`),
//! but nodes and edges cannot be removed.

use crate::attributes::{EdgeAttributes, NodeAttributes};
use crate::builder::{Buildable, Builder};
use crate::traits::{Directed, DirectedEdge, FiniteDigraph, FiniteGraph, GraphType, Undirected};
use crate::traits::{GraphIterator, IndexGraph, Indexable};

use crate::num::iter::{range, range_step, Range, RangeStep};
use crate::num::traits::{PrimInt, Unsigned};

use std::fmt;
use std::hash::{Hash, Hasher};

#[cfg(feature = "serialize")]
use serde_derive::{Deserialize, Serialize};

/// Node of a linked list graph.
///
/// This is basically a newtype of the node index.
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub struct Node<ID = u32>(ID)
where
    ID: PrimInt + Unsigned;

impl<ID> fmt::Display for Node<ID>
where
    ID: PrimInt + Unsigned + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl<ID> Indexable for Node<ID>
where
    ID: PrimInt + Unsigned,
{
    fn index(&self) -> usize {
        self.0.to_usize().unwrap()
    }
}

/// Edge of a linked list graph.
///
/// This is basically a newtype of the *arc* index. Note that
/// `e == g.reverse(e)`.
#[derive(Eq, Clone, Copy, Debug)]
pub struct Edge<ID = u32>(ID)
where
    ID: PrimInt + Unsigned;

impl<ID> PartialEq for Edge<ID>
where
    ID: PrimInt + Unsigned,
{
    fn eq(&self, other: &Self) -> bool {
        (self.0 >> 1) == (other.0 >> 1)
    }
}

impl<ID> fmt::Display for Edge<ID>
where
    ID: PrimInt + Unsigned + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            if (self.0 & ID::one()).is_zero() { "+" } else { "-" },
            self.0 >> 1
        )
    }
}

impl<ID> Hash for Edge<ID>
where
    ID: PrimInt + Unsigned + Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.0 >> 1).hash(state)
    }
}

impl<ID> Indexable for Edge<ID>
where
    ID: PrimInt + Unsigned,
{
    fn index(&self) -> usize {
        (self.0 >> 1).to_usize().unwrap()
    }
}

impl<ID> DirectedEdge for Edge<ID>
where
    ID: PrimInt + Unsigned,
{
    type Edge = Self;

    fn is_incoming(&self) -> bool {
        !(self.0 & ID::one()).is_zero()
    }

    fn edge(&self) -> Self::Edge {
        *self
    }
}

/// The linked list based graph data structure.
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct LinkedListGraph<ID = u32, N = (), E = ()> {
    /// List of nodes.
    nodes: Vec<NodeData<ID, N>>,
    /// List of edges.
    edges: Vec<EdgeData<ID, E>>,
}

/// Data for a node in a linked list graph.
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
struct NodeData<ID, N> {
    /// The first outgoing adjacent edge.
    first_out: ID,
    /// The first incoming adjacent edge.
    first_in: ID,
    /// Associated node attributes.
    attrs: N,
}

/// Data for an edge in the linked list graph.
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
struct EdgeData<ID, E> {
    /// The sink node.
    snk: ID,
    /// The next arc adjacent to the source node.
    next: ID,
    /// Associated edge attributes.
    eattrs: E,
}

/// A graph iterator over all nodes of a linked list graph.
#[derive(Clone)]
pub struct NodeIt<ID>(Range<ID>);

impl<'a, ID, N: 'a, E: 'a> GraphIterator<LinkedListGraph<ID, N, E>> for NodeIt<ID>
where
    ID: 'a + PrimInt + Unsigned,
{
    type Item = Node<ID>;

    fn next(&mut self, _g: &LinkedListGraph<ID, N, E>) -> Option<Self::Item> {
        Iterator::next(&mut self.0).map(Node)
    }

    fn size_hint(&self, _g: &LinkedListGraph<ID, N, E>) -> (usize, Option<usize>) {
        Iterator::size_hint(&self.0)
    }

    fn count(self, _g: &LinkedListGraph<ID, N, E>) -> usize {
        Iterator::count(self.0)
    }
}

/// An iterator over all edges of a linked list graph.
///
/// This iterator only returns the forward edges.
#[derive(Clone)]
pub struct EdgeIt<ID>(RangeStep<ID>);

impl<'a, ID, N: 'a, E: 'a> GraphIterator<LinkedListGraph<ID, N, E>> for EdgeIt<ID>
where
    ID: 'a + PrimInt + Unsigned,
{
    type Item = Edge<ID>;

    fn next(&mut self, _g: &LinkedListGraph<ID, N, E>) -> Option<Self::Item> {
        Iterator::next(&mut self.0).map(Edge)
    }

    fn size_hint(&self, _g: &LinkedListGraph<ID, N, E>) -> (usize, Option<usize>) {
        Iterator::size_hint(&self.0)
    }

    fn count(self, _g: &LinkedListGraph<ID, N, E>) -> usize {
        Iterator::count(self.0)
    }
}

impl<'a, ID, N, E> GraphType<'a> for LinkedListGraph<ID, N, E>
where
    ID: 'a + PrimInt + Unsigned,
{
    type Node = Node<ID>;
    type Edge = Edge<ID>;
}

impl<'a, ID, N, E> FiniteGraph<'a> for LinkedListGraph<ID, N, E>
where
    ID: 'a + PrimInt + Unsigned,
{
    type NodeIt = NodeIt<ID>;
    type EdgeIt = EdgeIt<ID>;

    fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    fn num_edges(&self) -> usize {
        self.edges.len() / 2
    }

    fn nodes_iter(&self) -> Self::NodeIt {
        NodeIt(range(ID::zero(), ID::from(self.num_nodes()).unwrap()))
    }

    fn edges_iter(&self) -> Self::EdgeIt {
        EdgeIt(range_step(
            ID::zero(),
            ID::from(self.edges.len()).unwrap(),
            ID::from(2).unwrap(),
        ))
    }

    fn enodes(&self, e: Self::Edge) -> (Self::Node, Self::Node) {
        let eid = e.0.to_usize().unwrap();
        (Node(self.edges[eid | 1].snk), Node(self.edges[eid & !1].snk))
    }
}

impl<'a, ID, N, E> FiniteDigraph<'a> for LinkedListGraph<ID, N, E>
where
    ID: 'a + PrimInt + Unsigned,
{
    fn src(&self, e: Self::Edge) -> Self::Node {
        Node(self.edges[e.0.to_usize().unwrap() | 1].snk)
    }

    fn snk(&self, e: Self::Edge) -> Self::Node {
        Node(self.edges[e.0.to_usize().unwrap() & !1].snk)
    }
}

/// Graph iterator over edges incident with some node.
#[derive(Clone)]
pub struct NeighIt<ID>(ID);

impl<'a, ID, N, E> GraphIterator<LinkedListGraph<ID, N, E>> for NeighIt<ID>
where
    ID: 'a + PrimInt + Unsigned,
{
    type Item = (Edge<ID>, Node<ID>);

    fn next(&mut self, g: &LinkedListGraph<ID, N, E>) -> Option<Self::Item> {
        if self.0 != ID::max_value() {
            let e = &g.edges[self.0.to_usize().unwrap()];
            let x = (Edge(self.0), Node(e.snk));
            self.0 = e.next;
            Some(x)
        } else {
            None
        }
    }
}

impl<'a, ID, N: 'a, E: 'a> Undirected<'a> for LinkedListGraph<ID, N, E>
where
    ID: 'a + PrimInt + Unsigned,
{
    type NeighIt = NeighIt<ID>;

    fn neigh_iter(&'a self, u: Self::Node) -> Self::NeighIt {
        let u = &self.nodes[u.index()];
        if u.first_out != ID::max_value() {
            NeighIt(u.first_out)
        } else {
            NeighIt(u.first_in)
        }
    }
}

/// A graph iterator over edges leaving a node.
#[derive(Clone)]
pub struct OutIt<ID>(ID);

impl<'a, ID, N, E> GraphIterator<LinkedListGraph<ID, N, E>> for OutIt<ID>
where
    ID: 'a + PrimInt + Unsigned,
{
    type Item = (Edge<ID>, Node<ID>);

    fn next(&mut self, g: &LinkedListGraph<ID, N, E>) -> Option<Self::Item> {
        if (self.0 & ID::one()).is_zero() {
            let e = &g.edges[self.0.to_usize().unwrap()];
            let x = (Edge(self.0), Node(e.snk));
            self.0 = e.next;
            Some(x)
        } else {
            None
        }
    }
}

/// A graph iterator over edges entering a node.
pub type InIt<ID> = NeighIt<ID>;

/// A graph iterator over directed edges incident with some node.
pub type IncidentIt<ID> = NeighIt<ID>;

impl<'a, ID, N: 'a, E: 'a> Directed<'a> for LinkedListGraph<ID, N, E>
where
    ID: 'a + PrimInt + Unsigned,
{
    type OutIt = OutIt<ID>;

    type InIt = InIt<ID>;

    type IncidentIt = IncidentIt<ID>;

    type DirectedEdge = Self::Edge;

    fn out_iter(&'a self, u: Self::Node) -> Self::OutIt {
        OutIt(self.nodes[u.index()].first_out)
    }

    fn in_iter(&'a self, u: Self::Node) -> Self::InIt {
        NeighIt(self.nodes[u.index()].first_in)
    }

    fn incident_iter(&'a self, u: Self::Node) -> Self::IncidentIt {
        self.neigh_iter(u)
    }
}

impl<'a, ID, N: 'a, E: 'a> IndexGraph<'a> for LinkedListGraph<ID, N, E>
where
    ID: 'a + PrimInt + Unsigned,
{
    fn node_id(&self, u: Self::Node) -> usize {
        u.index()
    }

    fn id2node(&self, id: usize) -> Self::Node {
        debug_assert!(id < self.nodes.len(), "Invalid node id");
        Node(ID::from(id).unwrap())
    }

    fn edge_id(&self, e: Self::Edge) -> usize {
        e.index()
    }

    fn id2edge(&self, id: usize) -> Self::Edge {
        debug_assert!(id << 1 < self.edges.len(), "Invalid edge id");
        Edge(ID::from(id << 1).unwrap())
    }
}

impl<'a, ID, N: 'a, E: 'a> NodeAttributes<'a, LinkedListGraph<ID, N, E>, N> for LinkedListGraph<ID, N, E>
where
    ID: 'a + PrimInt + Unsigned,
{
    fn node(&self, u: <Self as GraphType<'a>>::Node) -> &N {
        &self.nodes[u.index()].attrs
    }

    fn node_mut(&mut self, u: <Self as GraphType<'a>>::Node) -> &mut N {
        &mut self.nodes[u.index()].attrs
    }
}

impl<'a, ID, N: 'a, E: 'a> EdgeAttributes<'a, LinkedListGraph<ID, N, E>, E> for LinkedListGraph<ID, N, E>
where
    ID: 'a + PrimInt + Unsigned,
{
    fn edge(&self, e: <Self as GraphType<'a>>::Edge) -> &E {
        &self.edges[e.index()].eattrs
    }

    fn edge_mut(&mut self, e: <Self as GraphType<'a>>::Edge) -> &mut E {
        &mut self.edges[e.index()].eattrs
    }
}

/// A builder for a LinkedListGraph.
///
/// The basic task is to arrange the final outgoing and incoming edges in the
/// linked lists appropriately (i.e. first outgoing, then incoming edges).
pub struct LinkedListGraphBuilder<ID, N, E> {
    /// The graph to be built.
    graph: LinkedListGraph<ID, N, E>,
    /// The last outgoing edge for each node (if there is one).
    last_out: Vec<Option<ID>>,
}

impl<ID, N, E> Builder for LinkedListGraphBuilder<ID, N, E>
where
    ID: PrimInt + Unsigned,
    N: Default,
    E: Default,
{
    type Graph = LinkedListGraph<ID, N, E>;
    type Node = Node<ID>;
    type Edge = Edge<ID>;

    fn with_capacities(nnodes: usize, nedges: usize) -> Self {
        LinkedListGraphBuilder {
            graph: LinkedListGraph {
                nodes: Vec::with_capacity(nnodes),
                edges: Vec::with_capacity(nedges),
            },
            last_out: Vec::with_capacity(nnodes),
        }
    }

    fn reserve(&mut self, nnodes: usize, nedges: usize) {
        self.graph.nodes.reserve(nnodes);
        self.graph.edges.reserve(nedges);
        self.last_out.reserve(nnodes);
    }

    fn num_nodes(&self) -> usize {
        self.graph.nodes.len()
    }

    fn num_edges(&self) -> usize {
        self.graph.edges.len() / 2
    }

    fn add_node(&mut self) -> Self::Node {
        assert!(
            self.graph.nodes.len() + 1 < ID::max_value().to_usize().unwrap(),
            "Node capacity exceeded"
        );
        let id = self.graph.nodes.len();
        self.graph.nodes.push(NodeData {
            first_out: ID::max_value(),
            first_in: ID::max_value(),
            attrs: Default::default(),
        });
        self.last_out.push(None);
        Node(ID::from(id).unwrap())
    }

    fn add_edge(&mut self, u: Self::Node, v: Self::Node) -> Self::Edge {
        assert!(
            self.graph.edges.len() + 2 < ID::max_value().to_usize().unwrap(),
            "Edge capacity exceeded"
        );
        let eid = ID::from(self.graph.edges.len()).unwrap();
        let uid = u.0.to_usize().unwrap();
        let vid = v.0.to_usize().unwrap();
        self.graph.edges.push(EdgeData {
            snk: v.0,
            next: self.graph.nodes[uid].first_out,
            eattrs: Default::default(),
        });
        self.graph.edges.push(EdgeData {
            snk: u.0,
            next: self.graph.nodes[vid].first_in,
            eattrs: Default::default(),
        });
        self.graph.nodes[uid].first_out = eid;
        self.graph.nodes[vid].first_in = eid + ID::one();
        if self.last_out[uid].is_none() {
            self.last_out[uid] = Some(eid);
        }
        Edge(eid)
    }

    fn node2id(&self, u: Self::Node) -> usize {
        IndexGraph::node_id(&self.graph, u)
    }

    fn edge2id(&self, e: Self::Edge) -> usize {
        IndexGraph::edge_id(&self.graph, e)
    }

    fn into_graph(self) -> LinkedListGraph<ID, N, E> {
        // Append the list of incoming edges to the end of the list of outgoing
        // edges.
        let mut g = self.graph;
        for (u, e) in self
            .last_out
            .into_iter()
            .enumerate()
            .filter_map(|(u, e)| e.map(|e| (u, e)))
        {
            g.edges[e.to_usize().unwrap()].next = g.nodes[u].first_in;
        }
        g
    }
}

impl<ID, N, E> Buildable for LinkedListGraph<ID, N, E>
where
    ID: PrimInt + Unsigned,
    N: Default,
    E: Default,
{
    type Builder = LinkedListGraphBuilder<ID, N, E>;
}

impl<ID, N, E> LinkedListGraph<ID, N, E>
where
    ID: PrimInt + Unsigned,
{
    pub fn new() -> LinkedListGraph<ID, N, E> {
        LinkedListGraph {
            nodes: vec![],
            edges: vec![],
        }
    }
}

impl<ID, N, E> Default for LinkedListGraph<ID, N, E>
where
    ID: PrimInt + Unsigned,
{
    fn default() -> Self {
        LinkedListGraph::new()
    }
}

#[cfg(test)]
mod tests {
    use crate::attributes::*;
    use crate::classes::*;
    use crate::traits::Indexable;
    use crate::traits::*;
    use crate::LinkedListGraph;
    use std::cmp::{max, min};

    #[test]
    fn test_graph() {
        const N: usize = 7;
        let g = cycle::<LinkedListGraph>(N);

        assert_eq!(g.num_nodes(), N);
        assert_eq!(g.num_edges(), N);

        let mut balances = vec![0; g.num_nodes()];

        for u in g.nodes() {
            balances[g.node_id(u)] = u.index();
        }

        for u in g.nodes() {
            assert_eq!(balances[g.node_id(u)], u.index());
        }

        for u in g.nodes() {
            let mut neighs: Vec<_> = g.neighs(u).collect();

            for &(e, v) in &neighs {
                eprintln!(
                    "{} {}->{} {}-{}",
                    e.index(),
                    u.index(),
                    v.index(),
                    g.enodes(e).0.index(),
                    g.enodes(e).1.index()
                );
                assert!((g.enodes(e) == (u, v)) || (g.enodes(e) == (v, u)));
            }

            neighs.sort_by_key(|&(_, u)| u.index());

            let x = (u.index() + N - 1) % N;
            let y = (u.index() + 1) % N;
            assert_eq!(
                neighs.iter().map(|&(_, v)| v).collect::<Vec<_>>(),
                vec![g.id2node(min(x, y)), g.id2node(max(x, y))]
            );
        }
    }

    #[test]
    fn test_edge_vec() {
        let g = cycle::<LinkedListGraph>(7);

        let mut x = vec![0; g.num_edges()];
        for (i, e) in g.edges().enumerate() {
            x[g.edge_id(e)] = i;
        }

        for u in g.nodes() {
            for (e, _) in g.neighs(u) {
                assert_eq!(x[g.edge_id(e)], e.index());
            }
        }
    }

    #[test]
    fn test_digraph() {
        for g in [cycle::<LinkedListGraph>(7), peterson(), hypercube(5)].iter() {
            for u in g.nodes() {
                for (e, v) in g.outedges(u) {
                    assert_eq!(u, g.src(e));
                    assert_eq!(v, g.snk(e));
                }
                for (e, v) in g.inedges(u) {
                    assert_eq!(v, g.src(e));
                    assert_eq!(u, g.snk(e));
                }
                for (e, v) in g.incident_edges(u) {
                    assert_eq!(
                        v,
                        if e.is_incoming() {
                            g.src(e.edge())
                        } else {
                            g.snk(e.edge())
                        }
                    );
                }
            }
        }
    }

    #[test]
    fn test_attrs() {
        #[derive(Default)]
        struct NodeData {
            balance: usize,
        }

        #[derive(Default)]
        struct EdgeData {
            upper: usize,
        }

        let mut g = peterson::<LinkedListGraph<u32, NodeData, EdgeData>>();
        for u in 0..g.num_nodes() {
            g.node_mut(g.id2node(u)).balance = u;
        }

        for e in 0..g.num_edges() {
            let uid = g.node_id(g.src(g.id2edge(e)));
            g.edge_mut(g.id2edge(e)).upper = uid;
        }

        for u in g.nodes() {
            assert_eq!(g.node(u).balance, g.node_id(u));
            for (e, _) in g.outedges(u) {
                assert_eq!(g.edge(e).upper, g.node_id(g.src(e)));
            }
            for (e, _) in g.inedges(u) {
                assert_eq!(g.edge(e).upper, g.node_id(g.src(e)));
            }
        }
    }

    #[cfg(feature = "serialize")]
    mod serialize {
        use super::LinkedListGraph;
        use crate::classes::peterson;
        use crate::traits::{FiniteDigraph, FiniteGraph, IndexGraph, };
        use serde_json;

        #[test]
        fn test_serde() {
            let g = peterson::<LinkedListGraph>();

            let serialized = serde_json::to_string(&g).unwrap();

            println!("serialized = {}", serialized);

            let h: LinkedListGraph = serde_json::from_str(&serialized).unwrap();

            assert_eq!(g.num_nodes(), h.num_nodes());
            assert_eq!(g.num_edges(), h.num_edges());
            for e in g.edges() {
                let f = h.id2edge(g.edge_id(e));
                assert_eq!(g.node_id(g.src(e)), h.node_id(h.src(f)));
                assert_eq!(g.node_id(g.snk(e)), h.node_id(h.snk(f)));
            }
        }

        #[test]
        fn test_serialize() {
            use crate::{Buildable, Builder};
            let g = LinkedListGraph::<u32>::new_with(|b| {
                let nodes = b.add_nodes(5);
                b.add_edge(nodes[0], nodes[1]);
                b.add_edge(nodes[0], nodes[2]);
                b.add_edge(nodes[1], nodes[4]);
                b.add_edge(nodes[2], nodes[3]);
            });

            let serialized = serde_json::to_string(&g).unwrap();
            let g2: LinkedListGraph<u32> = serde_json::from_str(&serialized).unwrap();

            assert_eq!(g.num_nodes(), g2.num_nodes());
            let mut edges = g2
                .edges()
                .map(|e| {
                    let (u, v) = g2.enodes(e);
                    let (u, v) = (g2.node_id(u), g2.node_id(v));
                    (u.min(v), u.max(v))
                })
                .collect::<Vec<_>>();
            edges.sort();
            assert_eq!(edges, vec![(0, 1), (0, 2), (1, 4), (2, 3)]);
        }
    }
}
