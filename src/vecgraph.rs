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

use crate::builder::{Buildable, Builder};
use crate::traits::{Directed, DirectedEdge, FiniteDigraph, FiniteGraph, GraphIterator, GraphType, Undirected};
use crate::traits::{IndexGraph, Indexable};

use crate::num::iter::{range, range_step, Range, RangeStep};
use crate::num::traits::{PrimInt, Unsigned};

use std::fmt;
use std::hash::{Hash, Hasher};
use std::slice::Iter as SliceIter;

#[cfg(feature = "serialize")]
use serde_derive::{Deserialize, Serialize};

/// Node of a vector graph.
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

/// Edge of a vector graph.
///
/// This is basically a newtype of the *edge* index. Note that
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

/// Data for a node in a vector graph.
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
struct NodeData<ID> {
    firstout: ID,
    firstin: ID,
}

/// Data for an edge in a vector graph.
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
struct EdgeData<ID> {
    nodes: [ID; 2],
}

/// A vector based graph data structure.
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct VecGraph<ID = u32> {
    nodes: Vec<NodeData<ID>>,
    edges: Vec<EdgeData<ID>>,
    // The list of adjacencies. This list contains the edge numbers in
    // a specific order, so that for each node the incident outgoing
    // and incoming edges are in successive positions.
    adj: Vec<ID>,
}

/// A graph iterator over all nodes of a linked list graph.
#[derive(Clone)]
pub struct NodeIt<ID>(Range<ID>);

impl<'a, ID> GraphIterator<VecGraph<ID>> for NodeIt<ID>
where
    ID: 'a + PrimInt + Unsigned,
{
    type Item = Node<ID>;

    fn next(&mut self, _g: &VecGraph<ID>) -> Option<Self::Item> {
        Iterator::next(&mut self.0).map(Node)
    }

    fn size_hint(&self, _g: &VecGraph<ID>) -> (usize, Option<usize>) {
        Iterator::size_hint(&self.0)
    }

    fn count(self, _g: &VecGraph<ID>) -> usize {
        Iterator::count(self.0)
    }
}

/// An iterator over all edges of a linked list graph.
///
/// This iterator only returns the forward edges.
#[derive(Clone)]
pub struct EdgeIt<ID>(RangeStep<ID>);

impl<'a, ID> GraphIterator<VecGraph<ID>> for EdgeIt<ID>
where
    ID: 'a + PrimInt + Unsigned,
{
    type Item = Edge<ID>;

    fn next(&mut self, _g: &VecGraph<ID>) -> Option<Self::Item> {
        Iterator::next(&mut self.0).map(Edge)
    }

    fn size_hint(&self, _g: &VecGraph<ID>) -> (usize, Option<usize>) {
        Iterator::size_hint(&self.0)
    }

    fn count(self, _g: &VecGraph<ID>) -> usize {
        Iterator::count(self.0)
    }
}

impl<'a, ID> GraphType<'a> for VecGraph<ID>
where
    ID: 'a + PrimInt + Unsigned,
{
    type Node = Node<ID>;
    type Edge = Edge<ID>;
}

impl<'a, ID> FiniteGraph<'a> for VecGraph<ID>
where
    ID: 'a + PrimInt + Unsigned,
{
    type NodeIt = NodeIt<ID>;
    type EdgeIt = EdgeIt<ID>;

    fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    fn num_edges(&self) -> usize {
        self.edges.len()
    }

    fn nodes_iter(&self) -> Self::NodeIt {
        NodeIt(range(ID::zero(), ID::from(self.num_nodes()).unwrap()))
    }

    fn edges_iter(&self) -> Self::EdgeIt {
        EdgeIt(range_step(
            ID::zero(),
            ID::from(2 * self.edges.len()).unwrap(),
            ID::from(2).unwrap(),
        ))
    }

    fn enodes(&self, e: Self::Edge) -> (Self::Node, Self::Node) {
        let eid = e.index();
        (Node(self.edges[eid].nodes[0]), Node(self.edges[eid].nodes[1]))
    }
}

impl<'a, ID> FiniteDigraph<'a> for VecGraph<ID>
where
    ID: 'a + PrimInt + Unsigned,
{
    fn src(&self, e: Self::Edge) -> Self::Node {
        let eid = e.0.to_usize().unwrap();
        Node(self.edges[eid >> 1].nodes[0])
    }

    fn snk(&self, e: Self::Edge) -> Self::Node {
        let eid = e.0.to_usize().unwrap();
        Node(self.edges[eid >> 1].nodes[1])
    }
}

#[derive(Clone)]
pub struct NeighIt<'a, ID>(SliceIter<'a, ID>);

impl<'a, ID> GraphIterator<VecGraph<ID>> for NeighIt<'a, ID>
where
    ID: 'a + PrimInt + Unsigned,
{
    type Item = (Edge<ID>, Node<ID>);

    fn next(&mut self, g: &VecGraph<ID>) -> Option<Self::Item> {
        self.0.next().map(|&eid| {
            let i = eid.to_usize().unwrap();
            (Edge(eid), Node(g.edges[i >> 1].nodes[1 - (i & 1)]))
        })
    }
}

impl<'a, ID> Undirected<'a> for VecGraph<ID>
where
    ID: 'a + PrimInt + Unsigned,
{
    type NeighIt = NeighIt<'a, ID>;

    fn neigh_iter(&'a self, u: Self::Node) -> Self::NeighIt {
        let uid = u.index();
        let beg = self.nodes[uid].firstout.to_usize().unwrap();
        let end = self
            .nodes
            .get(uid + 1)
            .map(|n| n.firstout.to_usize().unwrap())
            .unwrap_or_else(|| self.adj.len());
        NeighIt(self.adj[beg..end].iter())
    }
}

impl<'a, ID> Directed<'a> for VecGraph<ID>
where
    ID: 'a + PrimInt + Unsigned,
{
    type OutIt = NeighIt<'a, ID>;

    type InIt = NeighIt<'a, ID>;

    type IncidentIt = NeighIt<'a, ID>;

    type DirectedEdge = Self::Edge;

    fn out_iter(&'a self, u: Self::Node) -> Self::OutIt {
        let uid = u.index();
        let beg = self.nodes[uid].firstout.to_usize().unwrap();
        let end = self.nodes[uid].firstin.to_usize().unwrap();
        NeighIt(self.adj[beg..end].iter())
    }

    fn in_iter(&'a self, u: Self::Node) -> Self::InIt {
        let uid = u.index();
        let beg = self.nodes[uid].firstin.to_usize().unwrap();
        let end = self
            .nodes
            .get(uid + 1)
            .map(|n| n.firstout.to_usize().unwrap())
            .unwrap_or_else(|| self.adj.len());
        NeighIt(self.adj[beg..end].iter())
    }

    fn incident_iter(&'a self, u: Self::Node) -> Self::IncidentIt {
        self.neigh_iter(u)
    }
}

impl<'a, ID> IndexGraph<'a> for VecGraph<ID>
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
        debug_assert!(
            id < self.edges.len(),
            "Invalid edge id: {}({}), must be in 0..{}",
            id,
            id << 1,
            self.edges.len()
        );
        Edge(ID::from(id << 1).unwrap())
    }
}

/// A builder for a VecGraph.
///
/// The basic task is to arrange the final outgoing and incoming edges in the
/// linked lists appropriately (i.e. first outgoing, then incoming edges).
pub struct VecGraphBuilder<ID> {
    /// The outgoing and incoming edges of each node.
    nodes: Vec<[Vec<ID>; 2]>,

    /// The end nodes of each edge.
    edges: Vec<EdgeData<ID>>,
}

impl<ID> Builder for VecGraphBuilder<ID>
where
    ID: PrimInt + Unsigned,
{
    type Graph = VecGraph<ID>;
    type Node = Node<ID>;
    type Edge = Edge<ID>;

    fn with_capacities(nnodes: usize, nedges: usize) -> Self {
        VecGraphBuilder {
            nodes: Vec::with_capacity(nnodes),
            edges: Vec::with_capacity(nedges),
        }
    }

    fn reserve(&mut self, nnodes: usize, nedges: usize) {
        self.nodes.reserve(nnodes);
        self.edges.reserve(nedges);
    }

    fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    fn num_edges(&self) -> usize {
        self.edges.len()
    }

    fn add_node(&mut self) -> Self::Node {
        assert!(
            self.nodes.len() + 1 < ID::max_value().to_usize().unwrap(),
            "Node capacity exceeded"
        );
        let id = self.nodes.len();
        self.nodes.push([vec![], vec![]]);
        Node(ID::from(id).unwrap())
    }

    fn add_edge(&mut self, u: Self::Node, v: Self::Node) -> Self::Edge {
        assert!(
            self.edges.len() * 2 + 2 < ID::max_value().to_usize().unwrap(),
            "Edge capacity exceeded"
        );
        let eid = ID::from(self.edges.len() << 1).unwrap();
        self.edges.push(EdgeData { nodes: [u.0, v.0] });
        self.nodes[u.index()][0].push(eid);
        self.nodes[v.index()][1].push(eid | ID::one());
        Edge(eid)
    }

    fn node2id(&self, u: Self::Node) -> usize {
        u.index()
    }

    fn edge2id(&self, e: Self::Edge) -> usize {
        e.index()
    }

    fn into_graph(self) -> VecGraph<ID> {
        let mut nodes = Vec::with_capacity(self.nodes.len());
        let mut adj = Vec::with_capacity(self.edges.len() * 2);

        for [outs, ins] in self.nodes.into_iter() {
            nodes.push(NodeData {
                firstout: ID::from(adj.len()).unwrap(),
                firstin: ID::from(adj.len() + outs.len()).unwrap(),
            });
            adj.extend(outs);
            adj.extend(ins);
        }

        VecGraph {
            nodes,
            edges: self.edges,
            adj,
        }
    }
}

impl<ID> Buildable for VecGraph<ID>
where
    ID: PrimInt + Unsigned,
{
    type Builder = VecGraphBuilder<ID>;
}

impl<ID> VecGraph<ID>
where
    ID: PrimInt + Unsigned,
{
    pub fn new() -> VecGraph<ID> {
        VecGraph {
            nodes: vec![],
            edges: vec![],
            adj: vec![],
        }
    }
}

impl<ID> Default for VecGraph<ID>
where
    ID: PrimInt + Unsigned,
{
    fn default() -> Self {
        VecGraph::new()
    }
}

#[cfg(test)]
mod tests {
    use crate::classes::*;
    use crate::traits::Indexable;
    use crate::traits::*;
    use crate::VecGraph;
    use std::cmp::{max, min};

    #[test]
    fn test_graph() {
        const N: usize = 7;
        let g = cycle::<VecGraph>(N);

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
        let g = cycle::<VecGraph>(7);

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
        for g in [cycle::<VecGraph>(7), peterson(), hypercube(5)].iter() {
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

    #[cfg(feature = "serialize")]
    mod serialize {
        use super::VecGraph;
        use crate::classes::peterson;
        use crate::traits::{FiniteDigraph, FiniteGraph, IndexGraph};
        use serde_json;

        #[test]
        fn test_serde() {
            let g = peterson::<VecGraph>();

            let serialized = serde_json::to_string(&g).unwrap();

            println!("serialized = {}", serialized);

            let h: VecGraph = serde_json::from_str(&serialized).unwrap();

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
            let g = VecGraph::<u32>::new_with(|b| {
                let nodes = b.add_nodes(5);
                b.add_edge(nodes[0], nodes[1]);
                b.add_edge(nodes[0], nodes[2]);
                b.add_edge(nodes[1], nodes[4]);
                b.add_edge(nodes[2], nodes[3]);
            });

            let serialized = serde_json::to_string(&g).unwrap();
            let g2: VecGraph<u32> = serde_json::from_str(&serialized).unwrap();

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
