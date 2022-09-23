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

//! Traits for graph data structures.
//!
//! The traits for graph data structures provide an additional level
//! of information about (the edges of) the graph. There are three
//! levels:
//!
//! 1. `Graph`: an undirected graph, edges have no defined source or
//!     sink.
//! 2. `Digraph`: a directed graph, each edge has a designated source
//!     and a designated sink node. Furthermore, there is the concept
//!     of "outgoing" and "incoming" edges. A `Digraph` is also a
//!     `Graph`, which basically means ignoring the direction
//!     information of the edges.

use crate::adjacencies::{InEdges, Neighbors, OutEdges};

pub mod refs;

/// A graph iterator.
///
/// This is roughly the same interface as a standard iterator. However,
/// all its method take additionally the graph itself as parameter. This
/// allows the iterator to not contain a reference to internal graph data.
///
/// This might be useful for algorithms that need to store several
/// iterators because they require less memory (they do not need to store
/// a reference to the same graph, each!).
pub trait GraphIterator<G: ?Sized>: Clone {
    type Item;

    fn next(&mut self, g: &G) -> Option<Self::Item>;

    fn size_hint(&self, _g: &G) -> (usize, Option<usize>) {
        (0, None)
    }

    fn count(mut self, g: &G) -> usize {
        let mut c = 0;
        while self.next(g).is_some() {
            c += 1
        }
        c
    }

    fn iter(self, g: &G) -> GraphIter<G, Self>
    where
        G: Sized,
    {
        GraphIter(self, g)
    }
}

/// A graph iterator as a standard iterator.
///
/// This is a pair consisting of a graph iterator and a reference the
/// graph itself. It can be used as a standard iterator.
pub struct GraphIter<'a, G, I>(pub(crate) I, pub(crate) &'a G);

impl<'a, G, I> Clone for GraphIter<'a, G, I>
where
    I: Clone,
{
    fn clone(&self) -> Self {
        GraphIter(self.0.clone(), self.1)
    }
}

impl<'a, G, I> Iterator for GraphIter<'a, G, I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next(self.1)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint(self.1)
    }

    fn count(self) -> usize {
        self.0.count(self.1)
    }
}

/// Base information of a graph.
pub trait GraphType<'a> {
    /// Type of a node.
    type Node: 'a + Copy + Eq;

    /// Type of an edge.
    type Edge: 'a + Copy + Eq;
}

/// Iterator over all nodes of a graph.
pub type NodeIterator<'a, G> = GraphIter<'a, G, <G as FiniteGraph<'a>>::NodeIt>;

/// Iterator over all edges of a graph.
pub type EdgeIterator<'a, G> = GraphIter<'a, G, <G as FiniteGraph<'a>>::EdgeIt>;

/// A (finite) graph with a known number of nodes and edges.
///
/// Finite graphs also provide access to the list of all nodes and edges.
pub trait FiniteGraph<'a>: GraphType<'a> {
    /// Type of an iterator over all nodes.
    type NodeIt: GraphIterator<Self, Item = Self::Node>;

    /// Type of an iterator over all edges.
    type EdgeIt: GraphIterator<Self, Item = Self::Edge>;

    /// Return the number of nodes in the graph.
    fn num_nodes(&self) -> usize;
    /// Return the number of edges in the graph.
    fn num_edges(&self) -> usize;

    /// Return a graph iterator over all nodes.
    fn nodes_iter(&'a self) -> Self::NodeIt;

    /// Return an iterator over all nodes.
    fn nodes(&'a self) -> NodeIterator<'a, Self>
    where
        Self: Sized,
    {
        GraphIter(self.nodes_iter(), self)
    }

    /// Return a graph iterator over all edges.
    ///
    /// This iterator traverses only the forward edges.
    fn edges_iter(&'a self) -> Self::EdgeIt;

    /// Return an iterator over all edges.
    ///
    /// This iterator traverses only the forward edges.
    fn edges(&'a self) -> EdgeIterator<'a, Self>
    where
        Self: Sized,
    {
        GraphIter(self.edges_iter(), self)
    }

    /// Return the nodes connected by an edge.
    ///
    /// The order of the nodes is undefined.
    fn enodes(&'a self, e: Self::Edge) -> (Self::Node, Self::Node);
}

/// A (finite) directed graph with a known number of nodes and edges.
///
/// For each edge the source and the sink node may be returned.
pub trait FiniteDigraph<'a>: FiniteGraph<'a> {
    /// Return the source node of an edge.
    fn src(&'a self, e: Self::Edge) -> Self::Node;

    /// Return the sink node of an edge.
    fn snk(&'a self, e: Self::Edge) -> Self::Node;
}

/// Iterator over incident edges and neighbors of some node.
type NeighIterator<'a, G> = GraphIter<'a, G, <G as Undirected<'a>>::NeighIt>;

/// A graph with list access to undirected incident edges.
pub trait Undirected<'a>: GraphType<'a> {
    /// Type of a graph iterator over all incident edges.
    type NeighIt: GraphIterator<Self, Item = (Self::Edge, Self::Node)>;

    /// Return a graph iterator over the edges adjacent to some node.
    fn neigh_iter(&'a self, u: Self::Node) -> Self::NeighIt;

    /// Return an iterator over the edges adjacent to some node.
    fn neighs(&'a self, u: Self::Node) -> NeighIterator<'a, Self>
    where
        Self: Sized,
    {
        self.neigh_iter(u).iter(self)
    }

    /// Return access to the neighbors via an `Adjacencies` trait.
    ///
    /// This is the same as calling `Neighbors(&g)` on the graph.
    fn neighbors(&'a self) -> Neighbors<'a, Self>
    where
        Self: Sized,
    {
        Neighbors(self)
    }
}

/// A directed edge.
///
/// A directed edge is either incoming or outgoing.
pub trait DirectedEdge {
    /// The underlying edge.
    type Edge;

    /// Whether the edge is incoming.
    fn is_incoming(&self) -> bool;

    /// Whether the edge is outgoing.
    fn is_outgoing(&self) -> bool {
        !self.is_incoming()
    }

    /// The underlying edge.
    fn edge(&self) -> Self::Edge;
}

/// Iterator over edges leaving a node.
type OutIterator<'a, G> = GraphIter<'a, G, <G as Directed<'a>>::OutIt>;

/// Iterator over edges entering a node.
type InIterator<'a, G> = GraphIter<'a, G, <G as Directed<'a>>::InIt>;

/// Iterator over directed edges incident with a node.
type IncidentIterator<'a, G> = GraphIter<'a, G, <G as Directed<'a>>::IncidentIt>;

/// A graph with list access to directed incident edges.
///
/// Note that each directed graph is also an undirected graph
/// by simply ignoring the direction of each edge. Hence, each
/// type implementing `Directed` must also implement `Undirected`.
///
/// This trait adds a few additional methods to explicitely access the
/// direction information of an edge. In particular, the direction
/// information can be used in the following ways:
///
///  - The `src` and `snk` methods return the source and sink nodes of
///    an edge.
///  - The iterators `outedges` and `inedges` iterate only over edges
///    leaving or entering a certain node, respectively.
pub trait Directed<'a>: Undirected<'a> {
    /// Type of a graph iterator over edges leaving a node.
    type OutIt: GraphIterator<Self, Item = (Self::Edge, Self::Node)>;

    /// Type of a graph iterator over edges entering a node.
    type InIt: GraphIterator<Self, Item = (Self::Edge, Self::Node)>;

    /// Type of an iterator over all incident edges.
    type IncidentIt: GraphIterator<Self, Item = (Self::DirectedEdge, Self::Node)>;

    /// Type of a directed edge.
    type DirectedEdge: 'a + DirectedEdge<Edge = Self::Edge> + Copy + Eq;

    /// Return a graph iterator over the edges leaving a node.
    fn out_iter(&'a self, u: Self::Node) -> Self::OutIt;

    /// Return an iterator over the edges leaving a node.
    fn outedges(&'a self, u: Self::Node) -> OutIterator<'a, Self>
    where
        Self: Sized,
    {
        GraphIter(self.out_iter(u), self)
    }

    /// Return access to the outgoing arcs via an `Adjacencies` trait.
    ///
    /// This is the same as calling `OutEdges(&g)` on the graph.
    fn outgoing(&'a self) -> OutEdges<'a, Self>
    where
        Self: Sized,
    {
        OutEdges(self)
    }

    /// Return a graph iterator over the edges leaving a node.
    fn in_iter(&'a self, u: Self::Node) -> Self::InIt;

    /// Return an iterator over the edges leaving a node.
    fn inedges(&'a self, u: Self::Node) -> InIterator<'a, Self>
    where
        Self: Sized,
    {
        GraphIter(self.in_iter(u), self)
    }

    /// Return access to the incoming arcs via an `Adjacencies` trait.
    ///
    /// This is the same as calling `InEdges(&g)` on the graph.
    fn incoming(&'a self) -> InEdges<'a, Self>
    where
        Self: Sized,
    {
        InEdges(self)
    }

    /// Return an iterator over all directed edges incident with a node.
    fn incident_iter(&'a self, u: Self::Node) -> Self::IncidentIt;

    /// Return an iterator over all directed edges incident with a node.
    fn incident_edges(&'a self, u: Self::Node) -> IncidentIterator<'a, Self>
    where
        Self: Sized,
    {
        GraphIter(self.incident_iter(u), self)
    }
}

/// A trait for general undirected, finite graphs.
pub trait Graph<'a>: FiniteGraph<'a> + Undirected<'a> {}

impl<'a, G> Graph<'a> for G where G: FiniteGraph<'a> + Undirected<'a> {}

/// A trait for general directed, finite graphs.
pub trait Digraph<'a>: Graph<'a> + FiniteDigraph<'a> + Directed<'a> {}

impl<'a, G> Digraph<'a> for G where G: FiniteDigraph<'a> + Directed<'a> {}

/// An item that has an index.
pub trait Indexable {
    fn index(&self) -> usize;
}

/// Associates nodes and edges with unique ids.
pub trait IndexGraph<'a>: Graph<'a> {
    /// Return a unique id associated with a node.
    fn node_id(&self, u: Self::Node) -> usize;

    /// Return the node associated with the given id.
    ///
    /// The method panics if the id is invalid.
    fn id2node(&'a self, id: usize) -> Self::Node;

    /// Return a unique id associated with an edge.
    ///
    /// The returned id is the same for the edge and its reverse edge.
    fn edge_id(&self, e: Self::Edge) -> usize;

    /// Return the edge associated with the given id.
    ///
    /// The method returns the forward edge.
    ///
    /// The method panics if the id is invalid.
    fn id2edge(&'a self, id: usize) -> Self::Edge;
}

/// A `Digraph` that is also an `IndexGraph`.
pub trait IndexDigraph<'a>: IndexGraph<'a> + Digraph<'a> {}

impl<'a, T> IndexDigraph<'a> for T where T: IndexGraph<'a> + Digraph<'a> {}

/// Marker trait for graphs with directly numbered nodes and edges.
pub trait NumberedGraph<'a>: Graph<'a>
where
    <Self as GraphType<'a>>::Node: Indexable,
    <Self as GraphType<'a>>::Edge: Indexable,
{
}

impl<'a, G> NumberedGraph<'a> for G
where
    G: Graph<'a>,
    G::Node: Indexable,
    G::Edge: Indexable,
{
}

/// Marker trait for digraphs with directly numbered nodes and edges.
pub trait NumberedDigraph<'a>: NumberedGraph<'a> + Digraph<'a>
where
    <Self as GraphType<'a>>::Node: Indexable,
    <Self as GraphType<'a>>::Edge: Indexable,
{
}

impl<'a, G> NumberedDigraph<'a> for G
where
    G: Digraph<'a> + NumberedGraph<'a>,
    G::Node: Indexable,
    G::Edge: Indexable,
{
}

impl<'a, 'g: 'a, G> GraphType<'a> for &'g G
where
    G: GraphType<'g>,
{
    type Node = G::Node;

    type Edge = G::Edge;
}

#[derive(Clone)]
pub struct WrapIt<I>(pub I);

impl<'a, G, I> GraphIterator<&'a G> for WrapIt<I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self, g: &&'a G) -> Option<Self::Item> {
        self.0.next(*g)
    }

    fn size_hint(&self, g: &&'a G) -> (usize, Option<usize>) {
        self.0.size_hint(*g)
    }

    fn count(self, g: &&'a G) -> usize {
        self.0.count(*g)
    }
}

impl<I> From<I> for WrapIt<I> {
    fn from(it: I) -> WrapIt<I> {
        WrapIt(it)
    }
}

impl<'a, 'g: 'a, G> FiniteGraph<'a> for &'g G
where
    G: FiniteGraph<'g>,
{
    type NodeIt = WrapIt<G::NodeIt>;

    type EdgeIt = WrapIt<G::EdgeIt>;

    fn num_nodes(&self) -> usize {
        (*self).num_nodes()
    }

    fn num_edges(&self) -> usize {
        (*self).num_edges()
    }

    fn nodes_iter(&'a self) -> Self::NodeIt {
        (*self).nodes_iter().into()
    }

    fn edges_iter(&self) -> Self::EdgeIt {
        (*self).edges_iter().into()
    }

    fn enodes(&'a self, e: Self::Edge) -> (Self::Node, Self::Node) {
        (*self).enodes(e)
    }
}

impl<'a, 'g: 'a, G> FiniteDigraph<'a> for &'g G
where
    G: FiniteDigraph<'g>,
{
    fn src(&'a self, e: Self::Edge) -> Self::Node {
        (*self).src(e)
    }

    fn snk(&'a self, e: Self::Edge) -> Self::Node {
        (*self).snk(e)
    }
}

impl<'a, 'g: 'a, G> Undirected<'a> for &'g G
where
    G: Undirected<'g>,
{
    type NeighIt = WrapIt<G::NeighIt>;

    fn neigh_iter(&'a self, u: Self::Node) -> Self::NeighIt {
        (*self).neigh_iter(u).into()
    }
}

impl<'a, 'g: 'a, G> IndexGraph<'a> for &'g G
where
    G: IndexGraph<'g>,
{
    fn node_id(&self, u: Self::Node) -> usize {
        (*self).node_id(u)
    }

    fn id2node(&'a self, id: usize) -> Self::Node {
        (*self).id2node(id)
    }

    fn edge_id(&self, e: Self::Edge) -> usize {
        (*self).edge_id(e)
    }

    fn id2edge(&'a self, id: usize) -> Self::Edge {
        (*self).id2edge(id)
    }
}

impl<'a, 'g: 'a, G> Directed<'a> for &'g G
where
    G: Directed<'g>,
{
    type OutIt = WrapIt<G::OutIt>;

    type InIt = WrapIt<G::InIt>;

    type IncidentIt = WrapIt<G::IncidentIt>;

    type DirectedEdge = G::DirectedEdge;

    fn out_iter(&'a self, u: Self::Node) -> Self::OutIt {
        (*self).out_iter(u).into()
    }

    fn in_iter(&'a self, u: Self::Node) -> Self::InIt {
        (*self).in_iter(u).into()
    }

    fn incident_iter(&'a self, u: Self::Node) -> Self::IncidentIt {
        (*self).incident_iter(u).into()
    }
}

impl<'a, G> refs::FiniteGraphRef<'a> for &'a G
where
    G: FiniteGraph<'a>,
{
    fn nodes_iter(&self) -> Self::NodeIt {
        (*self).nodes_iter().into()
    }

    fn edges_iter(&self) -> Self::EdgeIt {
        (*self).edges_iter().into()
    }

    fn enodes(&self, e: Self::Edge) -> (Self::Node, Self::Node) {
        (*self).enodes(e)
    }
}

impl<'a, G> refs::FiniteDigraphRef<'a> for &'a G
where
    G: FiniteDigraph<'a>,
{
    fn src(&self, e: Self::Edge) -> Self::Node {
        (*self).src(e)
    }

    fn snk(&self, e: Self::Edge) -> Self::Node {
        (*self).snk(e)
    }
}

impl<'a, G> refs::UndirectedRef<'a> for &'a G
where
    G: Undirected<'a>,
{
    fn neigh_iter(&self, u: Self::Node) -> Self::NeighIt {
        (*self).neigh_iter(u).into()
    }
}

impl<'a, G> refs::DirectedRef<'a> for &'a G
where
    G: Directed<'a>,
{
    fn out_iter(&self, u: Self::Node) -> Self::OutIt {
        (*self).out_iter(u).into()
    }

    fn in_iter(&self, u: Self::Node) -> Self::InIt {
        (*self).in_iter(u).into()
    }

    fn incident_iter(&self, u: Self::Node) -> Self::IncidentIt {
        (*self).incident_iter(u).into()
    }
}

impl<'a, G> refs::IndexGraphRef<'a> for &'a G
where
    G: IndexGraph<'a>,
{
    fn id2node(&self, id: usize) -> Self::Node {
        (*self).id2node(id)
    }

    fn id2edge(&self, id: usize) -> Self::Edge {
        (*self).id2edge(id)
    }
}
