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

//! Traits for constructing graphs.

/// A trait to construct graphs.
///
/// In general graphs are static objects. In order to build a graph,
/// one should use a graph builder and, once the construction is
/// complete, convert it into a graph.
///
/// This 2-level approach is used because some graph implementations
/// be unstable if the graph is modified (e.g., the node numbers might
/// change). The builder approach allows to separate construction and
/// use of a graph.
pub trait Builder
where
    Self: Sized,
{
    /// The graph type produced by this builder.
    type Graph;

    /// The type of a nodes.
    type Node: Copy + Eq;

    /// The type of an edge.
    type Edge: Copy + Eq;

    /// Create a new, empty builder.
    fn new() -> Self {
        Self::with_capacities(0, 0)
    }

    /// Create a new, empty builder.
    ///
    /// The builder might be passed a guess of the number of nodes and
    /// edges. This might be used to reserve the appropriate internal
    /// memory, but is no strict requirement for the number of nodes
    /// and edges to be added to the graph.
    fn with_capacities(nnodes: usize, nedges: usize) -> Self;

    /// Reserve memory for a certain number of nodes and edges.
    fn reserve(&mut self, nnodes: usize, nedges: usize);

    /// Return the current number of nodes.
    fn num_nodes(&self) -> usize;

    /// Return the current number of nodes.
    fn num_edges(&self) -> usize;

    /// Add a new node.
    fn add_node(&mut self) -> Self::Node;

    /// Add `n` new nodes.
    fn add_nodes(&mut self, n: usize) -> Vec<Self::Node> {
        (0..n).map(|_| self.add_node()).collect()
    }

    /// Add a new edge.
    fn add_edge(&mut self, u: Self::Node, v: Self::Node) -> Self::Edge;

    /// Return a unique id of a node.
    fn node2id(&self, u: Self::Node) -> usize;

    /// Return a unique id of an edge.
    fn edge2id(&self, e: Self::Edge) -> usize;

    /// Turn the builder into a graph.
    fn into_graph(self) -> Self::Graph;
}

/// A graph with a default builder.
pub trait Buildable
where
    Self: Sized,
{
    type Builder: Builder<Graph = Self>;

    /// Create a new builder for this graph type.
    fn new_builder() -> Self::Builder {
        Self::Builder::new()
    }

    /// Create a new graph by passing the builder to the callback `f`.
    ///
    /// # Example
    ///
    /// ```
    /// use rs_graph::{Buildable, Builder, LinkedListGraph};
    /// use rs_graph::traits::FiniteGraph;
    ///
    /// let g = LinkedListGraph::<usize>::new_with(|b| {
    ///     let u = b.add_node();
    ///     let v = b.add_node();
    ///     b.add_edge(u, v);
    /// });
    ///
    /// assert_eq!(g.num_nodes(), 2);
    /// assert_eq!(g.num_edges(), 1);
    /// ```
    fn new_with<F>(f: F) -> Self
    where
        F: FnOnce(&mut Self::Builder),
    {
        let mut b = Self::new_builder();
        f(&mut b);
        b.into_graph()
    }
}
