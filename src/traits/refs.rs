/*
 * Copyright (c) 2020-2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

///! Reference graph traits.
use super::{Directed, FiniteDigraph, FiniteGraph, GraphIter, IndexGraph, Undirected};

/// A reference to a basic finite graph.
///
/// This trait contains methods with a unrestricted lifetime for `self`.
pub trait FiniteGraphRef<'a>: FiniteGraph<'a> {
    fn nodes_iter(&self) -> Self::NodeIt;
    fn edges_iter(&self) -> Self::EdgeIt;

    fn nodes<'b>(&'b self) -> GraphIter<'b, Self, Self::NodeIt>
    where
        Self: Sized,
        'a: 'b,
    {
        GraphIter(FiniteGraphRef::nodes_iter(self), self)
    }

    fn edges<'b>(&'b self) -> GraphIter<'b, Self, Self::EdgeIt>
    where
        Self: Sized,
        'a: 'b,
    {
        GraphIter(FiniteGraphRef::edges_iter(self), self)
    }

    fn enodes(&self, e: Self::Edge) -> (Self::Node, Self::Node);
}

/// A reference to a basic graph.
///
/// This trait contains methods with a unrestricted lifetime for `self`.
pub trait FiniteDigraphRef<'a>: FiniteDigraph<'a> {
    fn src(&self, e: Self::Edge) -> Self::Node;
    fn snk(&self, e: Self::Edge) -> Self::Node;
}

/// A reference to an undirected graph.
///
/// This trait contains methods with a unrestricted lifetime for `self`.
pub trait UndirectedRef<'a>: Undirected<'a> {
    fn neigh_iter(&self, u: Self::Node) -> Self::NeighIt;
}

/// A reference to a digraph.
///
/// This trait contains methods with a unrestricted lifetime for `self`.
pub trait DirectedRef<'a>: Directed<'a> + UndirectedRef<'a> {
    fn out_iter(&self, u: Self::Node) -> Self::OutIt;
    fn in_iter(&self, u: Self::Node) -> Self::InIt;
    fn incident_iter(&self, u: Self::Node) -> Self::IncidentIt;
}

/// A reference to an indexed graph.
///
/// This trait contains methods with a unrestricted lifetime for `self`.
pub trait IndexGraphRef<'a>: IndexGraph<'a> + UndirectedRef<'a> {
    fn id2node(&self, id: usize) -> Self::Node;
    fn id2edge(&self, id: usize) -> Self::Edge;
}
