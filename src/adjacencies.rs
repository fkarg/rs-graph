/*
 * Copyright (c) 2018, 2020, 2021 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! Abstraction of neighboring edges.
//!
//! This module implements the arguably simplest representation of a graph: for
//! each node the list of adjacent edges and nodes. No further information like
//! the number of nodes or edges in a graph is available.
//!
//! The purpose of the trait `Adjacencies` is therefore to abstract over the concept
//! of adjacent edges and nodes. Standard examples are "all edges" (in the
//! undirected sense), "incoming edges" and "outgoing edges" represented by the structs
//! `Neighbors`, `InEdges` and `OutEdges`.
//!
//! Some algorithms (e.g. breadth-first search or depth-first search) can be
//! described in terms of adjacencies only.
//!
//! # Example
//!
//! ```
//! use rs_graph::classes;
//! use rs_graph::Net;
//! use rs_graph::traits::*;
//! use rs_graph::adjacencies::*;
//!
//! let g = classes::peterson::<Net>();
//!
//! let neighs = Neighbors(&g);
//! let neighs = neighs.filter(|&(e, _)| {
//!   let (u,v) = g.enodes(e);
//!   (g.node_id(u) < 5) == (g.node_id(v) < 5)
//! });
//! for u in g.nodes() {
//!     assert_eq!(neighs.neighs(u).count(), 2);
//! }
//! ```

use crate::traits::{Directed, GraphIter, GraphIterator, GraphType, Undirected};

//pub type AdjacenciesIter<'a, G> = GraphIter<'a, G, <G as Adjacencies<'a>>::IncidenceIt>;

pub trait Adjacencies<'a>: GraphType<'a> {
    type IncidenceIt: GraphIterator<Self, Item = (Self::Edge, Self::Node)>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt;

    fn neighs<'b>(&'b self, u: Self::Node) -> GraphIter<'b, Self, Self::IncidenceIt>
    where
        'a: 'b,
        Self: Sized,
    {
        GraphIter(self.neigh_iter(u), self)
    }

    fn filter<P>(self, predicate: P) -> FilterAdjacencies<Self, P>
    where
        Self: Sized,
        P: for<'r> Fn(&'r (Self::Edge, Self::Node)) -> bool,
    {
        FilterAdjacencies(self, predicate)
    }
}

pub struct FilterAdjacencies<A, P>(A, P);

#[derive(Clone)]
pub struct Filtered<I>(I);

impl<A, P, I> GraphIterator<FilterAdjacencies<A, P>> for Filtered<I>
where
    I: GraphIterator<A>,
    P: for<'r> Fn(&'r I::Item) -> bool,
{
    type Item = I::Item;

    fn next(&mut self, adj: &FilterAdjacencies<A, P>) -> Option<Self::Item> {
        while let Some(it) = self.0.next(&adj.0) {
            if (adj.1)(&it) {
                return Some(it);
            }
        }
        None
    }
}

impl<'a, A, P> GraphType<'a> for FilterAdjacencies<A, P>
where
    A: Adjacencies<'a>,
{
    type Node = A::Node;
    type Edge = A::Edge;
}

impl<'a, A, P> Adjacencies<'a> for FilterAdjacencies<A, P>
where
    A: Adjacencies<'a>,
    P: 'a + Clone + for<'r> Fn(&'r (A::Edge, A::Node)) -> bool,
{
    type IncidenceIt = Filtered<A::IncidenceIt>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt {
        Filtered(self.0.neigh_iter(u))
    }
}

#[derive(Clone)]
pub struct AdjacenciesWrapIt<I>(I);

impl<I> From<I> for AdjacenciesWrapIt<I> {
    fn from(it: I) -> Self {
        AdjacenciesWrapIt(it)
    }
}

impl<'g, G, I> GraphIterator<Neighbors<'g, G>> for AdjacenciesWrapIt<I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self, adj: &Neighbors<'g, G>) -> Option<Self::Item> {
        self.0.next(adj.0)
    }

    fn size_hint(&self, adj: &Neighbors<'g, G>) -> (usize, Option<usize>) {
        self.0.size_hint(adj.0)
    }

    fn count(self, adj: &Neighbors<'g, G>) -> usize {
        self.0.count(adj.0)
    }
}

impl<'g, G, I> GraphIterator<OutEdges<'g, G>> for AdjacenciesWrapIt<I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self, adj: &OutEdges<'g, G>) -> Option<Self::Item> {
        self.0.next(adj.0)
    }

    fn size_hint(&self, adj: &OutEdges<'g, G>) -> (usize, Option<usize>) {
        self.0.size_hint(adj.0)
    }

    fn count(self, adj: &OutEdges<'g, G>) -> usize {
        self.0.count(adj.0)
    }
}

impl<'g, G, I> GraphIterator<InEdges<'g, G>> for AdjacenciesWrapIt<I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self, adj: &InEdges<'g, G>) -> Option<Self::Item> {
        self.0.next(adj.0)
    }

    fn size_hint(&self, adj: &InEdges<'g, G>) -> (usize, Option<usize>) {
        self.0.size_hint(adj.0)
    }

    fn count(self, adj: &InEdges<'g, G>) -> usize {
        self.0.count(adj.0)
    }
}

/// Neighbor access over all adjacent (undirected) edges.
pub struct Neighbors<'g, G>(pub &'g G);

impl<'a, 'g: 'a, G> GraphType<'a> for Neighbors<'g, G>
where
    G: GraphType<'g>,
{
    type Node = G::Node;
    type Edge = G::Edge;
}

impl<'a, 'g: 'a, G> Adjacencies<'a> for Neighbors<'g, G>
where
    G: Undirected<'g>,
{
    type IncidenceIt = AdjacenciesWrapIt<G::NeighIt>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt {
        self.0.neigh_iter(u).into()
    }
}

/// Neighbor access over all outgoing edges of a `Digraph`.
pub struct OutEdges<'g, G>(pub &'g G);

impl<'a, 'g: 'a, G> GraphType<'a> for OutEdges<'g, G>
where
    G: Directed<'g>,
{
    type Node = G::Node;
    type Edge = G::Edge;
}

impl<'a, 'g: 'a, G> Adjacencies<'a> for OutEdges<'g, G>
where
    G: Directed<'g>,
{
    type IncidenceIt = AdjacenciesWrapIt<G::OutIt>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt {
        self.0.out_iter(u).into()
    }
}

/// Neighbor access over all incoming edges of a `Digraph`.
pub struct InEdges<'g, G>(pub &'g G);

impl<'a, 'g: 'a, G> GraphType<'a> for InEdges<'g, G>
where
    G: Directed<'g>,
{
    type Node = G::Node;
    type Edge = G::Edge;
}

impl<'a, 'g: 'a, G> Adjacencies<'a> for InEdges<'g, G>
where
    G: Directed<'g>,
{
    type IncidenceIt = AdjacenciesWrapIt<G::InIt>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt {
        self.0.in_iter(u).into()
    }
}

impl<'a, A, I> GraphIterator<&'a A> for AdjacenciesWrapIt<I>
where
    I: GraphIterator<A>,
{
    type Item = I::Item;

    fn next(&mut self, adj: &&'a A) -> Option<Self::Item> {
        self.0.next(*adj)
    }

    fn size_hint(&self, adj: &&'a A) -> (usize, Option<usize>) {
        self.0.size_hint(*adj)
    }

    fn count(self, adj: &&'a A) -> usize {
        self.0.count(*adj)
    }
}

/// Implement Adjacencies for references.
impl<'a, A> Adjacencies<'a> for &'a A
where
    A: Adjacencies<'a>,
{
    type IncidenceIt = AdjacenciesWrapIt<A::IncidenceIt>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt {
        (*self).neigh_iter(u).into()
    }
}
