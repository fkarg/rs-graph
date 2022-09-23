/*
 * Copyright (c) 2018-2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! This is a graph adaptor suppressing some edges.

//! # Example
//!
//! ```
//! use rs_graph::Net;
//! use rs_graph::traits::*;
//! use rs_graph::classes;
//! use rs_graph::filtered::*;
//!
//! let g = classes::peterson::<Net>();
//! let h = filter(&g, |&e| {
//!   let (u,v) = g.enodes(e);
//!   (g.node_id(u) < 5) == (g.node_id(v) < 5)
//! });
//!
//! assert_eq!(h.num_edges(), 10);
//!
//! for u in h.nodes() {
//!     assert_eq!(h.neighs(u).count(), 2);
//! }
//! ```

use crate::traits::{Directed, DirectedEdge, FiniteDigraph, FiniteGraph, GraphIterator, GraphType, Undirected};

pub struct FilteredGraph<'a, G, P>
where
    G: GraphType<'a>,
    P: for<'r> Fn(&'r G::Edge) -> bool,
{
    graph: &'a G,
    predicate: P,
}

#[derive(Clone)]
pub struct Filtered<I>(I);

impl<'a, G, P, I> GraphIterator<FilteredGraph<'a, G, P>> for Filtered<I>
where
    G: GraphType<'a>,
    P: for<'r> Fn(&'r G::Edge) -> bool,
    I: GraphIterator<G, Item = (G::Edge, G::Node)>,
{
    type Item = I::Item;

    fn next(&mut self, g: &FilteredGraph<'a, G, P>) -> Option<Self::Item> {
        while let Some((e, v)) = self.0.next(g.graph) {
            if (g.predicate)(&e) {
                return Some((e, v));
            }
        }
        None
    }
}

#[derive(Clone)]
pub struct FilteredIncidentIt<I>(I);

impl<'a, G, P, I> GraphIterator<FilteredGraph<'a, G, P>> for FilteredIncidentIt<I>
where
    G: Directed<'a>,
    P: for<'r> Fn(&'r G::Edge) -> bool,
    I: GraphIterator<G, Item = (G::DirectedEdge, G::Node)>,
{
    type Item = I::Item;

    fn next(&mut self, g: &FilteredGraph<'a, G, P>) -> Option<Self::Item> {
        while let Some((e, v)) = self.0.next(g.graph) {
            if (g.predicate)(&e.edge()) {
                return Some((e, v));
            }
        }
        None
    }
}

#[derive(Clone)]
pub struct FilterWrapIt<I>(I);

impl<'a, G, P, I> GraphIterator<FilteredGraph<'a, G, P>> for FilterWrapIt<I>
where
    G: GraphType<'a>,
    P: for<'r> Fn(&'r G::Edge) -> bool,
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self, g: &FilteredGraph<'a, G, P>) -> Option<I::Item> {
        self.0.next(g.graph)
    }

    fn size_hint(&self, g: &FilteredGraph<'a, G, P>) -> (usize, Option<usize>) {
        self.0.size_hint(g.graph)
    }

    fn count(self, g: &FilteredGraph<'a, G, P>) -> usize {
        self.0.count(g.graph)
    }
}

#[derive(Clone)]
pub struct FilterEdgeIt<I>(I);

impl<'a, G, P> GraphIterator<FilteredGraph<'a, G, P>> for FilterEdgeIt<G::EdgeIt>
where
    G: FiniteGraph<'a>,
    P: for<'r> Fn(&'r G::Edge) -> bool,
{
    type Item = G::Edge;

    fn next(&mut self, g: &FilteredGraph<'a, G, P>) -> Option<G::Edge> {
        while let Some(e) = self.0.next(g.graph) {
            if (g.predicate)(&e) {
                return Some(e);
            }
        }
        None
    }
}

pub struct FilterNeighIter<'a, I, P> {
    it: I,
    predicate: &'a P,
}

impl<'a, I, P, N, E> Iterator for FilterNeighIter<'a, I, P>
where
    P: for<'r> Fn(&'r E) -> bool,
    I: Iterator<Item = (E, N)>,
{
    type Item = (E, N);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((e, v)) = self.it.next() {
            if (self.predicate)(&e) {
                return Some((e, v));
            }
        }
        None
    }
}

impl<'a, G, P> GraphType<'a> for FilteredGraph<'a, G, P>
where
    G: GraphType<'a>,
    P: 'a + for<'r> Fn(&'r G::Edge) -> bool,
{
    type Node = G::Node;

    type Edge = G::Edge;
}

impl<'a, G, P> FiniteGraph<'a> for FilteredGraph<'a, G, P>
where
    G: FiniteGraph<'a>,
    P: 'a + for<'r> Fn(&'r G::Edge) -> bool,
{
    type NodeIt = FilterWrapIt<G::NodeIt>;

    type EdgeIt = FilterEdgeIt<G::EdgeIt>;

    fn num_nodes(&self) -> usize {
        self.graph.num_nodes()
    }

    fn num_edges(&self) -> usize {
        Iterator::count(self.graph.edges().filter(&self.predicate))
    }

    fn nodes_iter(&'a self) -> Self::NodeIt {
        FilterWrapIt(self.graph.nodes_iter())
    }

    fn edges_iter(&self) -> Self::EdgeIt {
        FilterEdgeIt(self.graph.edges_iter())
    }

    fn enodes(&'a self, e: Self::Edge) -> (Self::Node, Self::Node) {
        debug_assert!((self.predicate)(&e), "Edge has been filtered");
        self.graph.enodes(e)
    }
}

impl<'a, G, P> FiniteDigraph<'a> for FilteredGraph<'a, G, P>
where
    G: FiniteDigraph<'a>,
    P: 'a + for<'r> Fn(&'r G::Edge) -> bool,
{
    fn src(&'a self, e: Self::Edge) -> Self::Node {
        debug_assert!((self.predicate)(&e), "Edge has been filtered");
        self.graph.src(e)
    }

    fn snk(&'a self, e: Self::Edge) -> Self::Node {
        debug_assert!((self.predicate)(&e), "Edge has been filtered");
        self.graph.snk(e)
    }
}

impl<'a, G, P> Undirected<'a> for FilteredGraph<'a, G, P>
where
    G: Undirected<'a>,
    P: 'a + for<'r> Fn(&'r G::Edge) -> bool,
{
    type NeighIt = Filtered<G::NeighIt>;

    fn neigh_iter(&'a self, u: Self::Node) -> Self::NeighIt {
        Filtered(self.graph.neigh_iter(u))
    }
}

impl<'a, G, P> Directed<'a> for FilteredGraph<'a, G, P>
where
    G: Directed<'a>,
    P: 'a + for<'r> Fn(&'r G::Edge) -> bool,
{
    type OutIt = Filtered<G::OutIt>;

    type InIt = Filtered<G::InIt>;

    type IncidentIt = FilteredIncidentIt<G::IncidentIt>;

    type DirectedEdge = G::DirectedEdge;

    fn out_iter(&'a self, u: Self::Node) -> Self::OutIt {
        Filtered(self.graph.out_iter(u))
    }

    fn in_iter(&'a self, u: Self::Node) -> Self::InIt {
        Filtered(self.graph.in_iter(u))
    }

    fn incident_iter(&'a self, u: Self::Node) -> Self::IncidentIt {
        FilteredIncidentIt(self.graph.incident_iter(u))
    }
}

pub fn filter<'a, G, P>(graph: &'a G, predicate: P) -> FilteredGraph<'a, G, P>
where
    G: GraphType<'a>,
    P: for<'r> Fn(&'r G::Edge) -> bool,
{
    FilteredGraph { graph, predicate }
}
