// Copyright (c) 2016-2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! General algorithms working on graphs.

use crate::builder::{Buildable, Builder};
use crate::traits::{Digraph, Graph, GraphType, IndexDigraph, IndexGraph};

use std::cmp::{max, min};
use std::collections::HashSet;
use std::usize;

/// Returns the complement of `g`.
///
/// # Example
///
/// ```
/// use rs_graph::LinkedListGraph;
/// use rs_graph::traits::{Undirected, IndexGraph, FiniteGraph};
/// use rs_graph::algorithms::complement;
/// use rs_graph::classes::cycle;
/// use std::cmp::{min, max};
///
/// let g: LinkedListGraph = cycle(5);
/// let h: LinkedListGraph = complement(&g);
///
/// assert_eq!(h.num_nodes(), 5);
/// assert_eq!(h.num_edges(), 5);
///
/// let mut edges: Vec<_> = h.edges().map(|e| {
///     let (u, v) = h.enodes(e);
///     let (u, v) = (h.node_id(u), h.node_id(v));
///     (min(u,v), max(u,v))
/// }).collect();
/// edges.sort();
/// assert_eq!(edges, vec![(0,2), (0,3), (1,3), (1,4), (2,4)]);
/// ```
///
/// Note that this function assumes that `g` is a simple graph (no
/// loops or double edges). It will work on multi-graphs, too, but
/// only adjacencies are respected, no multiplicities.
pub fn complement<'g, 'h, G, H>(g: &'g G) -> H
where
    G: IndexGraph<'g>,
    H: Graph<'h> + Buildable,
{
    let mut edges = HashSet::new();
    for e in g.edges() {
        let (u, v) = g.enodes(e);
        edges.insert((min(g.node_id(u), g.node_id(v)), max(g.node_id(u), g.node_id(v))));
    }

    let n = g.num_nodes();
    let mut h = H::Builder::with_capacities(n, n * (n - 1) / 2 - g.num_edges());
    let nodes = h.add_nodes(n);
    for i in 0..n {
        for j in i..n {
            if i < j && !edges.contains(&(i, j)) {
                h.add_edge(nodes[i], nodes[j]);
            }
        }
    }
    h.into_graph()
}

/// Returns the inverse directed graph of `g`.
///
/// For $G=(V,A)$ the returned graph is $G=(V,A')$ with
/// $A' := \{(v,u) \colon (u,v) \in A\}$.
///
/// # Example
///
/// ```
/// use rs_graph::{LinkedListGraph, Buildable, Builder};
/// use rs_graph::algorithms::inverse;
/// use rs_graph::traits::*;
///
/// let g = LinkedListGraph::<usize>::new_with(|b| {
///     let nodes = b.add_nodes(18);
///     for &u in &nodes {
///         for &v in &nodes {
///             if b.node2id(v) > 0 && b.node2id(u) % b.node2id(v) == 0 {
///               b.add_edge(u, v);
///             }
///         }
///     }
/// });
///
/// let h: LinkedListGraph = inverse(&g);
/// assert_eq!(g.num_nodes(), h.num_nodes());
/// assert_eq!(g.num_edges(), h.num_edges());
/// for e in h.edges() {
///     let (u,v) = (h.node_id(h.src(e)), h.node_id(h.snk(e)));
///     assert!(u > 0 && v % u == 0);
/// }
/// ```
///
/// Another example to create a star with all edges directed to the center.
///
/// ```
/// use rs_graph::LinkedListGraph;
/// use rs_graph::traits::*;
/// use rs_graph::classes::star;
/// use rs_graph::algorithms::inverse;
///
/// type G = LinkedListGraph<usize>;
/// let g: G = inverse(&star::<G>(42));
/// assert_eq!(g.num_nodes(), 43);
/// for e in g.edges() {
///     let (u,v) = (g.node_id(g.src(e)), g.node_id(g.snk(e)));
///     assert!(u > 0 && v == 0);
/// }
/// ```
pub fn inverse<'g, 'h, G, H>(g: &'g G) -> H
where
    G: IndexDigraph<'g>,
    H: Digraph<'h> + Buildable,
{
    let mut h = H::Builder::with_capacities(g.num_nodes(), g.num_edges());
    let nodes = h.add_nodes(g.num_nodes());
    for e in g.edges() {
        h.add_edge(nodes[g.node_id(g.snk(e))], nodes[g.node_id(g.src(e))]);
    }
    h.into_graph()
}

/// Determines if a graph is connected.
///
/// The empty graph is connected.
///
/// # Example
///
/// ```
/// use rs_graph::{LinkedListGraph, Graph, Buildable, Builder, classes, algorithms};
///
/// let mut g: LinkedListGraph = classes::cycle(5);
/// assert!(algorithms::is_connected(&g));
///
/// let g = LinkedListGraph::<usize>::new_with(|b| {
///     let nodes = b.add_nodes(5);
///     for i in 0..5 {
///         b.add_edge(nodes[i], nodes[(i + 1) % 5]);
///     }
///     b.add_node();
/// });
///
/// assert!(!algorithms::is_connected(&g));
///
/// ```
pub fn is_connected<'g, G>(g: &'g G) -> bool
where
    G: IndexGraph<'g>,
{
    if g.num_nodes() == 0 {
        return true;
    }

    let mut seen = vec![false; g.num_nodes()];
    let mut q = vec![g.id2node(0)];

    while let Some(u) = q.pop() {
        for (_, v) in g.neighs(u) {
            let vid = g.node_id(v);
            if !seen[vid] {
                seen[vid] = true;
                q.push(v);
            }
        }
    }

    seen.iter().all(|&u| u)
}

/// Determines all components of a graph.
///
/// The function numbers all components and assigns each node the
/// number its containing component. The number of components is
/// returned.
///
/// The empty graph has 0 components.
///
/// # Example
///
/// ```
/// use rs_graph::LinkedListGraph;
/// use rs_graph::builder::{Buildable, Builder};
/// use rs_graph::traits::*;
/// use rs_graph::{algorithms, classes};
///
/// let mut g: LinkedListGraph = classes::cycle(5);
/// {
///     let (ncomps, comps) = algorithms::components(&g);
///     assert_eq!(ncomps, 1);
///     for u in g.nodes() { assert_eq!(comps[g.node_id(u)], 0); }
/// }
///
/// let mut v = None;
/// let g = LinkedListGraph::<usize>::new_with(|b| {
///     let nodes = b.add_nodes(5);
///     for i in 0..5 {
///         b.add_edge(nodes[i], nodes[(i + 1) % 5]);
///     }
///     v = Some(b.add_node());
/// });
///
/// {
///     let v = v.unwrap();
///     let (ncomps, comps) = algorithms::components(&g);
///     assert_eq!(ncomps, 2);
///     for u in g.nodes() { assert_eq!(comps[g.node_id(u)], if u == v { 1 } else { 0 }); }
/// }
/// ```
pub fn components<'g, G>(g: &'g G) -> (usize, Vec<usize>)
where
    G: IndexGraph<'g>,
{
    if g.num_nodes() == 0 {
        return (0, vec![0; g.num_nodes()]);
    }

    let mut components = vec![usize::max_value(); g.num_nodes()];
    let mut q = vec![];
    let mut nodes = g.nodes();
    let mut ncomponents = 0;

    loop {
        // find next node that has not been seen, yet
        while let Some(u) = nodes.next() {
            let uid = g.node_id(u);
            if components[uid] == usize::MAX {
                // found a node, start new component
                components[uid] = ncomponents;
                q.push(u);
                ncomponents += 1;
                break;
            }
        }

        // no unseen node found -> stop
        if q.is_empty() {
            return (ncomponents, components);
        }

        // do dfs from this node
        while let Some(u) = q.pop() {
            let uid = g.node_id(u);
            for (_, v) in g.neighs(u) {
                let vid = g.node_id(v);
                if components[vid] != components[uid] {
                    components[vid] = components[uid];
                    q.push(v);
                }
            }
        }
    }
}

/// Either a node or an edge.
pub enum Item<'a, G>
where
    G: GraphType<'a>,
{
    Node(G::Node),
    Edge(G::Edge),
}

/// Return a subgraph.
///
/// The resulting graph contains all nodes and edges for which the predicate
/// returns *true*.
///
/// # Example
/// ```
/// // Extract a bipartite subgraph.
/// use rs_graph::LinkedListGraph;
/// use rs_graph::traits::*;
/// use rs_graph::classes;
/// use rs_graph::algorithms::*;
///
/// let g: LinkedListGraph = classes::complete_graph(7);
/// let h: LinkedListGraph = subgraph(&g, |i| match i {
///     Item::Node(u) => g.node_id(u) < 6,
///     Item::Edge(e) => {
///         let (u,v) = g.enodes(e);
///         g.node_id(u) % 2 != g.node_id(v) % 2
///     }
/// });
///
/// assert_eq!(h.num_nodes(), 6);
/// assert_eq!(h.num_edges(), 3*3);
/// for u in h.nodes() {
///     let mut neighs = h.neighs(u).map(|(_,v)| h.node_id(v)).collect::<Vec<_>>();
///     neighs.sort();
///     assert_eq!(neighs, if h.node_id(u) % 2 == 0 { vec![1,3,5] } else { vec![0,2,4] });
/// }
/// ```
pub fn subgraph<'g, 'h, G, H, P>(g: &'g G, predicate: P) -> H
where
    G: IndexDigraph<'g>,
    H: Digraph<'h> + Buildable,
    P: Fn(Item<G>) -> bool,
{
    let mut h = H::Builder::with_capacities(g.num_nodes(), g.num_edges());

    let mut nodes = Vec::with_capacity(g.num_nodes());
    for u in g.nodes() {
        nodes.push(if predicate(Item::Node(u)) {
            Some(h.add_node())
        } else {
            None
        });
    }

    for e in g.edges() {
        let (u, v) = g.enodes(e);
        if let (Some(u), Some(v)) = (nodes[g.node_id(u)], nodes[g.node_id(v)]) {
            if predicate(Item::Edge(e)) {
                h.add_edge(u, v);
            }
        }
    }
    h.into_graph()
}

#[cfg(test)]
mod tests {
    use crate::algorithms::complement;
    use crate::classes::*;
    use crate::linkedlistgraph::{Edge, LinkedListGraph};
    use crate::traits::*;
    use std::cmp::{max, min};

    #[test]
    fn test_complement() {
        let g: LinkedListGraph = cycle(5);
        let h: LinkedListGraph = complement(&g);
        let l: LinkedListGraph = complement(&h);

        fn to_id(g: &LinkedListGraph, e: Edge) -> (usize, usize) {
            let (u, v) = g.enodes(e);
            let (u, v) = (g.node_id(u), g.node_id(v));
            (min(u, v), max(u, v))
        }

        let mut gedges: Vec<_> = g.edges().map(|e| to_id(&g, e)).collect();
        gedges.sort();

        let mut hedges: Vec<_> = h.edges().map(|e| to_id(&h, e)).collect();
        hedges.sort();

        let mut ledges: Vec<_> = g.edges().map(|e| to_id(&l, e)).collect();
        ledges.sort();

        assert_eq!(hedges, vec![(0, 2), (0, 3), (1, 3), (1, 4), (2, 4)]);
        assert_eq!(gedges, ledges);
    }
}
