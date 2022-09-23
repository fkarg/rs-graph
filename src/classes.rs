// Copyright (c) 2016-2021 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! Some common graph classes.

use crate::builder::{Buildable, Builder};
use crate::num::traits::FromPrimitive;
use crate::traits::Graph;

/// Returns a path with `m` edges.
///
/// The path is directed if G is a digraph.
pub fn path<'a, G>(m: usize) -> G
where
    G: Graph<'a> + Buildable,
{
    let mut b = G::Builder::with_capacities(m + 1, m);
    let nodes: Vec<_> = (0..=m).map(|_| b.add_node()).collect();
    for (u, v) in nodes.iter().zip(nodes.iter().skip(1)) {
        b.add_edge(*u, *v);
    }
    b.into_graph()
}

/// Returns a cycle with length `n`.
///
/// The cycle is directed if G is directed
pub fn cycle<'a, G>(n: usize) -> G
where
    G: Graph<'a> + Buildable,
{
    let mut b = G::Builder::with_capacities(n, n);
    let nodes: Vec<_> = (0..n).map(|_| b.add_node()).collect();
    for (u, v) in nodes.iter().zip(nodes.iter().cycle().skip(1)) {
        b.add_edge(*u, *v);
    }
    b.into_graph()
}

/// Returns the complete graph on `n` nodes.
pub fn complete_graph<'a, G>(n: usize) -> G
where
    G: Graph<'a> + Buildable,
{
    let mut b = G::Builder::with_capacities(n, n * (n - 1) / 2);
    let nodes: Vec<_> = (0..n).map(|_| b.add_node()).collect();
    for (i, &u) in nodes.iter().enumerate() {
        for &v in &nodes[i + 1..] {
            b.add_edge(u, v);
        }
    }
    b.into_graph()
}

/// Returns a complete bipartite graph on `n+m` nodes.
///
/// The edges will run between the first n nodes and the last m nodes.
/// If G is a digraph, the edges will run in this direction.
pub fn complete_bipartite<'a, G>(n: usize, m: usize) -> G
where
    G: Graph<'a> + Buildable,
{
    let mut b = G::Builder::with_capacities(n + m, n * m);
    let nodes: Vec<_> = (0..n + m).map(|_| b.add_node()).collect();
    for &u in &nodes[..n] {
        for &v in &nodes[n..] {
            b.add_edge(u, v);
        }
    }
    b.into_graph()
}

/// Returns a star graph with `n` rays.
///
/// The center node will be the first node. This is equivalent to
/// `complete_bipartite(1,n)`.
///
/// If G is a digraph, the source of all edges will be the center
/// node.
pub fn star<'a, G>(n: usize) -> G
where
    G: Graph<'a> + Buildable,
{
    complete_bipartite::<G>(1, n)
}

/// Returns a hypercube of dimension `d`.
pub fn hypercube<'a, G>(d: u32) -> G
where
    G: Graph<'a> + Buildable,
{
    let n = 2usize.pow(d);
    let mut b = G::Builder::with_capacities(n, n * usize::from_u32(d).unwrap());
    let nodes: Vec<_> = (0..n).map(|_| b.add_node()).collect();
    for i in 0..n {
        for bit in 0..d {
            if i & (1 << bit) == 0 {
                b.add_edge(nodes[i], nodes[i | (1 << bit)]);
            }
        }
    }
    b.into_graph()
}

/// Return a grid graph with `n` columns and `m` rows.
///
/// The nodes are created from left to right and from bottom to top. The
/// following is a grid graph with 5 columns and 4 rows.
///
///   15 - 16 - 17 - 18 - 19
///    |    |    |    |    |
///   10 - 11 - 12 - 13 - 14
///    |    |    |    |    |
///    5 -- 6 -- 7 -- 8 -- 9
///    |    |    |    |    |
///    0 -- 1 -- 2 -- 3 -- 4
///
/// ```
/// use rs_graph::LinkedListGraph;
/// use rs_graph::traits::*;
/// use rs_graph::classes;
///
/// let g: LinkedListGraph = classes::grid(5, 4);
/// assert_eq!(g.num_nodes(), 20);
/// assert_eq!(g.num_edges(), 5*3 + 4*4);
///
/// assert_eq!(g.nodes().filter(|&u| g.neighs(u).count() == 2).count(), 4);
/// assert_eq!(g.nodes().filter(|&u| g.neighs(u).count() == 3).count(), 10);
/// assert_eq!(g.nodes().filter(|&u| g.neighs(u).count() == 4).count(), 6);
/// ```
pub fn grid<'a, G>(n: usize, m: usize) -> G
where
    G: Graph<'a> + Buildable,
{
    let mut b = G::Builder::with_capacities(n * m, (n - 1) * m + n * (m - 1));
    let nodes: Vec<_> = (0..n * m).map(|_| b.add_node()).collect();
    for x in 0..n - 1 {
        for y in 0..m {
            b.add_edge(nodes[y * n + x], nodes[y * n + x + 1]);
        }
    }
    for x in 0..n {
        for y in 0..m - 1 {
            b.add_edge(nodes[y * n + x], nodes[y * n + x + n]);
        }
    }
    b.into_graph()
}

/// Returns a Peterson graph.
pub fn peterson<'a, G>() -> G
where
    G: Graph<'a> + Buildable,
{
    let mut b = G::Builder::with_capacities(10, 15);
    let nodes: Vec<_> = (0..10).map(|_| b.add_node()).collect();
    for i in 0..5 {
        b.add_edge(nodes[i], nodes[(i + 1) % 5]);
        b.add_edge(nodes[i + 5], nodes[(i + 2) % 5 + 5]);
        b.add_edge(nodes[i], nodes[i + 5]);
    }
    b.into_graph()
}

#[cfg(test)]
mod tests {

    use super::{complete_bipartite, complete_graph, cycle, hypercube, path, star};
    use crate::traits::*;
    use crate::Net;
    use std::cmp::{max, min};

    #[test]
    fn test_path() {
        let g = path::<Net>(5);
        assert_eq!(g.num_nodes(), 6);
        assert_eq!(g.num_edges(), 5);
        let mut degrees = vec![0; g.num_nodes()];
        for e in g.edges() {
            let (u, v) = g.enodes(e);
            assert_eq!(min(u.index(), v.index()) + 1, max(u.index(), v.index()));
            degrees[u.index()] += 1;
            degrees[v.index()] += 1;
        }
        assert_eq!(degrees.iter().filter(|x| **x == 1).count(), 2);
        assert_eq!(degrees.iter().filter(|x| **x == 2).count(), g.num_nodes() - 2);
    }

    #[test]
    fn test_cycle() {
        let g = cycle::<Net>(42);
        assert_eq!(g.num_nodes(), 42);
        assert_eq!(g.num_edges(), 42);
        let mut degrees = vec![0; g.num_nodes()];
        for e in g.edges() {
            let (u, v) = g.enodes(e);
            let (u, v) = (u.index(), v.index());
            assert!((min(u, v) + 1 == max(u, v)) || (min(u, v) == 0 && max(u, v) == g.num_nodes() - 1));
            degrees[u] += 1;
            degrees[v] += 1;
        }
        assert!(degrees.into_iter().all(|x| x == 2));
    }

    #[test]
    fn test_complete() {
        let n = 12;
        let g = complete_graph::<Net>(n);
        assert_eq!(g.num_nodes(), n);
        assert_eq!(g.num_edges(), n * (n - 1) / 2);
        let mut degrees = vec![0; n];
        for e in g.edges() {
            let (u, v) = g.enodes(e);
            degrees[u.index()] += 1;
            degrees[v.index()] += 1;
        }
        assert!(degrees.into_iter().all(|x| x == n - 1));
    }

    #[test]
    fn test_complete_bipartite() {
        let n = 13;
        let m = 7;
        let g = complete_bipartite::<Net>(n, m);
        assert_eq!(g.num_nodes(), n + m);
        assert_eq!(g.num_edges(), n * m);
        let mut degrees = vec![0; n + m];
        for e in g.edges() {
            let (u, v) = g.enodes(e);
            let (u, v) = (u.index(), v.index());
            assert!(min(u, v) < n);
            assert!(max(u, v) >= m);
            degrees[u] += 1;
            degrees[v] += 1;
        }
        assert!(degrees[..n].iter().all(|x| *x == m));
        assert!(degrees[n..].iter().all(|x| *x == n));
    }

    #[test]
    fn test_star() {
        let n = 17;
        let g: Net = star(n);
        assert_eq!(g.num_nodes(), n + 1);
        assert_eq!(g.num_edges(), n);
        let mut degrees = vec![0; n + 1];
        for e in g.edges() {
            let (u, v) = g.enodes(e);
            let (u, v) = (u.index(), v.index());
            assert_eq!(min(u, v), 0);
            degrees[u] += 1;
            degrees[v] += 1;
        }
        assert_eq!(degrees[0], n);
        assert!(degrees[1..].iter().all(|x| *x == 1));
    }

    #[test]
    fn test_hypercube() {
        let g: Net = hypercube(3);
        assert_eq!(g.num_nodes(), 8);
        assert_eq!(g.num_edges(), 12);

        let mut edges: Vec<_> = g.edges().map(|e| (g.src(e).index(), g.snk(e).index())).collect();
        edges.sort();

        assert_eq!(
            edges,
            vec![
                (0, 1),
                (0, 2),
                (0, 4),
                (1, 3),
                (1, 5),
                (2, 3),
                (2, 6),
                (3, 7),
                (4, 5),
                (4, 6),
                (5, 7),
                (6, 7),
            ]
        );
    }
}
