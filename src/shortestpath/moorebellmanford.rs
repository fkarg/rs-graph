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

#![allow(clippy::type_complexity)]

use crate::num::traits::NumAssign;

use crate::traits::{Graph, IndexDigraph, IndexGraph};

/// The shortest-path algorithm by Moore-Bellman-Ford on a directed graph.
///
/// The function returns pair. The first element is the vector of the
/// incoming edge for each (reachable) node. The second element a node
/// on a negative cylce if it exists, otherwise it is `None`.
///
/// # Example
///
/// ```
/// use rs_graph::{LinkedListGraph, Buildable, Builder, traits::*};
/// use rs_graph::shortestpath::moorebellmanford;
///
/// let mut weights = vec![];
/// let mut g = LinkedListGraph::<usize>::new_with(|b| {
///     let nodes = b.add_nodes(7);
///     for &(u,v,w) in [(0,1,-8), (1,4,-3), (2,0,2), (2,1,1), (2,5,-3), (3,1,0), (3,2,5),
///                      (4,3,8), (5,3,-1), (6,3,4), (6,4,6), (6,5,3)].iter()
///     {
///         b.add_edge(nodes[u], nodes[v]);
///         weights.push(w);
///     }
/// });
///
/// let (pred, cycle) = moorebellmanford::directed(&g, |e| weights[g.edge_id(e)], g.id2node(6));
/// assert_eq!(cycle, None);
/// assert_eq!(pred[6], None);
/// for &(u,p) in [(0,2), (1,0), (2,3), (4,1), (5,6)].iter() {
///     assert_eq!(g.src(pred[u].unwrap()), g.id2node(p));
/// }
/// ```
pub fn directed<'a, G, W, F>(g: &'a G, weights: F, src: G::Node) -> (Vec<Option<G::Edge>>, Option<G::Node>)
where
    G: 'a + IndexDigraph<'a>,
    W: NumAssign + Ord + Copy,
    F: Fn(G::Edge) -> W,
{
    let mut pred = vec![None; g.num_nodes()];
    let mut dist = vec![W::zero(); g.num_nodes()];
    let src = g.node_id(src);

    dist[src] = W::zero();

    for i in 0..g.num_nodes() {
        let mut changed = false;
        for e in g.edges() {
            let (u, v) = (g.src(e), g.snk(e));
            let uid = g.node_id(u);
            let vid = g.node_id(v);

            // skip source nodes that have not been seen, yet
            if uid != src && pred[uid].is_none() {
                continue;
            }

            let newdist = dist[uid] + weights(e);
            if dist[vid] > newdist || pred[vid].is_none() {
                dist[vid] = newdist;
                pred[vid] = Some(e);
                changed = true;

                if i + 1 == g.num_nodes() {
                    return (pred, Some(v));
                }
            }
        }
        if !changed {
            break;
        }
    }

    (pred, None)
}

/// The shortest-path algorithm by Moore-Bellman-Ford on an undirected graph.
///
/// The function returns pair. The first element is the vector of the
/// incoming edge for each (reachable) node. The second element a node
/// on a negative cylce if it exists, otherwise it is `None`.
pub fn undirected<'a, G, W, F>(g: &'a G, weights: F, src: G::Node) -> (Vec<Option<G::Edge>>, Option<G::Node>)
where
    G: 'a + IndexGraph<'a> + Graph<'a>,
    W: NumAssign + Ord + Copy,
    F: Fn(G::Edge) -> W,
{
    let mut pred = vec![None; g.num_nodes()];
    let mut dist = vec![W::zero(); g.num_nodes()];
    let src = g.node_id(src);

    dist[src] = W::zero();

    for i in 0..g.num_nodes() {
        let mut changed = false;
        for e in g.edges() {
            let (u, v) = g.enodes(e);
            for &(u, v) in &[(u, v), (v, u)] {
                // skip source nodes that have not been seen, yet
                let uid = g.node_id(u);
                let vid = g.node_id(v);
                if uid != src && pred[uid].is_none() {
                    continue;
                }

                let newdist = dist[uid] + weights(e);
                if dist[vid] > newdist || pred[vid].is_none() {
                    dist[vid] = newdist;
                    pred[vid] = Some(e);
                    changed = true;

                    if i + 1 == g.num_nodes() {
                        return (pred, Some(v));
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    (pred, None)
}
