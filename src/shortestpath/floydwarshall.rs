// Copyright (c) 2016, 2017, 2018, 2020, 2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! All-Pairs-Shortest-Path algorithm of Floyd and Warshall.

use crate::num::traits::{Bounded, NumAssign};
use crate::traits::{IndexDigraph, IndexGraph};

/// Solve the All-Pairs-Shortest-Path-Problem with the algorithm of
/// Floyd and Warshall on an undirected graph.
///
/// Returns a 2D vector with entries `(dist, pred)` for each pair of
/// nodes where `dist` is the length of the shortest path and `pred` is
/// the predecessor of the last node.
pub fn undirected<'a, G, W, F>(g: &'a G, weights: F) -> Vec<Vec<Option<(W, G::Node)>>>
where
    G: IndexGraph<'a>,
    W: NumAssign + Ord + Copy + Bounded,
    F: Fn(G::Edge) -> W,
{
    let mut dist: Vec<Vec<Option<(W, G::Node)>>> = vec![vec![None; g.num_nodes()]; g.num_nodes()];

    for u in g.nodes() {
        dist[g.node_id(u)][g.node_id(u)] = Some((W::zero(), u));
    }

    for e in g.edges() {
        let (u, v) = g.enodes(e);
        let uid = g.node_id(u);
        let vid = g.node_id(v);
        let w = weights(e);
        if w < dist[uid][vid].map(|x| x.0).unwrap_or_else(W::max_value) {
            dist[uid][vid] = Some((w, u));
            dist[vid][uid] = Some((w, u));
        }
    }

    for k in 0..g.num_nodes() {
        for u in 0..g.num_nodes() {
            if u == k {
                continue;
            }
            if let Some(&(dist_uk, _)) = dist[u][k].as_ref() {
                for v in 0..g.num_nodes() {
                    if v == k {
                        continue;
                    }
                    if let Some(&(dist_kv, pred_kv)) = dist[k][v].as_ref() {
                        if dist[u][v].map(|x| x.0).unwrap_or_else(W::max_value) > dist_uk + dist_kv {
                            dist[u][v] = Some((dist_uk + dist_kv, pred_kv));
                        }
                    }
                }
            }
        }
    }

    dist
}

/// Solve the All-Pairs-Shortest-Path-Problem with the algorithm of
/// Floyd and Warshall on a directed graph.
///
/// Returns a 2D vector with entries `(dist, pred)` for each pair of
/// nodes where `dist` is the length of the shortest path and `pred` is
/// the predecessor of the last node.
///
/// # Example
/// ```
/// use rs_graph::{LinkedListGraph, Buildable, Builder};
/// use rs_graph::shortestpath::floydwarshall;
/// use rs_graph::traits::IndexGraph;
///
/// let mut weights = vec![];
/// let g = LinkedListGraph::<usize>::new_with(|b| {
///     let nodes = b.add_nodes(5);
///     for &(u,v,w) in [(0,1,6), (0,2,5),
///                      (1,2,7), (1,3,3), (1,4,-2),
///                      (2,3,-4), (3,4,8),
///                      (3,1,-1),
///                      (4,0,2), (4,3,7), ].iter()
///     {
///         b.add_edge(nodes[u], nodes[v]);
///         weights.push(w);
///     }
/// });
///
/// let result = floydwarshall::directed(&g, |e| weights[g.edge_id(e)]);
/// let mut s = [[0; 5]; 5];
/// for (i,v) in result.into_iter().enumerate() {
///     for (j,d) in v.into_iter().enumerate() {
///         s[i][j] = d.unwrap().0;
///     }
/// }
/// assert_eq!(s, [[ 0, 0, 5, 1,-2],
///                [ 0, 0, 5, 1,-2],
///                [-5,-5, 0,-4,-7],
///                [-1,-1, 4, 0,-3],
///                [ 2, 2, 7, 3, 0],]);
/// ```
pub fn directed<'a, G, W, F>(g: &'a G, weights: F) -> Vec<Vec<Option<(W, G::Node)>>>
where
    G: IndexDigraph<'a>,
    W: NumAssign + Ord + Copy + Bounded,
    F: Fn(G::Edge) -> W,
{
    let mut dist: Vec<Vec<Option<(W, G::Node)>>> = vec![vec![None; g.num_nodes()]; g.num_nodes()];

    for u in g.nodes() {
        dist[g.node_id(u)][g.node_id(u)] = Some((W::zero(), u));
    }

    for e in g.edges() {
        let (u, v) = (g.src(e), g.snk(e));
        let uid = g.node_id(u);
        let vid = g.node_id(v);
        let w = weights(e);
        if w < dist[uid][vid].map(|x| x.0).unwrap_or_else(W::max_value) {
            dist[uid][vid] = Some((w, u));
        }
    }

    for k in 0..g.num_nodes() {
        for u in 0..g.num_nodes() {
            if u == k {
                continue;
            }
            if let Some(&(dist_uk, _)) = dist[u][k].as_ref() {
                for v in 0..g.num_nodes() {
                    if v == k {
                        continue;
                    }
                    if let Some(&(dist_kv, pred_kv)) = dist[k][v].as_ref() {
                        if dist[u][v].map(|x| x.0).unwrap_or_else(W::max_value) > dist_uk + dist_kv {
                            dist[u][v] = Some((dist_uk + dist_kv, pred_kv));
                        }
                    }
                }
            }
        }
    }

    dist
}
