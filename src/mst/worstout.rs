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

//! Implementation of Worst-Out-Greedy for the Minium-Spanning-Tree problem

use crate::traits::IndexGraph;

/// Run Worst-Out-Greedy algorithm to solve the *Minimum Spanning Tree*
/// problem on a graph.
///
/// * `g` is the undirected graph `weights` the edge weights
///
/// The algorithm actually solved a minimum spanning *forest* problem
/// in the graph. This can easily be verified by checking the size of
/// the returned vector.
///
/// # Example
///
/// ```
/// use rs_graph::{Net, traits::*};
/// use rs_graph::mst::worstout;
/// use rs_graph::string::{Data, from_ascii};
///
/// let Data { graph, weights, nodes } = from_ascii::<Net>(r"
///            ------9-----
///           /            \
///       ---a---9--   --2--b
///      /   |\     \ /     |\
///     4    5 \     c      4 6
///    /     |  -7-  |\     |  \
///   d---1--e-    \ 8 --2--f-3-g
///    \     | \    \|     /|   |
///     4    |  -9---h---9- |   |
///      \   3      / \     9  /
///       \  | -10--   -8-- | 9
///        \ |/            \|/
///         -i------18------j
///     ").unwrap();
/// let a = nodes[&'a'];
/// let b = nodes[&'b'];
/// let c = nodes[&'c'];
/// let d = nodes[&'d'];
/// let e = nodes[&'e'];
/// let f = nodes[&'f'];
/// let g = nodes[&'g'];
/// let h = nodes[&'h'];
/// let i = nodes[&'i'];
/// let j = nodes[&'j'];
///
/// // run the algorithm
/// let tree = worstout(&graph, |e| weights[graph.edge_id(e)]);
///
/// // check the results
/// let mut sum = 0;
/// for &e in &tree { sum += weights[graph.edge_id(e)]; }
/// assert_eq!(sum, 38);
///
/// let mut tree = tree.into_iter()
///      .map(|e| graph.enodes(e))
///      .map(|(u,v)| if graph.node_id(u) > graph.node_id(v) { (v,u) } else { (u,v) })
///      .collect::<Vec<_>>();
/// tree.sort_by_key(|&(u,v)| (graph.node_id(u), graph.node_id(v)));
///
/// assert_eq!(tree, vec![(a,d), (a,h), (b,c), (c,f), (c,h), (d,e), (e,i), (f,g), (h,j)]);
/// ```
pub fn worstout<'a, 'b, G, W, F>(g: &'a G, weights: F) -> Vec<G::Edge>
where
    G: IndexGraph<'a>,
    W: Copy + Ord,
    F: Fn(G::Edge) -> W,
{
    let mut used = vec![true; g.num_edges()];
    let mut edges: Vec<_> = g.edges().collect();
    edges.sort_by_key(|&e| weights(e));

    let mut stack = Vec::with_capacity(g.num_nodes());
    let mut seen = vec![false; g.num_nodes()];
    for e in edges.into_iter().rev() {
        let (u, v) = g.enodes(e);

        // dfs from u to v
        seen.fill(false);
        seen[g.node_id(u)] = true;
        stack.clear();
        stack.push(u);

        // mark this edge as not used, so dfs ignores it
        used[g.edge_id(e)] = false;
        let mut found = false;
        while let Some(x) = stack.pop() {
            for (_, y) in g.neighs(x).filter(|&(f, _)| used[g.edge_id(f)]) {
                if !seen[g.node_id(y)] {
                    if y == v {
                        found = true;
                        break;
                    }
                    seen[g.node_id(y)] = true;
                    stack.push(y);
                }
            }
        }

        // if we have not found another path, keep e
        used[g.edge_id(e)] = !found;
    }

    g.edges().filter(|&e| used[g.edge_id(e)]).collect()
}
