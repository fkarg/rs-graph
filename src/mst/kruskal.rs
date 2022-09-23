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

//! Implementation of Kruskal's algorithm

use crate::traits::IndexGraph;

/// Run Kruskal's algorithm to solve the *Minimum Spanning Tree*
/// problem on a graph.
///
/// * `g` is the undirected graph `weights` the edge weights
///
/// The algorithm actually solves a minimum spanning *forest* problem
/// if the graph is not connected. This can easily be verified by
/// checking the number of returned edges.
///
/// # Example
///
/// ```
/// use rs_graph::{Net, traits::*};
/// use rs_graph::mst::kruskal;
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
/// let tree = kruskal(&graph, |e| weights[graph.edge_id(e)]);
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
pub fn kruskal<'a, 'b, G, W, F>(g: &'a G, weights: F) -> Vec<G::Edge>
where
    G: IndexGraph<'a>,
    W: Ord,
    F: Fn(G::Edge) -> W,
{
    let mut edges: Vec<_> = g.edges().collect();
    edges.sort_by_key(|&e| weights(e));

    // parent map for finding
    let mut comps = vec![Component::Root(0); g.num_nodes()];
    let mut tree = Vec::with_capacity(g.num_nodes() - 1);

    for e in edges {
        let (u, v) = g.enodes(e);
        let u = g.node_id(u);
        let v = g.node_id(v);
        let (uroot, udepth) = find_root(&comps, u);
        let (vroot, vdepth) = find_root(&comps, v);
        if uroot != vroot {
            tree.push(e);
            if g.num_nodes() - 1 == tree.len() {
                break;
            }
            if udepth < vdepth {
                comps[uroot] = Component::Node(vroot);
            } else {
                comps[vroot] = Component::Node(uroot);
                if udepth == vdepth {
                    comps[uroot] = Component::Root(udepth + 1);
                }
            }
        }
    }

    tree
}

/// Union-Find data-structure for Kruskal.
#[derive(Clone, Copy)]
enum Component {
    /// The root element with the tree's depth.
    Root(usize),
    /// An inner node with the parent node.
    Node(usize),
}

/// Return the root node and the tree's depth of node `u`.
fn find_root(comps: &[Component], u: usize) -> (usize, usize) {
    let mut v = u;
    loop {
        match comps[v] {
            Component::Node(parent) => v = parent,
            Component::Root(depth) => return (v, depth),
        }
    }
}
