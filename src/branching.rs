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

//! Compute a maximum weight branching.

use crate::builder::{Buildable, Builder};
use crate::linkedlistgraph::LinkedListGraph;
use crate::traits::{IndexDigraph, IndexGraph};

use crate::num::traits::NumAssign;

#[allow(clippy::cognitive_complexity)]
pub fn max_weight_branching<'a, G, W>(g: &'a G, weights: &[W]) -> Vec<G::Edge>
where
    G: IndexDigraph<'a>,
    W: NumAssign + Ord + Copy,
{
    // find non-cycle-free subset
    let mut inarcs = vec![None; g.num_nodes()];
    for e in g.edges() {
        let u = g.snk(e);
        let uid = g.node_id(u);
        let w = weights[g.edge_id(e)];
        if let Some((_, max_w)) = inarcs[uid] {
            if max_w < w {
                inarcs[uid] = Some((e, w))
            }
        } else if w > W::zero() {
            inarcs[uid] = Some((e, w))
        }
    }

    let mut newnodes = vec![None; g.num_nodes()];
    let mut newg = LinkedListGraph::<usize>::new_builder();

    // find cycles
    let mut label = vec![0; g.num_nodes()];
    let mut diffweights = vec![W::zero(); g.num_nodes()];
    for u in g.nodes() {
        let uid = g.node_id(u);
        if label[uid] != 0 {
            continue;
        } // node already seen

        // run along predecessors of unseen nodes
        let mut vid = uid;
        while label[vid] == 0 {
            label[vid] = 1;
            if let Some((e, _)) = inarcs[vid] {
                vid = g.node_id(g.src(e));
            } else {
                break;
            }
        }

        if let Some((e, w_e)) = inarcs[vid] {
            // last node has an incoming arc ...
            if label[vid] == 1 {
                // ... and has been seen on *this* path
                // we have found a cycle
                // find the minimal weight
                let mut minweight = w_e;
                let mut wid = g.node_id(g.src(e));
                while wid != vid {
                    let (e, w_e) = inarcs[wid].unwrap();
                    minweight = minweight.min(w_e);
                    wid = g.node_id(g.src(e));
                }

                // contract the cycle and compute the weight difference
                // for each node
                let contracted_node = newg.add_node();
                newnodes[vid] = Some(contracted_node);
                diffweights[vid] = w_e - minweight;
                label[vid] = 2;
                let mut wid = g.node_id(g.src(e));
                while wid != vid {
                    newnodes[wid] = Some(contracted_node);
                    label[wid] = 2;
                    let (e, w_e) = inarcs[wid].unwrap();
                    diffweights[wid] = w_e - minweight;
                    wid = g.node_id(g.src(e));
                }
            }
        }

        // add all remaining nodes on the path as single nodes
        let mut vid = uid;
        while label[vid] == 1 {
            newnodes[vid] = Some(newg.add_node());
            label[vid] = 2;
            if let Some((e, _)) = inarcs[vid] {
                vid = g.node_id(g.src(e));
            } else {
                break;
            }
        }
    }

    if newg.num_nodes() == g.num_nodes() {
        // nothing contracted => found a branching
        return inarcs.into_iter().filter_map(|e| e.map(|(e, _)| e)).collect();
    }

    // add arcs
    let mut newweights = vec![];
    let mut newarcs = vec![];
    for e in g.edges() {
        let newu = newnodes[g.node_id(g.src(e))].unwrap();
        let newv = newnodes[g.node_id(g.snk(e))].unwrap();
        if newu != newv {
            let w_e = weights[g.edge_id(e)];
            if w_e > W::zero() {
                newg.add_edge(newu, newv);
                newarcs.push(e);
                newweights.push(w_e - diffweights[g.node_id(g.snk(e))]);
            }
        }
    }

    let newg = newg.into_graph();

    // recursively determine branching on smaller graph
    let newbranching = max_weight_branching(&newg, &newweights[..]);
    let mut branching = vec![];

    // add original arcs
    for newa in newbranching {
        let e = newarcs[newg.edge_id(newa)];
        branching.push(e);
        let uid = g.node_id(g.snk(e));
        label[uid] = 3;
        // if sink of arc is a contraction node, add the cycle
        if let Some((inarc, _)) = inarcs[uid] {
            if inarc != e {
                let mut vid = g.node_id(g.src(inarc));
                while vid != uid {
                    label[vid] = 3;
                    let e = inarcs[vid].unwrap().0;
                    branching.push(e);
                    vid = g.node_id(g.src(e));
                }
            }
        }
    }

    // Now find all nodes that are not contained in the branching.
    // These nodes might be contained in a cycle, we add that cycle
    // except for the cheapest arc.
    for u in g.nodes() {
        let uid = g.node_id(u);
        if label[uid] == 2 {
            label[uid] = 3;
            if let Some((mut minarc, mut min_w)) = inarcs[uid] {
                let mut vid = g.node_id(g.src(minarc));
                while label[vid] != 3 {
                    label[vid] = 3;
                    if let Some((e, w_e)) = inarcs[vid] {
                        if w_e >= min_w {
                            branching.push(e);
                        } else {
                            branching.push(minarc);
                            minarc = e;
                            min_w = w_e;
                        }
                        vid = g.node_id(g.src(e));
                    } else {
                        break;
                    }
                }
            }
        }
    }

    branching
}

#[cfg(test)]
mod tests {
    use crate::branching::max_weight_branching;
    use crate::traits::IndexGraph;
    use crate::{Buildable, Builder, LinkedListGraph};

    #[test]
    fn test_branching1() {
        let mut g = LinkedListGraph::<usize>::new_builder();
        let mut weights = vec![];
        let nodes = g.add_nodes(9);

        for &(u, v, c) in [
            (1, 4, 17u32),
            (1, 5, 5),
            (1, 3, 18),
            (2, 1, 21),
            (2, 6, 17),
            (2, 7, 12),
            (3, 2, 21),
            (3, 8, 15),
            (4, 9, 12),
            (5, 2, 12),
            (5, 4, 12),
            (6, 5, 4),
            (6, 7, 13),
            (7, 3, 14),
            (7, 8, 12),
            (8, 9, 18),
            (9, 1, 19),
            (9, 3, 15),
        ]
        .iter()
        {
            g.add_edge(nodes[u - 1], nodes[v - 1]);
            weights.push(c);
        }

        let g = g.into_graph();

        let branching = max_weight_branching(&g, &weights);
        assert_eq!(branching.iter().fold(0, |acc, &e| acc + weights[g.edge_id(e)]), 131);
    }

    #[test]
    fn test_branching2() {
        let mut g = LinkedListGraph::<usize>::new_builder();
        let mut weights = vec![];
        let nodes = g.add_nodes(9);

        for &(u, v, c) in [
            (2, 1, 3),
            (1, 3, 4),
            (6, 3, 3),
            (6, 7, 1),
            (7, 4, 3),
            (1, 2, 10),
            (4, 1, 5),
            (3, 4, 5),
            (4, 5, 2),
            (4, 6, 4),
            (5, 6, 2),
        ]
        .iter()
        {
            g.add_edge(nodes[u - 1], nodes[v - 1]);
            weights.push(c);
        }

        let g = g.into_graph();
        let branching = max_weight_branching(&g, &weights);
        assert_eq!(branching.iter().fold(0, |acc, &e| acc + weights[g.edge_id(e)]), 28);
    }
}
