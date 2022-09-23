/*
 * Copyright (c) 2021 Frank Fischer <frank-fischer@shadow-soft.de>
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

use rs_graph::classes;
use rs_graph::linkedlistgraph::*;
use rs_graph::traits::*;
use rs_graph_derive::Graph;

#[derive(Graph)]
struct MyGraph {
    #[graph]
    graph: LinkedListGraph, // #[graph] not needed for fields named `graph`.
    balances: Vec<f64>,
    bounds: Vec<f64>,
}

impl From<LinkedListGraph> for MyGraph {
    fn from(g: LinkedListGraph) -> MyGraph {
        let n = g.num_nodes();
        let m = g.num_edges();
        MyGraph {
            graph: g,
            balances: vec![0.0; n],
            bounds: vec![0.0; m],
        }
    }
}

impl MyGraph {
    fn balance_mut(&mut self, u: Node) -> &mut f64 {
        &mut self.balances[self.graph.node_id(u)]
    }

    fn bound_mut(&mut self, e: Edge) -> &mut f64 {
        &mut self.bounds[self.graph.edge_id(e)]
    }
}

#[test]
fn test_simple() -> Result<(), Box<dyn std::error::Error>> {
    let mut g: MyGraph = classes::path::<LinkedListGraph>(5).into();
    let (s, t) = (g.id2node(0), g.id2node(4));
    *g.balance_mut(s) = 1.0;
    *g.balance_mut(t) = -1.0;
    for eid in 0..g.num_edges() {
        *g.bound_mut(g.id2edge(eid)) = eid as f64;
    }
    Ok(())
}
