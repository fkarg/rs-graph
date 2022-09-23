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
use std::marker::PhantomData;

#[derive(Graph)]
struct MyGraph<'a, I> {
    #[graph]
    graph: LinkedListGraph, // #[graph] not needed for fields named `graph`.
    balances: Vec<I>,
    bounds: Vec<I>,
    phantom: PhantomData<&'a I>,
}

impl<'a, T> From<LinkedListGraph> for MyGraph<'a, T>
where
    T: Default + Clone,
{
    fn from(g: LinkedListGraph) -> MyGraph<'a, T> {
        let n = g.num_nodes();
        let m = g.num_edges();
        MyGraph {
            graph: g,
            balances: vec![T::default(); n],
            bounds: vec![T::default(); m],
            phantom: PhantomData,
        }
    }
}

impl<'a, T> MyGraph<'a, T> {
    fn balance_mut(&mut self, u: Node) -> &mut T {
        &mut self.balances[self.graph.node_id(u)]
    }

    fn bound_mut(&mut self, e: Edge) -> &mut T {
        &mut self.bounds[self.graph.edge_id(e)]
    }
}

#[test]
fn test_simple() -> Result<(), Box<dyn std::error::Error>> {
    let mut g: MyGraph<f64> = classes::path::<LinkedListGraph>(5).into();
    let (s, t) = (g.id2node(0), g.id2node(4));
    *g.balance_mut(s) = 1.0;
    *g.balance_mut(t) = -1.0;
    for eid in 0..g.num_edges() {
        *g.bound_mut(g.id2edge(eid)) = eid as f64;
    }
    Ok(())
}
