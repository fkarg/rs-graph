/*
 * Copyright (c) 2015-2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

use num_traits::ToPrimitive;
use time::OffsetDateTime;

use rustop::opts;

use rs_graph::dimacs;
use rs_graph::maxflow::EdmondsKarp;
use rs_graph::traits::*;
use rs_graph::Net;

use std::fmt::Display;

fn run<'a, G, F, Us>(g: &mut EdmondsKarp<'a, G, F>, src: G::Node, snk: G::Node, upper: Us, niter: usize)
where
    G: 'a + IndexDigraph<'a>,
    F: Display + num_traits::NumAssign + Ord + Copy,
    Us: Fn(G::Edge) -> F + Copy,
{
    {
        let tstart = OffsetDateTime::now_utc();
        for _ in 0..niter {
            g.solve(src, snk, upper);
        }
        let tend = OffsetDateTime::now_utc();
        println!("Time: {}", (tend - tstart).as_seconds_f64());
        println!("Flow: {}", g.value());
    }
}

fn main() {
    let (args, _) = opts! {
        synopsis "Solve max-flow problem with the algorithm of Edmonds-Karp.";
        opt num:usize=1, desc:"Number of times the algorithm is repeated.";
        param file:String, desc:"Instance file name";
    }
    .parse_or_exit();

    let tstart = OffsetDateTime::now_utc();
    let instance = dimacs::max::read_from_file(&args.file).unwrap();

    let g: Net = instance.graph;
    let s = instance.src;
    let t = instance.snk;
    let upper: Vec<_> = instance.upper.into_iter().map(|u| u.to_i32().unwrap()).collect();

    let tend = OffsetDateTime::now_utc();
    println!("Time: {}", (tend - tstart).as_seconds_f64());
    println!("  graph: {}", std::any::type_name::<Net>());
    println!("  number of nodes: {}", g.num_nodes());
    println!("  number of arcs: {}", g.num_edges());

    let mut d = EdmondsKarp::new(&g);
    run(&mut d, s, t, |e| upper[g.edge_id(e)], args.num);

    assert!(g.edges().all(|e| d.flow(e) >= 0 && d.flow(e) <= upper[g.edge_id(e)]));
    assert!(g.nodes().filter(|&u| u != s && u != t).all(
        |u| g.outedges(u).map(|(e, _)| d.flow(e)).sum::<i32>() == g.inedges(u).map(|(e, _)| d.flow(e)).sum::<i32>()
    ));
    assert_eq!(
        g.outedges(s).map(|(e, _)| d.flow(e)).sum::<i32>() - g.inedges(s).map(|(e, _)| d.flow(e)).sum::<i32>(),
        d.value()
    );
}
