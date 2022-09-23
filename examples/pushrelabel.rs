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

use time::OffsetDateTime;

use rustop::opts;

use rs_graph::dimacs;
use rs_graph::maxflow::PushRelabel;
use rs_graph::traits::*;
use rs_graph::Net;

use std::fmt::{Debug, Display};

use num_traits::{FromPrimitive, NumAssign};
use ordered_float::NotNan;
use std::iter::Sum;

fn run<'a, G, F, Us>(g: &mut PushRelabel<'a, G, F>, src: G::Node, snk: G::Node, upper: Us, niter: usize)
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

fn read_and_run<F>(filename: &str, num: usize, global_relabelling: bool, typ: &str)
where
    F: Debug + Display + NumAssign + FromPrimitive + Copy + Ord + Sum,
{
    let tstart = OffsetDateTime::now_utc();
    let instance = dimacs::max::read_from_file(filename).unwrap();

    let g: Net = instance.graph;
    let s = instance.src;
    let t = instance.snk;
    let upper: Vec<_> = instance.upper.into_iter().map(|u| F::from_usize(u).unwrap()).collect();

    let tend = OffsetDateTime::now_utc();
    println!("Time: {}", (tend - tstart).as_seconds_f64());
    println!("  graph: {}", std::any::type_name::<Net>());
    println!("  number type: {}", typ);
    println!(
        "  global-relabelling heuristic: {}",
        if global_relabelling { "YES" } else { "NO" }
    );
    println!("  number of nodes: {}", g.num_nodes());
    println!("  number of arcs: {}", g.num_edges());

    let mut d = PushRelabel::new(&g);
    d.use_global_relabelling = global_relabelling;
    run(&mut d, s, t, |e| upper[g.edge_id(e)], num);

    println!("  number of relabels: {}", d.cnt_relabel);

    assert!(g
        .edges()
        .all(|e| d.flow(e) >= F::zero() && d.flow(e) <= upper[g.edge_id(e)]));

    assert!(g.nodes().filter(|&u| u != s && u != t).all(|u| {
        let f_out = g.outedges(u).map(|(e, _)| d.flow(e)).sum::<F>();
        let f_in = g.inedges(u).map(|(e, _)| d.flow(e)).sum::<F>();
        f_out == f_in
    }));

    assert_eq!(
        {
            let f_out = g.outedges(s).map(|(e, _)| d.flow(e)).sum::<F>();
            let f_in = g.inedges(s).map(|(e, _)| d.flow(e)).sum::<F>();
            f_out - f_in
        },
        d.value()
    );
}

fn main() {
    let (args, _) = opts! {
        synopsis "Solve max-flow problem with a push-relabel algorithm.";
        opt global_relabelling:bool, desc:"Use global-relabel heuristic.";
        opt num:usize=1, desc:"Number of times the algorithm is repeated.";
        opt real:bool, desc:"Use real valued flows.";
        param file:String, desc:"Instance file name";
    }
    .parse_or_exit();

    if !args.real {
        read_and_run::<i32>(&args.file, args.num, args.global_relabelling, "i32");
    } else {
        read_and_run::<NotNan<f64>>(&args.file, args.num, args.global_relabelling, "f64");
    }
}
