/*
 * Copyright (c) 2021, 2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

use num_traits::{Bounded, FromPrimitive, NumAssign, NumCast, Signed, ToPrimitive};
use rs_graph::dimacs;
use rs_graph::mcf::{simplex::Pricing, NetworkSimplex};
use rs_graph::traits::*;
use rs_graph::Net;
use std::error::Error;
use std::fmt::Display;
use std::io::Write;
use std::path::PathBuf;
use std::result::Result;
use std::str::FromStr;

use rustop::opts;
use time::OffsetDateTime;

trait ZeroValue {
    fn zero() -> Self;
}

impl ZeroValue for isize {
    fn zero() -> isize {
        0
    }
}

impl ZeroValue for f64 {
    fn zero() -> f64 {
        1e-9
    }
}

fn run<F>(filename: &str, pricing: Pricing) -> Result<(), Box<dyn Error>>
where
    F: Bounded
        + NumCast
        + NumAssign
        + PartialOrd
        + Copy
        + FromPrimitive
        + ToPrimitive
        + Signed
        + FromStr
        + Display
        + ZeroValue,
    F::Err: Display,
{
    let tstart = OffsetDateTime::now_utc();
    let instance = dimacs::min::read_from_file::<_, F>(filename)?;

    let g: Net = instance.graph;
    let balances = instance.balances;
    let lower = instance.lower;
    let upper = instance.upper;
    let costs = instance.costs;

    let tend = OffsetDateTime::now_utc();
    println!("Instance            : {}", filename);
    println!("Read Time (seconds) : {}", (tend - tstart).as_seconds_f64());
    println!("Graph type          : {}", std::any::type_name::<Net>());
    println!("Value type          : {}", std::any::type_name::<F>());
    println!("Number of nodes     : {}", g.num_nodes());
    println!("Number of edges     : {}", g.num_edges());

    let mut spx = NetworkSimplex::new(&g);
    spx.pricing = pricing;
    spx.set_balances(|u| balances[g.node_id(u)]);
    spx.set_lowers(|e| lower[g.edge_id(e)]);
    spx.set_uppers(|e| upper[g.edge_id(e)]);
    spx.set_costs(|e| costs[g.edge_id(e)]);
    spx.zero = ZeroValue::zero();

    let tstart = OffsetDateTime::now_utc();
    let state = spx.solve();
    let tend = OffsetDateTime::now_utc();
    let soltime = (tend - tstart).as_seconds_f64();

    println!();
    println!("Solution state      : {:?}", state);
    println!("Value               : {:.2}", spx.value().to_f64().unwrap());
    println!("Time (seconds)      : {:.2}", soltime);
    println!("Iterations (total)  : {}", spx.num_iterations());
    println!();
    println!("Write solution to   : {}.sol", filename);

    let solfile = PathBuf::from(format!("{}.sol", filename));
    let f = &mut std::fs::File::create(&solfile)?;
    let fname = solfile
        .file_name()
        .map(|s| s.to_string_lossy())
        .unwrap_or_else(|| "".into());
    writeln!(f, "c Solved with a primal network simplex")?;
    writeln!(f, "c instance            : {}", fname)?;
    writeln!(f, "c solution time       : {:.2} seconds", soltime)?;
    writeln!(f, "c number of iterations: {}", spx.num_iterations())?;
    dimacs::min::write_solution(f, &g, |e| spx.flow(e), spx.value())?;

    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let (args, _) = opts! {
        synopsis "Solve min-cost-flow problem with a network simplex algorithm.";
        param file:String, desc:"Instance file name";
        opt dantzig:bool, desc:"Dantzig's rule pricing (most negative)";
        opt first_eligible:bool, desc:"First eligible edge pricing (round robin)";
        opt multiple_partial:bool, desc:"Multiple Partial Pricing";
        opt floating_point:bool, desc:"Use floating point values";
    }
    .parse_or_exit();

    let pricing = if args.dantzig {
        Pricing::Complete
    } else if args.first_eligible {
        Pricing::RoundRobin
    } else if args.multiple_partial {
        Pricing::MultiplePartial
    } else {
        Pricing::Block
    };

    if args.floating_point {
        run::<f64>(&args.file, pricing)
    } else {
        run::<isize>(&args.file, pricing)
    }
}
