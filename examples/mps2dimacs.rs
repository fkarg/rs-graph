/*
 * Copyright (c) 2015-2021 Frank Fischer <frank-fischer@shadow-soft.de>
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

use rs_graph::dimacs::min;
use rs_graph::{mps, Net};
use rustop::opts;
use zopen;

fn int_vec(x: Vec<f64>, what: &str) -> Result<Vec<isize>, Box<dyn std::error::Error>> {
    x.into_iter()
        .map(|v| {
            if v.fract() == 0.0 {
                Ok(v.trunc() as isize)
            } else {
                Err(format!("Found non-integral {} value: {}", what, v).into())
            }
        })
        .collect()
}

fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let (args, _) = opts! {
        synopsis "Convert a file in MPS format to Dimacs format";
        param mps_file:String, desc:"Name of the MPS input file";
        param dimacs_file:String, desc:"Name of the Dimacs output file";
    }
    .parse_or_exit();

    let mps_inst = mps::read::<Net, _>(zopen::read(&args.mps_file)?)?;
    let min_inst = min::Instance {
        graph: mps_inst.graph,
        balances: int_vec(mps_inst.balances, "balance")?,
        lower: int_vec(mps_inst.lower, "lower")?,
        upper: int_vec(mps_inst.upper, "upper")?,
        costs: int_vec(mps_inst.costs, "cost")?,
    };

    min::write(&mut zopen::write(&args.dimacs_file)?, &min_inst)?;

    Ok(())
}
