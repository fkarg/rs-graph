/*
 * Copyright (c) 2020, 2021, 2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

use rs_graph::dimacs;
use rs_graph::maxflow::{dinic, edmondskarp, PushRelabel};
use rs_graph::traits::IndexGraph;
use rs_graph::LinkedListGraph;

use num_traits::ToPrimitive;
use std::error::Error;

const TESTS: &'static [(&'static str, i32, bool)] = &[
    ("tests/maxflow_test1.dat", 211846, false),
    ("tests/maxflow_test2.dat", 2135, false),
    ("tests/maxflow_test3.dat", 351015, true),
    ("tests/maxflow_test4.dat", 2344, true),
];

#[test]
fn test_edmondskarp() -> Result<(), Box<dyn Error>> {
    for &(file, expected, hard) in TESTS {
        if hard {
            continue;
        }
        let instance = dimacs::max::read_from_file(file)?;
        let g: LinkedListGraph = instance.graph;
        let s = instance.src;
        let t = instance.snk;
        let upper = instance.upper;

        let (value, _, _) = edmondskarp(&g, s, t, |e| upper[g.edge_id(e)].to_i32().unwrap());
        assert_eq!(value, expected);
    }

    Ok(())
}

#[test]
fn test_dinic() -> Result<(), Box<dyn Error>> {
    for &(file, expected, _) in TESTS {
        let instance = dimacs::max::read_from_file(file)?;
        let g: LinkedListGraph = instance.graph;
        let s = instance.src;
        let t = instance.snk;
        let upper = instance.upper;

        let (value, _, _) = dinic(&g, s, t, |e| upper[g.edge_id(e)].to_i32().unwrap());
        assert_eq!(value, expected);
    }

    Ok(())
}

#[test]
fn test_pushrelabel() -> Result<(), Box<dyn Error>> {
    for &use_relabelling in &[true, false] {
        for &(file, expected, _) in TESTS {
            let instance = dimacs::max::read_from_file(file)?;
            let g: LinkedListGraph = instance.graph;
            let s = instance.src;
            let t = instance.snk;
            let upper = instance.upper;

            let mut pr = PushRelabel::new(&g);
            pr.use_global_relabelling = use_relabelling;
            pr.solve(s, t, |e| upper[g.edge_id(e)].to_i32().unwrap());
            assert_eq!(
                pr.value(),
                expected,
                "Instance: {} relabelling: {}",
                file,
                use_relabelling
            );
        }
    }

    Ok(())
}
