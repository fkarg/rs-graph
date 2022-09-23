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

use std::collections::HashMap;
use std::error::Error;
use std::fs::read_dir;
use std::path::Path;

use rs_graph::dimacs;
use rs_graph::mcf::{NetworkSimplex, SolutionState};
use rs_graph::{IndexGraph, Net};

#[test]
fn test_network_simplex() -> Result<(), Box<dyn Error>> {
    let mut values = HashMap::new();

    for entry in read_dir(Path::new("tests/mcf"))? {
        let entry = entry?;
        if entry.path().extension().map(|ext| ext == "sol").unwrap_or(false) {
            let (value, _) = dimacs::min::read_solution_from_file::<isize>(&entry.path().to_string_lossy())?;
            if let Some(file_stem) = entry.path().file_stem().map(|s| s.to_string_lossy().to_string()) {
                values.insert(file_stem, value);
            }
        }
    }

    for entry in read_dir(Path::new("tests/mcf"))? {
        let entry = entry?;
        if entry.path().extension().map(|ext| ext == "min").unwrap_or(false) {
            let instance = dimacs::min::read_from_file(&entry.path().to_string_lossy())?;
            let g: Net = instance.graph;

            let balances = instance.balances;
            let lower = instance.lower;
            let upper = instance.upper;
            let costs = instance.costs;

            let mut spx = NetworkSimplex::new(&g);
            spx.set_balances(|u| balances[g.node_id(u)]);
            spx.set_lowers(|e| lower[g.edge_id(e)]);
            spx.set_uppers(|e| upper[g.edge_id(e)]);
            spx.set_costs(|e| costs[g.edge_id(e)]);

            let state = spx.solve();
            assert_eq!(state, SolutionState::Optimal);
            if let Some(value) = entry
                .path()
                .file_name()
                .and_then(|s| values.get(s.to_string_lossy().as_ref()))
            {
                assert_eq!(*value, spx.value());
            } else {
                panic!("Can't find solution file for {:?}", entry.path());
            }
        }
    }

    Ok(())
}
