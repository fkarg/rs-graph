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

//! This module implements a read function for the DIMACS min cost
//! flow format. A DIMACS file must look as follows.
//!
//! 1. empty lines are allowed and ignored
//! 2. a line starting with `c` is a comment line and is ignored
//! 3. the first non-comment line must have the form `p min <n> <m>`,
//!    where `<n>` is an integer > 0 denoting the number of nodes and
//!    `<m>` an integer > 0 denoting the number of arcs.
//! 4. after the problem line there must follow node lines of the form
//!    `n <node> <balance>` where `<node>` is the node number between
//!    `1..n` and `<balance>` is node's supply (if positive) or demand
//!    (if negative). Nodes that have balance 0 do not need to be
//!    specified.
//! 5. after the node lines there must be exactly `m` arc lines `a <u>
//!    <v> <lb> <ub> <c>` denoting the source and sink nodes of an arc
//!    as well as the arcs lower bound `<lb>`, upper bound `<ub>` and
//!    cost `<c>`.
//!
//! Loops are not allowed. This module accepts parallel arcs as long
//! as the used graph type supports them. In the "official" DIMACS
//! format parallel arcs are forbidden.

use super::{DimacsReader, Error, Result};
use crate::builder::{Buildable, Builder};
use crate::traits::IndexDigraph;
use num_traits::Zero;
use std::fmt::Display;
use std::io::{Read, Write};
use std::str::FromStr;

pub struct Instance<G, T> {
    /// The graph.
    pub graph: G,
    /// The node balance.
    pub balances: Vec<T>,
    /// The lower bounds.
    pub lower: Vec<T>,
    /// The upper bounds.
    pub upper: Vec<T>,
    /// The arc costs.
    pub costs: Vec<T>,
}

pub fn read<R: Read, G, T>(r: R) -> Result<Instance<G, T>>
where
    G: for<'a> IndexDigraph<'a> + Buildable,
    T: FromStr + Zero + Clone,
    T::Err: Display,
{
    let mut reader = DimacsReader::new(r);

    // Read the problem line.
    let mut pline = reader.expect_line('p')?;
    pline.expect("min")?;
    let nnodes = pline.number()?;
    let nedges = pline.number()?;
    pline.end()?;

    let mut b = G::Builder::new();
    let mut balances = vec![T::zero(); nnodes];
    let mut costs = Vec::with_capacity(nedges);
    let mut lower = Vec::with_capacity(nedges);
    let mut upper = Vec::with_capacity(nedges);

    let nodes = b.add_nodes(nnodes);

    while let Some((d, mut toks)) = reader.read_one_line_of(&["n", "a"])? {
        if d == "n" {
            let u: usize = toks.number()?;
            if u < 1 || u > nnodes {
                return Err(Error::Data {
                    line: toks.line,
                    msg: format!("invalid node id {} (must be in 1..{})", u, nnodes),
                });
            }
            balances[u - 1] = toks.number()?;
        } else {
            let u: usize = toks.number()?;
            let v: usize = toks.number()?;
            let lb: T = toks.number()?;
            let ub: T = toks.number()?;
            let c: T = toks.number()?;

            if u < 1 || u > nnodes {
                return Err(Error::Data {
                    line: toks.line,
                    msg: format!("invalid source node id {} (must be in 1..{})", u, nnodes),
                });
            }

            if v < 1 || v > nnodes {
                return Err(Error::Data {
                    line: toks.line,
                    msg: format!("invalid sink node id {} (must be in 1..{})", u, nnodes),
                });
            }

            if u == v {
                return Err(Error::Data {
                    line: toks.line,
                    msg: format!("invalid loop ({},{}) in edge", u, u),
                });
            }

            if upper.len() == nedges {
                return Err(Error::Data {
                    line: toks.line,
                    msg: format!("unexpected 'a' line (expected exactly {} arcs)", nedges),
                });
            }

            b.add_edge(nodes[u - 1], nodes[v - 1]);
            lower.push(lb);
            upper.push(ub);
            costs.push(c);
        }

        toks.end()?;
    }

    Ok(Instance {
        graph: b.into_graph(),
        balances,
        lower,
        upper,
        costs,
    })
}

pub fn read_from_file<G, T>(filename: &str) -> Result<Instance<G, T>>
where
    G: for<'a> IndexDigraph<'a> + Buildable,
    T: FromStr + Zero + Clone,
    T::Err: Display,
{
    read(std::fs::File::open(filename)?)
}

/// Write a min-cost-flow instance.
pub fn write<'a, W, G, T>(mut w: W, instance: &'a Instance<G, T>) -> std::io::Result<()>
where
    W: Write,
    G: IndexDigraph<'a>,
    T: Zero + Display + Clone,
{
    let g = &instance.graph;
    writeln!(w, "p min {} {}", g.num_nodes(), g.num_edges())?;
    for u in g.nodes() {
        let b = instance.balances[g.node_id(u)].clone();
        if !b.is_zero() {
            writeln!(w, "n {} {}", g.node_id(u) + 1, b)?;
        }
    }
    for e in g.edges() {
        let eid = g.edge_id(e);
        writeln!(
            w,
            "a {} {} {} {} {}",
            g.node_id(g.src(e)) + 1,
            g.node_id(g.snk(e)) + 1,
            instance.lower[eid],
            instance.upper[eid],
            instance.costs[eid]
        )?;
    }

    Ok(())
}

/// Write a min-cost-flow instance to a named file.
pub fn write_to_file<'a, G, T>(filename: &str, instance: &'a Instance<G, T>) -> std::io::Result<()>
where
    G: IndexDigraph<'a>,
    T: Zero + Display + Clone,
{
    write(&mut std::fs::File::create(filename)?, instance)
}

/// Write a solution of a min-cost-flow problem.
pub fn write_solution<'a, W, G, T, Fs>(mut w: W, g: &'a G, flow: Fs, value: T) -> std::io::Result<()>
where
    W: Write,
    G: IndexDigraph<'a>,
    T: Display + Zero,
    Fs: Fn(G::Edge) -> T,
{
    writeln!(w, "s {}", value)?;
    for e in g.edges() {
        let fl = (flow)(e);
        if !fl.is_zero() {
            writeln!(w, "f {} {} {}", g.node_id(g.src(e)) + 1, g.node_id(g.snk(e)) + 1, fl)?;
        }
    }

    Ok(())
}

/// Write a solution of a min-cost-flow problem to a named file.
pub fn write_solution_to_file<'a, G, T, Fs>(filename: &str, g: &'a G, flow: Fs, value: T) -> std::io::Result<()>
where
    G: IndexDigraph<'a>,
    T: Display + Zero,
    Fs: Fn(G::Edge) -> T,
{
    write_solution(&mut std::fs::File::create(filename)?, g, flow, value)
}

/// Read a solution of a min-cost-flow problem.
pub fn read_solution<'a, R, T>(r: R) -> Result<(T, Vec<(usize, usize, T)>)>
where
    R: Read,
    T: FromStr,
    T::Err: Display,
{
    let mut reader = DimacsReader::new(r);
    let mut flows = vec![];
    let mut sol = None;

    // Read the solution value line.
    while let Some((d, mut toks)) = reader.read_one_line_of(&["f", "s"])? {
        if d == "f" {
            flows.push((toks.number::<usize>()? - 1, toks.number::<usize>()? - 1, toks.number()?));
        } else {
            if sol.is_some() {
                return Err(Error::Format {
                    line: toks.line,
                    msg: "The solution value must be specified exactly once".to_string(),
                });
            }
            sol = Some(toks.number()?);
        }
        toks.end()?;
    }

    Ok((
        sol.ok_or_else(|| Error::Format {
            line: 0,
            msg: "Missing solution value".to_string(),
        })?,
        flows,
    ))
}

/// Read a solution of a min-cost-flow problem from a named file.
pub fn read_solution_from_file<T>(filename: &str) -> Result<(T, Vec<(usize, usize, T)>)>
where
    T: FromStr,
    T::Err: Display,
{
    read_solution(std::fs::File::open(filename)?)
}

#[cfg(test)]
mod tests {

    use crate::dimacs;
    use crate::{traits::*, Buildable, Builder, VecGraph};
    use std::io::{self, Cursor};

    #[test]
    fn parse_file_test() {
        let file = "c this is a test file

p min 8 11
n 1 10
n 2 20
n 4 -5
n 7 -15
n 8 -10

c there might be empty lines

a 1 4 0 15 2
a 2 1 0 10 1
a 2 3 0 10 0
a 2 6 0 10 6
a 3 4 0 5 1
a 3 5 0 10 4
a 4 7 0 10 5
a 5 6 0 20 2
a 5 7 0 15 7
a 6 8 0 10 8
a 7 8 0 15 9

c end of the file
";
        let instance = dimacs::min::read::<_, _, isize>(io::Cursor::new(file)).unwrap();

        let g: VecGraph = instance.graph;
        let balances = instance.balances;
        let lower = instance.lower;
        let upper = instance.upper;
        let costs = instance.costs;

        assert_eq!(g.num_nodes(), 8);
        assert_eq!(g.num_edges(), 11);

        assert_eq!(balances, vec![10, 20, 0, -5, 0, 0, -15, -10]);
        assert_eq!(lower, vec![0; g.num_edges()]);
        assert_eq!(upper, vec![15, 10, 10, 10, 5, 10, 10, 20, 15, 10, 15]);
        assert_eq!(costs, vec![2, 1, 0, 6, 1, 4, 5, 2, 7, 8, 9]);

        let edges = (0..g.num_edges())
            .map(|i| g.id2edge(i))
            .map(|e| (g.node_id(g.src(e)) + 1, g.node_id(g.snk(e)) + 1))
            .collect::<Vec<_>>();

        assert_eq!(
            edges,
            vec![
                (1, 4),
                (2, 1),
                (2, 3),
                (2, 6),
                (3, 4),
                (3, 5),
                (4, 7),
                (5, 6),
                (5, 7),
                (6, 8),
                (7, 8),
            ]
        );
    }

    #[test]
    fn write_test_file() {
        let g = VecGraph::<u32>::new_with(|b| {
            let nodes = b.add_nodes(4);
            b.add_edge(nodes[0], nodes[1]);
            b.add_edge(nodes[0], nodes[2]);
            b.add_edge(nodes[1], nodes[2]);
            b.add_edge(nodes[1], nodes[3]);
            b.add_edge(nodes[2], nodes[3]);
        });
        let balances = vec![4, 0, 0, -4];
        let lower = vec![0; g.num_edges()];
        let upper = vec![4, 2, 2, 3, 5];
        let costs = vec![2, 2, 1, 3, 1];

        let mut buf = Cursor::new(Vec::new());
        dimacs::min::write(
            &mut buf,
            &dimacs::min::Instance {
                graph: &g,
                balances,
                lower,
                upper,
                costs,
            },
        )
        .unwrap();

        assert_eq!(
            String::from_utf8(buf.into_inner()).unwrap(),
            "p min 4 5
n 1 4
n 4 -4
a 1 2 0 4 2
a 1 3 0 2 2
a 2 3 0 2 1
a 2 4 0 3 3
a 3 4 0 5 1
"
        );
    }

    #[test]
    fn write_solution_file() -> std::result::Result<(), Box<dyn std::error::Error>> {
        let g = VecGraph::<u32>::new_with(|b| {
            let nodes = b.add_nodes(4);
            b.add_edge(nodes[0], nodes[1]);
            b.add_edge(nodes[0], nodes[2]);
            b.add_edge(nodes[1], nodes[2]);
            b.add_edge(nodes[1], nodes[3]);
            b.add_edge(nodes[2], nodes[3]);
        });
        let flow = vec![2, 2, 2, 0, 4];

        let mut buf = Cursor::new(Vec::new());
        dimacs::min::write_solution(&mut buf, &g, |e| flow[g.edge_id(e)], 14)?;

        let soltxt = String::from_utf8(buf.into_inner())?;
        assert_eq!(
            soltxt,
            "s 14
f 1 2 2
f 1 3 2
f 2 3 2
f 3 4 4
"
        );

        let (value, flows) = dimacs::min::read_solution(Cursor::new(soltxt))?;
        assert_eq!(value, 14);
        assert_eq!(flows, vec![(0, 1, 2), (0, 2, 2), (1, 2, 2), (2, 3, 4)]);

        Ok(())
    }
}
