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

//! This module implements a read function for the famous DIMACS max
//! flow format. A DIMACS file must look as follows.
//!
//! 1. empty lines are allowed and ignored
//! 2. a line starting with `c` is a comment line and is ignored
//! 3. the first non-comment line must have the form `p max <n> <m>`,
//!    where `<n>` is an integer > 0 denoting the number of nodes and
//!    `<m>` an integer > 0 denoting the number of arcs.
//! 4. after the problem line there must follow exactly two node lines
//!    of the form `n <node> <type>` where `<node>` is the node number
//!    between `1..n` and `<type>` is either `s` (if this is the source
//!    node) or `t` (if this is the sink node).
//! 5. after the node lines there must be exactly `m` arc lines `a <u>
//!    <v> <c>` denoting the source and sink nodes of an arc as well as
//!    the arcs capacity `<c>` (an integer >= 0).
//!
//! Loops are not allowed. This module accepts parallel edges as long
//! as the used graph type supports them. In the "official" DIMACS
//! format parallel edges are forbidden.

use super::{DimacsReader, Error, Result};
use crate::builder::{Buildable, Builder};
use crate::traits::IndexDigraph;
use std::io::{Read, Write};

pub struct Instance<G, N> {
    /// The graph.
    pub graph: G,
    /// The source node.
    pub src: N,
    /// The sink node.
    pub snk: N,
    /// The upper bounds.
    pub upper: Vec<usize>,
}

pub fn read<R: Read, G, N>(r: R) -> Result<Instance<G, N>>
where
    G: for<'a> IndexDigraph<'a, Node = N> + Buildable,
{
    let mut reader = DimacsReader::new(r);

    // Read the problem line.
    let mut pline = reader.expect_line('p')?;
    pline.expect("max")?;
    let nnodes = pline.number()?;
    let nedges = pline.number()?;
    pline.end()?;

    let mut b = G::Builder::new();
    let mut upper = vec![0; nedges];
    let nodes = b.add_nodes(nnodes);
    let mut src = None;
    let mut snk = None;

    for _ in 0..2 {
        let mut nline = reader.expect_line('n')?;
        let u: usize = nline.number()?;
        if u < 1 || u > nnodes {
            return Err(Error::Data {
                line: nline.line,
                msg: format!("invalid node id {} (must be in 1..{})", u, nnodes),
            });
        }
        let what = nline.str()?;
        match what {
            "s" => {
                if src.is_some() {
                    return Err(Error::Format {
                        line: nline.line,
                        msg: "duplicate source node".to_string(),
                    });
                }
                src = Some(u);
            }
            "t" => {
                if snk.is_some() {
                    return Err(Error::Format {
                        line: nline.line,
                        msg: "duplicate sink node".to_string(),
                    });
                }
                snk = Some(u);
            }
            _ => {
                return Err(Error::Format {
                    line: nline.line,
                    msg: format!("invalid node type, must be 's' or 't', got: {}", what),
                });
            }
        }
    }

    for _ in 0..nedges {
        let mut aline = reader.expect_line('a')?;
        let u: usize = aline.number()?;
        let v: usize = aline.number()?;
        let c: usize = aline.number()?;

        if u < 1 || u > nnodes {
            return Err(Error::Data {
                line: aline.line,
                msg: format!("invalid source node id {} (must be in 1..{})", u, nnodes),
            });
        }

        if v < 1 || v > nnodes {
            return Err(Error::Data {
                line: aline.line,
                msg: format!("invalid sink node id {} (must be in 1..{})", u, nnodes),
            });
        }

        if u == v {
            return Err(Error::Data {
                line: aline.line,
                msg: format!("invalid loop ({},{}) in edge", u, u),
            });
        }

        let e = b.add_edge(nodes[u - 1], nodes[v - 1]);
        upper[b.edge2id(e)] = c;
    }

    if let Some(toks) = reader.read_line()? {
        return Err(Error::Format {
            line: toks.line,
            msg: format!(
                "unexpected line at the end of file (expected exactly {} 'a' lines)",
                nedges,
            ),
        });
    }

    let graph = b.into_graph();
    let src = graph.id2node(src.unwrap() - 1);
    let snk = graph.id2node(snk.unwrap() - 1);
    Ok(Instance { graph, src, snk, upper })
}

pub fn read_from_file<G, N>(filename: &str) -> Result<Instance<G, N>>
where
    G: for<'a> IndexDigraph<'a, Node = N> + Buildable,
{
    read(std::fs::File::open(filename)?)
}

/// Write a min-cost-flow instance.
pub fn write<'a, W, G>(mut w: W, instance: &'a Instance<G, G::Node>) -> std::io::Result<()>
where
    W: Write,
    G: IndexDigraph<'a>,
{
    let g = &instance.graph;
    writeln!(w, "p max {} {}", g.num_nodes(), g.num_edges())?;
    writeln!(w, "n {} s", g.node_id(instance.src) + 1)?;
    writeln!(w, "n {} t", g.node_id(instance.snk) + 1)?;
    for e in g.edges() {
        let eid = g.edge_id(e);
        writeln!(
            w,
            "a {} {} {}",
            g.node_id(g.src(e)) + 1,
            g.node_id(g.snk(e)) + 1,
            instance.upper[eid],
        )?;
    }

    Ok(())
}

/// Write a min-cost-flow instance to a named file.
pub fn write_to_file<'a, W, G>(filename: &str, instance: &'a Instance<G, G::Node>) -> std::io::Result<()>
where
    W: Write,
    G: IndexDigraph<'a>,
{
    write(&mut std::fs::File::create(filename)?, instance)
}

#[cfg(test)]
mod tests {

    use crate::dimacs;
    use crate::{traits::*, Buildable, Builder, VecGraph};
    use std::io::{self, Cursor};

    #[test]
    fn parse_file_test() {
        let file = "c this is a test file

p max 6 9
n 5 s
n 6 t

c there might be empty lines

a 5 1 10
a 5 2 10
a 1 2 2
a 1 3 4
a 1 4 8
a 2 4 9
a 3 6 10
a 4 3 6
a 4 6 10

c end of the file
";
        let instance = dimacs::max::read(io::Cursor::new(file)).unwrap();

        let g: VecGraph = instance.graph;
        let src = instance.src;
        let snk = instance.snk;
        let upper = instance.upper;

        assert_eq!(g.num_nodes(), 6);
        assert_eq!(g.num_edges(), 9);
        assert_eq!(g.node_id(src), 4);
        assert_eq!(g.node_id(snk), 5);

        let mut arcs: Vec<_> = g
            .edges()
            .map(|e| (g.node_id(g.src(e)) + 1, g.node_id(g.snk(e)) + 1, upper[g.edge_id(e)]))
            .collect();

        arcs.sort();

        assert_eq!(
            arcs,
            vec![
                (1, 2, 2),
                (1, 3, 4),
                (1, 4, 8),
                (2, 4, 9),
                (3, 6, 10),
                (4, 3, 6),
                (4, 6, 10),
                (5, 1, 10),
                (5, 2, 10),
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
        let upper = vec![4, 2, 2, 3, 5];

        let mut buf = Cursor::new(Vec::new());
        dimacs::max::write(
            &mut buf,
            &dimacs::max::Instance {
                graph: &g,
                src: g.id2node(0),
                snk: g.id2node(3),
                upper,
            },
        )
        .unwrap();

        assert_eq!(
            String::from_utf8(buf.into_inner()).unwrap(),
            "p max 4 5
n 1 s
n 4 t
a 1 2 4
a 1 3 2
a 2 3 2
a 2 4 3
a 3 4 5
"
        );
    }
}
