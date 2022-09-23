/*
 * Copyright (c) 2017-2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

use super::Instance;

use crate::{Buildable, Builder, IndexGraph};

use std::error;
use std::fmt;
use std::fs;
use std::io;

use super::EdgeAttr;
use std::collections::HashMap;

use peg;

/// Error raised by the parser.
pub type ParseError = peg::error::ParseError<peg::str::LineCol>;

//include!(concat!(env!("OUT_DIR"), "/parser.rs"));
peg::parser! {

    grammar steinlib_parser() for str {
      pub(super) rule doc() -> Vec<Section>
        = ws()* i("33D32945") ws()+ i("STP") ws()+ i("File,") ws()+ i("STP") ws()+ i("Format") ws()+ i("Version") ws()+ i("1.") "0"+ nl()+
          secs:(
             comment_section() /
              graph_section() /
              terminals_section() /
              coordinates_section() /
              drawing_section()
              ) ** (nl()*)
           nl()*
           i("EOF") nl()* ![_]
           { secs }

      pub(super) rule comment_section() -> Section
        = i("SECTION") ws()+ i("Comment") nl()+ h:comment_entry() ** (nl()*) nl()* i("END") nl()
           {
             Section::Comment(h.into_iter().collect())
           }

      rule comment_entry() -> (String, String)
        = ws()* key:$(['a'..='z' | 'A' ..= 'Z']+) ws()+ val:(quoted() / word()) nl()
          {
             (key.to_string(), val)
          }

      pub(super) rule graph_section() -> Section
        = i("SECTION") ws()+ i("Graph") nl()+
            g:(edge_line() / arc_line() / node_count() / edge_count() / arc_count()) ** (nl()*) nl()*
          i("END") nl() { Section::Graph(g) }

      rule edge_line() -> GraphLine
        = i("E") ws()+ u:int() ws()+ v:int() ws()+ w:float() nl() { GraphLine::Edge(u, v, w) }

      rule arc_line() -> GraphLine
        = i("A") ws()+ u:int() ws()+ v:int() ws()+ w:float() nl() { GraphLine::Arc(u, v, w) }

      rule node_count() -> GraphLine
        = i("Nodes") ws()+ n:int() nl() { GraphLine::NumNodes(n) }

      rule edge_count() -> GraphLine
        = i("Edges") ws()+ n:int() nl() { GraphLine::NumEdges(n) }

      rule arc_count() -> GraphLine
        = i("Arcs") ws()+ n:int() nl() { GraphLine::NumArcs(n) }


      pub(super) rule terminals_section() -> Section
        = i("SECTION") ws()+ i("Terminals")
          nl()+
          i("Terminals") ws()+ n:int()
           nl()+
          t:terminal() ** (nl()*)
           nl()*
           i("END") nl()
           { Section::Terminals(n, t) }

      rule terminal() -> usize
        = i("T") ws()* n:int() nl() { n }


      pub(super) rule coordinates_section() -> Section
        = i("SECTION") ws()+ i("Coordinates") nl()
          coords:coordinate() ** (nl()*)
           nl()*
           i("END") nl()
           { Section::Coordinates(coords) }

      rule coordinate() -> (usize,Vec<f64>)
        = ws()* beg:position!() i("D")+ end:position!() ws()+ u:int() ws()+ nums:float() **<{end-beg}> (ws()+) nl() { (u,nums) }


      pub(super) rule drawing_section() -> Section
        = i("SECTION") ws()+ i("Drawing") nl()
          d:arc_drawing() ** (nl()*)
           nl()*
           i("END") nl()
           { Section::Drawing(d) }

      rule arc_drawing() -> (usize, usize, Vec<EdgeAttr>)
        = ['a' | 'A' | 'e' | 'E'] ws()+ u:int() ws()+ v:int() ws()+ attrs:arc_attrs() ** (ws()+) nl()
          { (u, v, attrs) }

      rule arc_attrs() -> EdgeAttr
        = a:$(i("bl") / i("br"))
          {
             match a {
                "bl" | "bL" | "Bl" | "BL" => EdgeAttr::BendLeft,
                _ => EdgeAttr::BendRight
            }
          }

      rule int() -> usize
        = n:$(['-' | '+']? digit()+) { n.parse().unwrap() }

      rule float() -> f64
        = n:$(['-' | '+']? (digit()+ "."? digit()* / "." digit()+) (['e' | 'E'] ['-' | '+']? digit()+)?) { n.parse().unwrap() }

      rule digit()
        = ['0' ..= '9']

      rule quoted() -> String
        = "\"" s:$(( "\\" [_] / !['\\' | '"'] [_] )*) "\"" { s.to_string() }

      rule word() -> String
        = s:$((![' ' | '\t' | '\r' | '\n'] [_])+) { s.to_string() }

      rule nl()
        = quiet!{ws()* ("#" (!['\n'] [_])*)? "\n" ws()*}

      rule ws()
        = quiet!{[' ' | '\t' | '\r']}

      rule i(literal: &'static str)
        = input:$([_]*<{literal.len()}>)
          {? if input.eq_ignore_ascii_case(literal) { Ok(()) } else { Err(literal) } }
    }
}

#[derive(Debug)]
pub enum SteinlibError {
    Io(io::Error),
    Parse(ParseError),
    NoMixed,
    UnmatchedDimension { dim: usize },
    UnmatchedTerminalCount { got: usize, expected: usize },
    InvalidLoop { node: usize },
    Format { msg: String },
}

impl From<io::Error> for SteinlibError {
    fn from(err: io::Error) -> Self {
        SteinlibError::Io(err)
    }
}

impl From<ParseError> for SteinlibError {
    fn from(err: ParseError) -> Self {
        SteinlibError::Parse(err)
    }
}

impl fmt::Display for SteinlibError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::SteinlibError::*;
        match self {
            Io(err) => err.fmt(fmt),
            Parse(err) => err.fmt(fmt),
            NoMixed => write!(fmt, "Mixed graphs are not supported"),
            UnmatchedDimension { dim } => write!(
                fmt,
                "Dimension of coordinates for node {} differs from previous dimension",
                dim
            ),
            UnmatchedTerminalCount { got, expected } => write!(
                fmt,
                "Unexpected number of terminals (expected: {}, got: {})",
                expected, got
            ),
            InvalidLoop { node } => write!(fmt, "Loops are not allowed (got ({},{}))", node, node),
            Format { msg } => write!(fmt, "Format error: {}", msg),
        }
    }
}

impl error::Error for SteinlibError {
    fn cause(&self) -> Option<&dyn error::Error> {
        match self {
            SteinlibError::Io(err) => Some(err),
            SteinlibError::Parse(err) => Some(err),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum GraphLine {
    Edge(usize, usize, f64),
    Arc(usize, usize, f64),
    NumNodes(usize),
    NumEdges(usize),
    NumArcs(usize),
}

#[derive(Debug, PartialEq)]
pub enum Section {
    Comment(HashMap<String, String>),
    Graph(Vec<GraphLine>),
    Coordinates(Vec<(usize, Vec<f64>)>),
    Terminals(usize, Vec<usize>),
    Drawing(Vec<(usize, usize, Vec<EdgeAttr>)>),
}

pub fn read<G>(fname: &str) -> Result<Instance<G>, SteinlibError>
where
    G: for<'a> IndexGraph<'a> + Buildable,
{
    let mut f = fs::File::open(fname)?;
    read_from_buf(&mut f)
}

/// Read `SteinLib` file from a buffered reader.
///
/// - `buf` the buffer with the file content
pub fn read_from_buf<G, R>(buf: &mut R) -> Result<Instance<G>, SteinlibError>
where
    R: io::Read,
    G: for<'a> IndexGraph<'a> + Buildable,
{
    let data = {
        let mut s = String::new();
        buf.read_to_string(&mut s)?;
        steinlib_parser::doc(&s)?
    };

    let mut b = G::Builder::new();

    let mut nodes = vec![];
    let mut nodecoords = vec![];
    let mut nedges = 0;
    let mut narcs = 0;
    let mut weights = vec![];
    let mut edgeattrs = vec![];
    let mut edges = HashMap::new();

    for sec in data {
        match sec {
            Section::Comment(_) => (),
            Section::Terminals(n, terms) => {
                if n != terms.len() {
                    return Err(SteinlibError::UnmatchedTerminalCount {
                        got: terms.len(),
                        expected: n,
                    });
                }
            }
            Section::Graph(graph_lines) => {
                let mut cntarcs = 0;
                let mut cntedges = 0;
                for line in graph_lines {
                    match line {
                        GraphLine::NumNodes(n) => {
                            if !nodes.is_empty() {
                                return Err(SteinlibError::Format {
                                    msg: "Duplicate 'Nodes' keyword".to_string(),
                                });
                            }
                            nodes.extend_from_slice(&b.add_nodes(n));
                            nodecoords.resize(nodes.len(), vec![]);
                        }
                        GraphLine::NumEdges(m) => {
                            if nedges > 0 {
                                return Err(SteinlibError::Format {
                                    msg: "Duplicate 'Edges' keyword".to_string(),
                                });
                            } else if narcs > 0 {
                                return Err(SteinlibError::NoMixed);
                            }
                            nedges = m;
                            b.reserve(0, m);
                        }
                        GraphLine::NumArcs(m) => {
                            if narcs > 0 {
                                return Err(SteinlibError::Format {
                                    msg: "Duplicate 'Arcs' keyword".to_string(),
                                });
                            } else if nedges > 0 {
                                return Err(SteinlibError::NoMixed);
                            }
                            narcs = m;
                            b.reserve(0, m);
                        }
                        GraphLine::Edge(u, v, w) => {
                            if nedges == 0 {
                                return Err(SteinlibError::Format {
                                    msg: "Midding 'Edges' line before first edge".to_string(),
                                });
                            } else if nedges <= cntedges {
                                return Err(SteinlibError::Format {
                                    msg: format!("Too many edges (expected: {})", nedges),
                                });
                            } else if u == v {
                                return Err(SteinlibError::InvalidLoop { node: u });
                            } else if u < 1 || u > nodes.len() {
                                return Err(SteinlibError::Format {
                                    msg: format!("Invalid node in edge: {} (must be in 1..{})", u, nodes.len()),
                                });
                            } else if v < 1 || v > nodes.len() {
                                return Err(SteinlibError::Format {
                                    msg: format!("Invalid node in edge: {} (must be in 1..{})", v, nodes.len()),
                                });
                            }
                            b.add_edge(nodes[u - 1], nodes[v - 1]);
                            weights.push(w);
                            edges.insert((u, v), cntedges);
                            cntedges += 1;
                        }
                        GraphLine::Arc(u, v, w) => {
                            if narcs == 0 {
                                return Err(SteinlibError::Format {
                                    msg: "Midding 'Arcs' line before first arc".to_string(),
                                });
                            } else if narcs <= cntarcs {
                                return Err(SteinlibError::Format {
                                    msg: format!("Too many arcs (expected: {})", narcs),
                                });
                            } else if u == v {
                                return Err(SteinlibError::InvalidLoop { node: u });
                            } else if u < 1 || u > nodes.len() {
                                return Err(SteinlibError::Format {
                                    msg: format!("Invalid node in arc: {} (must be in 1..{})", u, narcs),
                                });
                            } else if v < 1 || v > nodes.len() {
                                return Err(SteinlibError::Format {
                                    msg: format!("Invalid node in arc: {} (must be in 1..{})", v, narcs),
                                });
                            }
                            b.add_edge(nodes[u - 1], nodes[v - 1]);
                            weights.push(w);
                            edges.insert((u, v), cntedges);
                            cntarcs += 1;
                        }
                    }
                }

                if nedges != cntedges {
                    return Err(SteinlibError::Format {
                        msg: format!("Wrong number of edges (found: {}, expected: {})", cntedges, nedges),
                    });
                }
                if narcs != cntarcs {
                    return Err(SteinlibError::Format {
                        msg: format!("Wrong number of arcs (found: {}, expected: {})", cntarcs, narcs),
                    });
                }
            }
            Section::Coordinates(coords) => {
                let mut dim = 0;
                for (u, coord) in coords {
                    if u < 1 || u > nodes.len() {
                        return Err(SteinlibError::Format {
                            msg: format!("Invalid node in coordinate: {} (must be in 1..{})", u, narcs),
                        });
                    }
                    if dim > 0 && coord.len() != dim {
                        return Err(SteinlibError::UnmatchedDimension { dim: u });
                    }
                    dim = coord.len();
                    nodecoords[u - 1] = coord;
                }
            }
            Section::Drawing(drawings) => {
                edgeattrs.resize(nedges, vec![]);
                for (u, v, attrs) in drawings {
                    if let Some(&e) = edges.get(&(u, v)) {
                        edgeattrs[e] = attrs;
                    } else {
                        return Err(SteinlibError::Format {
                            msg: format!("Unknown edge in drawing: ({},{})", u, v),
                        });
                    }
                }
            }
        };
    }

    Ok(Instance {
        graph: b.into_graph(),
        weights,
        coordinates: nodecoords,
        edgeattrs,
    })
}

#[cfg(test)]
mod tests {

    use super::steinlib_parser::doc as steinlib;
    use super::steinlib_parser::{
        comment_section, coordinates_section, drawing_section, graph_section, terminals_section,
    };
    use super::{read_from_buf, GraphLine, Section};
    use crate::steinlib::EdgeAttr;
    use crate::traits::{FiniteDigraph, FiniteGraph, IndexGraph};
    use crate::LinkedListGraph;

    #[test]
    fn test_graph_section() {
        let r = graph_section("SECTION Graph\n  NODES 5\n  ARCS 2\n   E 1 2 3 # Kante bla\n  A 4 5 6\nEND\n");
        assert_eq!(
            r,
            Ok(Section::Graph(vec![
                GraphLine::NumNodes(5),
                GraphLine::NumArcs(2),
                GraphLine::Edge(1, 2, 3.0),
                GraphLine::Arc(4, 5, 6.0),
            ]))
        );
    }

    #[test]
    fn test_coordinates_section() {
        let r = coordinates_section("SECTION coordinates\n  D 1 5\n  DD 2 2 3\n \n  DDD 3 1  2 3 # Kante bla\nEND\n");
        assert_eq!(
            r,
            Ok(Section::Coordinates(vec![
                (1, vec![5.0]),
                (2, vec![2.0, 3.0]),
                (3, vec![1.0, 2.0, 3.0]),
            ]))
        );
    }

    #[test]
    fn test_comment_section() {
        let r = comment_section("SECTION comment\n  Name \"blaa\" \n\n Creator   \"Me the king\"\nEND\n");
        assert_eq!(
            r,
            Ok(Section::Comment(
                [
                    ("Name".to_string(), "blaa".to_string()),
                    ("Creator".to_string(), "Me the king".to_string())
                ]
                .iter()
                .cloned()
                .collect()
            ))
        );
    }

    #[test]
    fn test_terminals_section() {
        let r = terminals_section("SECTION Terminals\n  TERMINALS  2 \n\n  T 1 \n T 2 \nEND\n");
        assert_eq!(r, Ok(Section::Terminals(2, vec![1, 2])));
    }

    #[test]
    fn test_drawing_section() {
        let r = drawing_section("SECTION Drawing\n  E 1 2 bl \n E 3 4 br \nEND\n");
        assert_eq!(
            r,
            Ok(Section::Drawing(vec![
                (1, 2, vec![EdgeAttr::BendLeft]),
                (3, 4, vec![EdgeAttr::BendRight]),
            ]))
        )
    }

    #[test]
    fn test_parser() {
        let file = "33D32945 STP File, STP Format Version 1.0
   SECTION Comment
   Name    \"Odd Wheel\"
   Creator \"T. Koch, A. Martin and S. Voss\"
   Remark  \"Example used to describe the STP data format\"
   END
   SECTION Graph
   Nodes 7
   Edges 9
   E 1 2 1
   E 1 4 1
   E 1 6 1
   E 2 3 1
   E 3 4 1
   E 4 5 1
   E 5 6 1
   E 6 7 1
   E 7 2 1
   END


   SECTION Terminals
   Terminals 4
   T 1
   T 3
   T 5
   T 7
   END

   SECTION Coordinates
   DD 1  80 50
   DD 2  30 50
   DD 3  55  5
   DD 4 105  5
   DD 5 130 50
   DD 6 105 95
   DD 7  55 95
   END

   SECTION Drawing
   E 1 2 bl
   E 6 7 BR
   END

   EOF";

        let r = steinlib(file);
        assert_eq!(
            r,
            Ok(vec![
                Section::Comment(
                    [
                        ("Name".to_string(), "Odd Wheel".to_string()),
                        ("Creator".to_string(), "T. Koch, A. Martin and S. Voss".to_string()),
                        (
                            "Remark".to_string(),
                            "Example used to describe the STP data format".to_string(),
                        ),
                    ]
                    .iter()
                    .cloned()
                    .collect(),
                ),
                Section::Graph(vec![
                    GraphLine::NumNodes(7),
                    GraphLine::NumEdges(9),
                    GraphLine::Edge(1, 2, 1.0),
                    GraphLine::Edge(1, 4, 1.0),
                    GraphLine::Edge(1, 6, 1.0),
                    GraphLine::Edge(2, 3, 1.0),
                    GraphLine::Edge(3, 4, 1.0),
                    GraphLine::Edge(4, 5, 1.0),
                    GraphLine::Edge(5, 6, 1.0),
                    GraphLine::Edge(6, 7, 1.0),
                    GraphLine::Edge(7, 2, 1.0),
                ]),
                Section::Terminals(4, vec![1, 3, 5, 7]),
                Section::Coordinates(vec![
                    (1, vec![80.0, 50.0]),
                    (2, vec![30.0, 50.0]),
                    (3, vec![55.0, 5.0]),
                    (4, vec![105.0, 5.0]),
                    (5, vec![130.0, 50.0]),
                    (6, vec![105.0, 95.0]),
                    (7, vec![55.0, 95.0]),
                ]),
                Section::Drawing(vec![
                    (1, 2, vec![EdgeAttr::BendLeft]),
                    (6, 7, vec![EdgeAttr::BendRight]),
                ]),
            ])
        )
    }

    #[test]
    fn test_read() {
        let mut file: &[u8] = &b"33D32945 STP File, STP Format Version 1.0
   SECTION Comment
   Name    \"Odd Wheel\"
   Creator \"T. Koch, A. Martin and S. Voss\"
   Remark  \"Example used to describe the STP data format\"
   END
   SECTION Graph
   Nodes 7
   Edges 9
   E 1 2 1
   E 1 4 2
   E 1 6 3
   E 2 3 4
   E 3 4 5
   E 4 5 6
   E 5 6 7
   E 6 7 8
   E 7 2 9
   END


   SECTION Terminals
   Terminals 4
   T 1
   T 3
   T 5
   T 7
   END

   SECTION Coordinates
   DD 1  80 50
   DD 2  30 50
   DD 3  55  5
   DD 4 105  5
   DD 5 130 50
   DD 6 105 95
   DD 7  55 95
   END

   SECTION Drawing
   E 1 2 bl
   E 6 7 BR
   END

   EOF"[..];

        let instance = read_from_buf::<LinkedListGraph, _>(&mut file).unwrap();
        let g = instance.graph;
        let weights = instance.weights;
        let coords = instance.coordinates;
        let edgeattrs = instance.edgeattrs;

        assert_eq!(g.num_nodes(), 7);
        assert_eq!(g.num_edges(), 9);

        let edges: Vec<_> = g
            .edges()
            .map(|e| (g.node_id(g.src(e)) + 1, g.node_id(g.snk(e)) + 1, weights[g.edge_id(e)]))
            .collect();
        assert_eq!(
            edges,
            vec![
                (1, 2, 1.0),
                (1, 4, 2.0),
                (1, 6, 3.0),
                (2, 3, 4.0),
                (3, 4, 5.0),
                (4, 5, 6.0),
                (5, 6, 7.0),
                (6, 7, 8.0),
                (7, 2, 9.0),
            ]
        );

        assert_eq!(
            coords,
            vec![
                vec![80.0, 50.0],
                vec![30.0, 50.0],
                vec![55.0, 5.0],
                vec![105.0, 5.0],
                vec![130.0, 50.0],
                vec![105.0, 95.0],
                vec![55.0, 95.0],
            ]
        );

        let edgeattrs: Vec<_> = g
            .edges()
            .map(|e| {
                (
                    g.node_id(g.src(e)) + 1,
                    g.node_id(g.snk(e)) + 1,
                    edgeattrs[g.edge_id(e)].clone(),
                )
            })
            .filter(|&(_, _, ref attrs)| !attrs.is_empty())
            .collect();

        assert_eq!(
            edgeattrs,
            vec![(1, 2, vec![EdgeAttr::BendLeft]), (6, 7, vec![EdgeAttr::BendRight])]
        )
    }
}
