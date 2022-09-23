// Copyright (c) 2016-2022 Frank Fischer <frank-fischer@shadow-soft.de>
//
// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see  <http://www.gnu.org/licenses/>
//

use super::{read_dimacs, Error as DimacsError};

use crate::{Buildable, Builder};

use std::cmp::{max, min};
use std::collections::HashSet;
use std::f64;
use std::fs;
use std::io::{BufRead, BufReader};

// Possible metrics
#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Metric {
    // infinity norm,
    LINF,
    // l_p norm
    L(f64),
    // squared euclidean norm
    L2S,
}

// Problem parameters
#[derive(PartialEq, Debug)]
pub enum Param {
    // edge included only if length greater than or equal to this
    MinLength(f64),
    // edge included only if length less than or equal to this
    MaxLength(f64),
}

/// Read DIMACS file.
///
/// - `fname` is the name of the file to be read
/// - `weights` is the array of node weights
pub fn read<G>(fname: &str) -> Result<(G, Vec<f64>), DimacsError>
where
    G: Buildable,
{
    read_from_buf(&mut BufReader::new(fs::File::open(fname)?))
}

/// Read DIMACS file from a buffered reader.
///
/// - `buf` the buffer with the file content
pub fn read_from_buf<R, G>(buf: &mut R) -> Result<(G, Vec<f64>), DimacsError>
where
    R: BufRead,
    G: Buildable,
{
    let mut g = G::new_builder();
    let mut weights = vec![];
    let mut nnodes = 0;
    let mut nedges = 0;
    let mut gnodes = vec![];
    let mut nodes = HashSet::new();
    let mut edges = HashSet::new();
    let mut dim = 0;
    let mut metric = None;
    let mut vertices = vec![];
    let mut minlength = None;
    let mut maxlength = None;

    let mut start = true;
    read_dimacs(buf, &mut |d, toks| {
        if start {
            if d != 'p' {
                return Err(DimacsError::Format {
                    line: toks.line,
                    msg: format!("expected problem line starting with 'p', got: {}", d),
                });
            }
            let edge = toks.next().unwrap_or("end of line");
            if edge != "edge" {
                return Err(DimacsError::Format {
                    line: toks.line,
                    msg: format!("expected 'edge' in p line, got: {}", edge),
                });
            }
            nnodes = toks.number()?;
            nedges = toks.number()?;
            toks.end()?;

            g.reserve(nnodes, nedges);
            gnodes = g.add_nodes(nnodes);
            weights.clear();
            weights.resize(nnodes, 0.0);

            start = false;
        } else {
            match d {
                'n' => {
                    let id: usize = toks.number()?;
                    let val = toks.number()?;
                    toks.end()?;
                    if id < 1 || id > nnodes {
                        return Err(DimacsError::Format {
                            line: toks.line,
                            msg: format!("invalid node id {} (must be <= {})", id, nnodes),
                        });
                    }
                    if !nodes.insert(id) {
                        return Err(DimacsError::Format {
                            line: toks.line,
                            msg: format!("duplicate node id {}", id),
                        });
                    }
                    weights[id - 1] = val;
                }
                'e' => {
                    let u: usize = toks.number()?;
                    let v: usize = toks.number()?;
                    toks.end()?;
                    if u < 1 || u > nnodes {
                        return Err(DimacsError::Format {
                            line: toks.line,
                            msg: format!("invalid node id {} in edge", u),
                        });
                    }
                    if v < 1 || v > nnodes {
                        return Err(DimacsError::Format {
                            line: toks.line,
                            msg: format!("invalid node id {} in edge", v),
                        });
                    }
                    if u == v {
                        return Err(DimacsError::Format {
                            line: toks.line,
                            msg: format!("invalid loop ({},{}) in edge", u, u),
                        });
                    }
                    if !edges.insert((min(u, v), max(u, v))) {
                        return Err(DimacsError::Format {
                            line: toks.line,
                            msg: format!("duplicate edge ({},{})", u, v),
                        });
                    }
                    g.add_edge(gnodes[u - 1], gnodes[v - 1]);
                }
                'd' => {
                    let d: usize = toks.number()?;
                    let m = match toks.next() {
                        Some("LINF") => Metric::LINF,
                        Some("L2S") => Metric::L2S,
                        Some(m) if !m.is_empty() && m.starts_with('L') => {
                            let p: f64 = match m[1..].parse() {
                                Ok(x) => x,
                                Err(_) => {
                                    return Err(DimacsError::Format {
                                        line: toks.line,
                                        msg: "invalid norm".to_string(),
                                    });
                                }
                            };
                            if p <= 0.0 {
                                return Err(DimacsError::Format {
                                    line: toks.line,
                                    msg: format!("p of p-norm must be > 0 (got: {})", p),
                                });
                            }
                            Metric::L(p)
                        }
                        Some(_) => {
                            return Err(DimacsError::Format {
                                line: toks.line,
                                msg: "invalid norm".to_string(),
                            });
                        }
                        None => {
                            return Err(DimacsError::Format {
                                line: toks.line,
                                msg: "missing norm".to_string(),
                            });
                        }
                    };
                    toks.end()?;

                    if d < 1 {
                        return Err(DimacsError::Format {
                            line: toks.line,
                            msg: format!("invalid dimension {} < 1", d),
                        });
                    }
                    if dim > 0 {
                        return Err(DimacsError::Format {
                            line: toks.line,
                            msg: "duplicate dimension".to_string(),
                        });
                    }

                    dim = d;
                    metric = Some(m);
                    vertices.reserve(nnodes);
                }
                'v' => {
                    if dim == 0 {
                        return Err(DimacsError::Format {
                            line: toks.line,
                            msg: "missing dimension line before vertex line".to_string(),
                        });
                    }

                    let mut vs: Vec<f64> = Vec::new();
                    for _ in 0..dim {
                        vs.push(toks.number()?);
                    }
                    toks.end()?;

                    if dim != vs.len() {
                        return Err(DimacsError::Format {
                            line: toks.line,
                            msg: format!("vertex line has too many entries {} (expected: {})", vs.len(), dim),
                        });
                    }

                    vertices.push(vs);
                }
                'x' => {
                    let par = toks.str()?;
                    let l: f64 = toks.number()?;
                    toks.end()?;
                    match par {
                        "MINLENGTH" => {
                            if minlength.is_some() {
                                return Err(DimacsError::Format {
                                    line: toks.line,
                                    msg: "duplicate parameter MINLENGTH".to_string(),
                                });
                            }
                            minlength = Some(l)
                        }
                        "MAXLENGTH" => {
                            if maxlength.is_some() {
                                return Err(DimacsError::Format {
                                    line: toks.line,
                                    msg: "duplicate parameter MAXLENGTH".to_string(),
                                });
                            }
                            maxlength = Some(l)
                        }
                        _ => {
                            return Err(DimacsError::Format {
                                line: toks.line,
                                msg: format!("unknown parameter {}", par),
                            });
                        }
                    };
                }
                _ => {
                    return Err(DimacsError::Format {
                        line: toks.line,
                        msg: format!("invalid command {}", d),
                    });
                }
            }
        }

        Ok(())
    })?;

    // verify consistency with vertex data
    if dim > 0 {
        let metric = metric.unwrap();
        let minl = match minlength {
            Some(l) => l,
            _ => 0.0,
        };
        let maxl = match maxlength {
            Some(l) => l,
            _ => f64::INFINITY,
        };
        for u in 0..nnodes {
            for v in u + 1..nnodes {
                let d = dist(&vertices[u], &vertices[v], metric);
                // invalid edges might have infinite lengths
                if !edges.contains(&(u + 1, v + 1)) {
                    // edge does not exist, the distance should be invalid
                    if d >= minl && d <= maxl {
                        return Err(DimacsError::Format {
                            line: 0,
                            msg: format!("edge ({},{}) should be contained in the graph", u, v),
                        });
                    }
                } else {
                    // edge exists, the distance must be valid
                    if d < minl {
                        return Err(DimacsError::Format {
                            line: 0,
                            msg: format!("edge ({},{}) should not be contained in the graph (too short)", u, v),
                        });
                    }
                    if d > maxl {
                        return Err(DimacsError::Format {
                            line: 0,
                            msg: format!("edge ({},{}) should not be contained in the graph (too long)", u, v),
                        });
                    }
                }
            }
        }
    }

    Ok((g.into_graph(), weights))
}

fn dist(x: &[f64], y: &[f64], metric: Metric) -> f64 {
    let mut d: f64 = 0.0;
    match metric {
        Metric::LINF => {
            for i in 0..x.len() {
                d = f64::max(d, f64::abs(x[i] - y[i]));
            }
        }
        Metric::L2S => {
            for i in 0..x.len() {
                d += (x[i] - y[i]) * (x[i] - y[i]);
            }
        }
        Metric::L(p) => {
            for i in 0..x.len() {
                d += (x[i] - y[i]).abs().powf(p);
            }
            d = d.powf(1.0 / p);
        }
    }
    d
}

#[cfg(test)]
mod tests {
    use super::read_dimacs;
    use super::read_from_buf;
    use crate::traits::{FiniteGraph, IndexGraph, Undirected};
    use crate::LinkedListGraph;
    use std::io::Cursor;

    #[test]
    fn test_read() {
        let file = "
c some comment

p edge 12 5
";
        read_dimacs(&mut Cursor::new(file), &mut |c, toks| {
            assert_eq!(c, 'p');
            assert_eq!(toks.next(), Some("edge"));
            assert_eq!(toks.number::<usize>().unwrap(), 12);
            assert_eq!(toks.number::<usize>().unwrap(), 5);
            assert_eq!(toks.next(), None);
            Ok(())
        })
        .unwrap();
    }

    #[test]
    fn parse_file_test() {
        let file = "c this is a test file

p edge 6 9
  n 1 12
n 6 42.23

c there might be empty lines

e 1 4
e 1 5
e 1 6
e 2 4
e 2 5
e 2 6
e 3 4
e 3 5
e 3 6

d 2 L2
v 1 1
v 1 2
v 1 3
v 10 1
v 10 2
v 10 3

x MINLENGTH 5
x MAXLENGTH 100

c end of the file
";
        let (g, weights) = read_from_buf::<_, LinkedListGraph>(&mut Cursor::new(file)).unwrap();

        assert_eq!(g.num_nodes(), 6);
        assert_eq!(g.num_edges(), 9);

        for u in 0..3 {
            let mut vs: Vec<_> = g.neighs(g.id2node(u)).map(|(_, v)| g.node_id(v)).collect();
            vs.sort();
            assert_eq!(vs, vec![3, 4, 5]);
        }

        for v in 3..6 {
            let mut vs: Vec<_> = g.neighs(g.id2node(v)).map(|(_, v)| g.node_id(v)).collect();
            vs.sort();
            assert_eq!(vs, vec![0, 1, 2]);
        }

        for u in g.nodes() {
            match (g.node_id(u), weights[g.node_id(u)]) {
                (0, w) => assert_eq!(w, 12.0),
                (5, w) => assert_eq!(w, 42.23),
                (_, w) => assert_eq!(w, 0.0),
            }
        }
    }
}
