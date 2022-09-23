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

//! Read and write routines for the MPS format.

use crate::{Buildable, Builder, IndexDigraph};
use std::collections::HashMap;
use std::error;
use std::fmt;
use std::io::{self, BufRead, BufReader, Read};

/// Error when reading a file in MPS format.
#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    Format { line: usize, msg: String },
    Data { line: usize, msg: String },
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Error::Io(err)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> std::result::Result<(), fmt::Error> {
        use self::Error::*;
        match self {
            Io(err) => err.fmt(fmt),
            Format { line, msg } => write!(fmt, "Format error on line {}: {}", line, msg),
            Data { line, msg } => write!(fmt, "Data error on line {}: {}", line, msg),
        }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        match self {
            Error::Io(err) => Some(err),
            _ => None,
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

/// An MCF instance.
pub struct Instance<G> {
    /// The name of the instance.
    pub name: Option<String>,
    /// The graph.
    pub graph: G,
    /// The node balance.
    pub balances: Vec<f64>,
    /// The lower bounds.
    pub lower: Vec<f64>,
    /// The upper bounds.
    pub upper: Vec<f64>,
    /// The arc costs.
    pub costs: Vec<f64>,
    /// Names of the nodes.
    ///
    /// These are the row names in the MPS file.
    pub node_names: Vec<String>,
    /// Names of the edges.
    ///
    /// These are the column names in the MPS file.
    pub edge_names: Vec<String>,
}

fn find_token(line: &str, beg: usize, end: usize) -> &str {
    if end <= line.len() {
        line[beg..end].trim()
    } else if beg < line.len() {
        line[beg..].trim()
    } else {
        &line[0..0]
    }
}

struct Reader<R: BufRead> {
    line: usize,
    buf: String,
    io: R,
}

impl<R: BufRead> Reader<R> {
    /// Read the next input line, return `true` on success.
    ///
    /// Empty lines and comment lines (those starting with a '*') are skipped
    fn next_line(&mut self) -> Result<bool> {
        loop {
            self.line += 1;
            self.buf.clear();
            if self.io.read_line(&mut self.buf)? == 0 {
                return Ok(false);
            }

            // skip empty lines and comments, i.e. lines starting with a '*'
            if !self.buf.trim().is_empty() && !self.buf.starts_with('*') {
                return Ok(true);
            }
        }
    }

    /// Reads the next non-section line.
    ///
    /// If the next line is a non-section line, returns `true`.
    /// If the next line is a section line, returns `false`.
    /// If there is no next line, returns an error.
    fn next_field_line(&mut self) -> Result<bool> {
        if self.next_line()? {
            Ok(!self.is_section_header())
        } else {
            Err(self.fmt_error("Unexpected end of file (require ENDATA)".to_string()))
        }
    }

    /// Return `true` if the current line is a section header.
    ///
    /// These are those lines not starting with a space.
    fn is_section_header(&self) -> bool {
        !self.buf.starts_with(' ')
    }

    /// Return the i-th field.
    fn field(&self, i: usize) -> &str {
        match i {
            0 => {
                assert!(self.is_section_header());
                find_token(&self.buf, 0, 14)
            }
            2 => find_token(&self.buf, 1, 3),
            5 => find_token(&self.buf, 4, 14),
            15 => find_token(&self.buf, 14, 24),
            25 => find_token(&self.buf, 24, 39),
            40 => find_token(&self.buf, 39, 49),
            50 => find_token(&self.buf, 49, self.buf.len().max(50)),
            _ => unimplemented!("Invalid field number"),
        }
    }

    /// Return the i-th field or an error if it is empty.
    fn non_empty_field(&self, i: usize) -> Result<&str> {
        let f = self.field(i);
        if !f.is_empty() {
            Ok(f)
        } else {
            Err(self.fmt_error(format!("Expected non-empty field in column {}", i)))
        }
    }

    /// Return an error if not all fields starting from the given field are empty.
    fn ensure_is_empty(&self, i: usize) -> Result<()> {
        if let 1 | 2 | 5 | 15 | 25 | 40 | 50 = i {
            if i > self.buf.len() || self.buf[i..].trim().is_empty() {
                Ok(())
            } else {
                Err(self.fmt_error(format!("Unexpected data after column {}", i)))
            }
        } else {
            unimplemented!("Invalid field number")
        }
    }

    /// Returns a format-error for the current line.
    fn fmt_error(&self, msg: String) -> Error {
        Error::Format { line: self.line, msg }
    }

    /// Returns a data-error for the current line.
    fn data_error(&self, msg: String) -> Error {
        Error::Data { line: self.line, msg }
    }
}

struct NodeInfo<N> {
    node: N,
    balance: Option<f64>,
}

impl<N> NodeInfo<N> {
    fn new(u: N) -> NodeInfo<N> {
        NodeInfo { node: u, balance: None }
    }
}

struct EdgeInfo<N> {
    cost: Option<f64>,
    src: Option<N>,
    snk: Option<N>,
    lb: Option<f64>,
    ub: Option<f64>,
}

impl<N> EdgeInfo<N> {
    fn new() -> EdgeInfo<N> {
        EdgeInfo {
            cost: None,
            src: None,
            snk: None,
            lb: None,
            ub: None,
        }
    }
}

fn add_edge<R: BufRead, N: Copy>(
    reader: &Reader<R>,
    col: &str,
    row: &str,
    coeff: &str,
    e: &mut EdgeInfo<N>,
    obj_row: &Option<String>,
    rows: &mut HashMap<String, NodeInfo<N>>,
) -> Result<()> {
    let coeff = coeff
        .parse::<f64>()
        .map_err(|err| reader.fmt_error(format!("Invalid coefficient: {}", err)))?;

    if obj_row.as_ref().map(|obj| obj == row).unwrap_or(false) {
        // Coefficient for the objective
        if e.cost.is_some() {
            return Err(reader.data_error(format!("Multiple cost coefficients in column {}", col)));
        }
        e.cost = Some(coeff)
    } else {
        let u = rows
            .get(row)
            .ok_or_else(|| reader.data_error(format!("Unknown row: {}", row)))?;

        #[allow(clippy::float_cmp)]
        if coeff == 1.0 {
            // Coefficient for some flow conservation constraint
            if e.src.is_some() {
                return Err(reader.data_error(format!("Multiple +1 coefficients in column {}", col)));
            }
            e.src = Some(u.node);
        } else if coeff == -1.0 {
            if e.snk.is_some() {
                return Err(reader.data_error(format!("Multiple -1 coefficients in column {}", col)));
            }
            e.snk = Some(u.node);
        } else {
            return Err(reader.data_error(format!("Only coefficients +1 and -1 are supported (got: {})", coeff)));
        }
    }

    Ok(())
}

fn add_rhs<R: BufRead, N: Copy>(
    reader: &Reader<R>,
    row: &str,
    rhs: &str,
    rows: &mut HashMap<String, NodeInfo<N>>,
) -> Result<()> {
    let rhs = rhs
        .parse::<f64>()
        .map_err(|err| reader.fmt_error(format!("Invalid right-hand side: {}", err)))?;

    let u = rows
        .get_mut(row)
        .ok_or_else(|| reader.data_error(format!("Unknown row: {}", row)))?;

    if u.balance.is_some() {
        return Err(reader.data_error(format!("Multiple right-hand side values in row {}", row)));
    }
    u.balance = Some(rhs);

    Ok(())
}

/// Read a file in MPS format from the reader.
pub fn read<'a, G, R: Read>(reader: R) -> Result<Instance<G>>
where
    G: IndexDigraph<'a> + Buildable,
{
    let mut reader = Reader {
        io: BufReader::new(reader),
        line: 0,
        buf: String::new(),
    };

    let mut name = None;
    let mut minimize = None;
    let mut obj_row = None;
    let mut cols = HashMap::new(); // corresponding to edges
    let mut rows = HashMap::new(); // corresponding to nodes
    let mut rhsname = None;
    let mut bndname = None;
    let mut graph = G::new_builder();

    if !reader.next_line()? {
        return Err(reader.fmt_error("Empty file".to_string()));
    }

    loop {
        if !reader.is_section_header() {
            return Err(reader.fmt_error("Expected a section header (non-whitespace in column 0)".to_string()));
        }
        let section = reader.field(0);
        match section {
            "NAME" => {
                let n = reader.field(15);
                if !n.is_empty() {
                    name = Some(n.to_string());
                }
                if reader.next_field_line()? {
                    return Err(reader.fmt_error("Invalid record in NAME section".to_string()));
                }
            }
            "ROWS" => {
                while reader.next_field_line()? {
                    match reader.field(2) {
                        "N" => {
                            if obj_row.is_some() {
                                return Err(reader.fmt_error("Only one objective row is supported".to_string()));
                            }
                            obj_row = Some(reader.non_empty_field(5)?.to_string());
                        }
                        "E" => {
                            let row = reader.non_empty_field(5)?;
                            reader.ensure_is_empty(15)?;
                            if rows.insert(row.to_string(), NodeInfo::new(graph.add_node())).is_some() {
                                return Err(reader.data_error(format!("Row {} specified multiple times", row)));
                            }
                        }
                        "L" | "G" => {
                            return Err(reader.fmt_error("Only equality constraints are supported".to_string()))
                        }
                        _ => {
                            return Err(reader
                                .fmt_error(format!("Invalid row type {} (expected N, L, E or G)", reader.field(2))))
                        }
                    }
                }
            }
            "COLUMNS" => {
                while reader.next_field_line()? {
                    if !reader.field(2).is_empty() {
                        return Err(reader.fmt_error("Unexpected field in column 2".to_string()));
                    }

                    let col = reader.non_empty_field(5)?; // name of the edge
                                                          // Get the edge.
                    let e = cols.entry(col.to_string()).or_insert_with(EdgeInfo::new);

                    let row1 = reader.non_empty_field(15)?; // node
                    let coeff1 = reader.non_empty_field(25)?; // src/snk

                    add_edge(&reader, col, row1, coeff1, e, &obj_row, &mut rows)?;

                    let row2 = reader.field(40);
                    let coeff2 = reader.field(50);
                    if row2.is_empty() != coeff2.is_empty() {
                        if row2.is_empty() {
                            return Err(reader.fmt_error("Second row name missing".to_string()));
                        } else {
                            return Err(reader.fmt_error("Second coefficient missing".to_string()));
                        }
                    }

                    if !row2.is_empty() {
                        add_edge(&reader, col, row2, coeff2, e, &obj_row, &mut rows)?;
                    }
                }
            }
            "RHS" => {
                while reader.next_field_line()? {
                    if !reader.field(2).is_empty() {
                        return Err(reader.fmt_error("Unexpected field in column 2".to_string()));
                    }

                    if let Some(rhsname) = rhsname.as_ref() {
                        if rhsname != reader.non_empty_field(5)? {
                            return Err(reader.data_error("Only one right-hand side is suported".to_string()));
                        }
                    } else {
                        rhsname = Some(reader.non_empty_field(5)?.to_string());
                    }

                    let row1 = reader.non_empty_field(15)?;
                    let rhs1 = reader.non_empty_field(25)?;
                    add_rhs(&reader, row1, rhs1, &mut rows)?;

                    let row2 = reader.field(40);
                    let rhs2 = reader.field(50);

                    if row2.is_empty() != rhs2.is_empty() {
                        if row2.is_empty() {
                            return Err(reader.fmt_error("Second row name missing".to_string()));
                        } else {
                            return Err(reader.fmt_error("Second right-hand side value missing".to_string()));
                        }
                    }
                    if !row2.is_empty() {
                        add_rhs(&reader, row2, rhs2, &mut rows)?;
                    }
                }
            }
            "BOUNDS" => {
                while reader.next_field_line()? {
                    if let Some(bndname) = bndname.as_ref() {
                        if bndname != reader.non_empty_field(5)? {
                            return Err(reader.data_error("Only one bound name is suported".to_string()));
                        }
                    } else {
                        bndname = Some(reader.non_empty_field(5)?.to_string());
                    }

                    let typ = reader.non_empty_field(2)?;
                    let (lb, ub) = match typ {
                        "FR" => {
                            reader.ensure_is_empty(25)?;
                            (-f64::INFINITY, f64::INFINITY)
                        }
                        "MI" => {
                            reader.ensure_is_empty(25)?;
                            (-f64::INFINITY, 0.0)
                        }
                        _ => {
                            reader.ensure_is_empty(40)?;
                            let val = reader
                                .non_empty_field(25)?
                                .parse::<f64>()
                                .map_err(|err| reader.fmt_error(format!("Invalid bound: {}", err)))?;
                            (val, val)
                        }
                    };

                    let col = reader.non_empty_field(15)?;
                    let e = cols
                        .get_mut(col)
                        .ok_or_else(|| reader.data_error(format!("Unknown column: {}", col)))?;

                    if let "UP" | "FX" | "MI" | "FR" = typ {
                        if e.ub.is_some() {
                            return Err(reader.data_error(format!("Multiple upper bounds for {}", col)));
                        }
                        e.ub = Some(ub);
                    }
                    if let "LO" | "FX" | "FR" = typ {
                        if e.lb.is_some() {
                            return Err(reader.data_error(format!("Multiple lower bounds for {}", col)));
                        }
                        e.lb = Some(lb);
                    }
                }
            }
            "RANGES" => {
                if reader.next_field_line()? {
                    return Err(reader.data_error("RANGES section is not supported".to_string()));
                }
            }
            "OBJSENSE" => {
                while reader.next_field_line()? {
                    if minimize.is_some() {
                        return Err(reader.fmt_error("OBJSENSE must be specified at most once".to_string()));
                    }
                    match reader.field(5) {
                        "MIN" => minimize = Some(true),
                        "MAX" => minimize = Some(false),
                        _ => {
                            return Err(reader.fmt_error(format!(
                                "Invalid objective sense {} (must be 'MIN' or 'MAX')",
                                reader.field(5)
                            )))
                        }
                    }
                    reader.ensure_is_empty(15)?;
                }
            }
            "ENDATA" => {
                if reader.next_line()? {
                    return Err(reader.fmt_error("Unexpected line after ENDATA".to_string()));
                }
                break;
            }
            _ => {
                return Err(reader.fmt_error(format!("Unknown section: {}", section)));
            }
        }
    }

    // We have everything, create the graph.
    let n = rows.len();
    let m = cols.len();

    let mut node_names = vec![String::new(); n];
    let mut balances = vec![0.0; n];
    let mut edge_names = Vec::with_capacity(m);
    let mut lower = Vec::with_capacity(m);
    let mut upper = Vec::with_capacity(m);
    let mut costs = Vec::with_capacity(m);

    for (uname, u) in rows {
        node_names[graph.node2id(u.node)] = uname;
        balances[graph.node2id(u.node)] = u.balance.unwrap_or(0.0);
    }

    for (ename, e) in cols {
        let u = e
            .src
            .ok_or_else(|| reader.data_error(format!("Missing +1 coefficient for edge {}", ename)))?;
        let v = e
            .snk
            .ok_or_else(|| reader.data_error(format!("Missing -1 coefficient for edge {}", ename)))?;
        graph.add_edge(u, v);
        edge_names.push(ename);
        lower.push(e.lb.unwrap_or(0.0));
        upper.push(e.ub.unwrap_or(f64::INFINITY));
        costs.push(e.cost.unwrap_or(0.0));
    }
    let graph = graph.into_graph();

    if !minimize.unwrap_or(true) {
        for c in &mut costs {
            *c = -*c;
        }
    }

    Ok(Instance {
        name,
        graph,
        balances,
        lower,
        upper,
        costs,
        node_names,
        edge_names,
    })
}

pub fn read_from_file<'a, G>(filename: &str) -> Result<Instance<G>>
where
    G: IndexDigraph<'a> + Buildable,
{
    read(std::fs::File::open(filename)?)
}
