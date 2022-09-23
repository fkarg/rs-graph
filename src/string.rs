/*
 * Copyright (c) 2019-2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! A small module to read graphs from ascii art.
//!
//! See [`from_ascii`] for a detailed explanation.
//!
//! *Warning*: the main purpose of this module is its use in
//! documentation comments and examples. It is not meant for
//! production use.

use crate::builder::{Buildable, Builder};
use crate::linkedlistgraph::LinkedListGraph;
use crate::traits::{Directed, GraphType, IndexGraph};

use std::collections::{HashMap, HashSet, VecDeque};
use std::error;
use std::num::ParseIntError;
use std::str::{from_utf8, Utf8Error};

/// Error reading an ascii-art graph.
#[derive(Debug)]
pub enum Error {
    /// An invalid character appeared in the ascii text.
    InvalidCharacter(char),
    /// Parsing a number (edge weight) failed.
    InvalidNumber(Box<dyn error::Error>),
}

impl std::fmt::Display for Error {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            Error::InvalidCharacter(c) => write!(fmt, "Invalid character: {}", c),
            Error::InvalidNumber(e) => write!(fmt, "Invalid number: {}", e),
        }
    }
}

impl std::error::Error for Error {}

impl From<ParseIntError> for Error {
    fn from(e: ParseIntError) -> Error {
        Error::InvalidNumber(e.into())
    }
}

impl From<Utf8Error> for Error {
    fn from(e: Utf8Error) -> Error {
        Error::InvalidNumber(e.into())
    }
}

/// The data returned by `from_ascii`.
pub struct Data<'a, G>
where
    G: GraphType<'a>,
{
    /// The graph.
    pub graph: G,
    /// Map from character to node for named nodes.
    pub nodes: HashMap<char, G::Node>,
    /// The edge weights.
    pub weights: Vec<usize>,
}

/// Create a graph from ASCII art drawing with edge weights.
///
/// Parses an ASCII-art drawing and generates the corresponding graph.
/// Node are `*` or letters (except for `v` which is used to draw directed
/// edges), edges are sequences of `-`, `|`, `/` and `\` characters. Edges may
/// cross as in the example below.
///
/// Weights are non-negative numbers along the edges. Edges without explicit
/// weight receive the weight 0. The edge weights are returned in a vector in
/// the order of creation (although the order is undefined -- usually this
/// corresponds to `g.edge_id`).
///
/// ```
/// use rs_graph::traits::*;
/// use rs_graph::linkedlistgraph::LinkedListGraph;
/// use rs_graph::string::{Data, from_ascii};
///
/// let Data{ graph: g, weights, nodes } = from_ascii::<LinkedListGraph>(r"
///       a  b
///       |  |
///   ----|-----
///  /   223 |  \
/// |     | /    |
/// |   --|-     |
///  \ /  |     /
///   -   *-10--").unwrap();
///
/// assert_eq!(g.neighs(nodes[&'a']).map(|(e,_)| weights[g.edge_id(e)]).collect::<Vec<_>>(), vec![223]);
/// assert_eq!(g.neighs(nodes[&'b']).map(|(e,_)| weights[g.edge_id(e)]).collect::<Vec<_>>(), vec![10]);
/// ```
///
/// Usually edges are undirected. Directed edges can be inserted by ending an
/// edge in one of the characters `<`, `>`, `^`, `v` or `@` (where the `@` can
/// be used in place of any of the other head characters; for diagonal directed
/// connections it is the only alternative).
///
/// ```
/// use rs_graph::traits::*;
/// use rs_graph::linkedlistgraph::LinkedListGraph;
/// use rs_graph::string::{Data, from_ascii};
///
/// let Data { graph: g, nodes, .. } = from_ascii::<LinkedListGraph>(r"
///    *  *  *
///     \ | /
///      @v@
///    *->a<-*
///      @^@
///     / | \
///    *  *  *").unwrap();
/// let a = nodes[&'a'];
///
/// assert_eq!(g.num_nodes(), 9);
/// assert_eq!(g.num_edges(), 8);
/// for u in g.nodes() {
///     if u == a {
///         assert_eq!(g.inedges(u).count(), 8);
///         assert_eq!(g.outedges(u).count(), 0);
///     } else {
///         assert_eq!(g.inedges(u).count(), 0);
///         assert_eq!(g.outedges(u).count(), 1);
///     }
/// }
/// ```
///
/// Nodes are created (and thus numbered) row-wise. Nodes that have a character
/// label can be access through the `nodes` field of the returned data. The
/// order of the edges is undefined.
///
/// *Note*: this function is meant to be used in test cases, it should not be
/// used in production code.
#[allow(clippy::cognitive_complexity)]
pub fn from_ascii<G>(text: &str) -> Result<Data<G>, Error>
where
    G: Buildable,
    G: for<'a> GraphType<'a, Node = <<G as Buildable>::Builder as Builder>::Node>,
{
    let lines = text.lines().map(|l| l.as_bytes()).collect::<Vec<_>>();

    // compute numbers of rows and columns
    let nrows = lines.len();
    let ncols = lines.iter().map(|l| l.len()).max().unwrap_or(0);

    let mut h = LinkedListGraph::<u32>::new_builder();
    let hnodes = (0..nrows)
        .map(|_| (0..ncols).map(|_| h.add_node()).collect::<Vec<_>>())
        .collect::<Vec<_>>();

    let mut hweights = HashMap::new();
    let mut hdirected = HashSet::new();

    // insert horizontal edges
    for i in 0..nrows {
        for j in 1..ncols {
            if j >= lines[i].len() {
                break;
            }
            if (lines[i][j - 1] == b'-' && is_node_or(lines[i][j], b"/\\-"))
                || (lines[i][j] == b'-' && is_node_or(lines[i][j - 1], b"/\\-"))
            {
                h.add_edge(hnodes[i][j - 1], hnodes[i][j]);
                h.add_edge(hnodes[i][j], hnodes[i][j - 1]);
            }
        }
    }

    // insert vertical edges
    for j in 0..ncols {
        for i in 1..nrows {
            if j >= lines[i - 1].len() || j >= lines[i].len() {
                continue;
            }
            if (lines[i - 1][j] == b'|' && is_node_or(lines[i][j], b"/\\|"))
                || (lines[i][j] == b'|' && is_node_or(lines[i - 1][j], b"/\\|"))
            {
                h.add_edge(hnodes[i - 1][j], hnodes[i][j]);
                h.add_edge(hnodes[i][j], hnodes[i - 1][j]);
            }
        }
    }

    // insert main diagonal edges
    for j in 1..ncols {
        for i in 1..nrows {
            if j > lines[i - 1].len() || j >= lines[i].len() {
                continue;
            }
            if (lines[i - 1][j - 1] == b'\\' && is_node_or(lines[i][j], b"\\-|"))
                || (lines[i][j] == b'\\' && is_node_or(lines[i - 1][j - 1], b"\\-|"))
            {
                h.add_edge(hnodes[i - 1][j - 1], hnodes[i][j]);
                h.add_edge(hnodes[i][j], hnodes[i - 1][j - 1]);
            }
        }
    }

    // insert secondary diagonal edges
    for j in 0..ncols - 1 {
        for i in 1..nrows {
            if j + 1 >= lines[i - 1].len() || j >= lines[i].len() {
                continue;
            }
            if (lines[i - 1][j + 1] == b'/' && is_node_or(lines[i][j], b"/-|*"))
                || (lines[i][j] == b'/' && is_node_or(lines[i - 1][j + 1], b"/-|*"))
            {
                h.add_edge(hnodes[i - 1][j + 1], hnodes[i][j]);
                h.add_edge(hnodes[i][j], hnodes[i - 1][j + 1]);
            }
        }
    }

    // insert directed end-points >, <, ^, v or @
    for i in 0..nrows {
        for j in 0..ncols {
            if j > 0
                && lines[i].get(j - 1).map(|&c| c == b'-').unwrap_or(false)
                && lines[i].get(j).map(|&c| c == b'@' || c == b'>').unwrap_or(false)
                && lines[i].get(j + 1).cloned().map(is_node).unwrap_or(false)
            {
                let e = h.add_edge(hnodes[i][j - 1], hnodes[i][j + 1]);
                hdirected.insert(e);
            }
            if j > 0
                && lines[i].get(j - 1).cloned().map(is_node).unwrap_or(false)
                && lines[i].get(j).map(|&c| c == b'@' || c == b'<').unwrap_or(false)
                && lines[i].get(j + 1).map(|&c| c == b'-').unwrap_or(false)
            {
                let e = h.add_edge(hnodes[i][j + 1], hnodes[i][j - 1]);
                hdirected.insert(e);
            }
            if i > 0
                && i + 1 < nrows
                && lines[i - 1].get(j).cloned().map(is_node).unwrap_or(false)
                && lines[i].get(j).map(|&c| c == b'@' || c == b'^').unwrap_or(false)
                && lines[i + 1].get(j).map(|&c| c == b'|').unwrap_or(false)
            {
                let e = h.add_edge(hnodes[i + 1][j], hnodes[i - 1][j]);
                hdirected.insert(e);
            }
            if i > 0
                && i + 1 < nrows
                && lines[i - 1].get(j).map(|&c| c == b'|').unwrap_or(false)
                && lines[i].get(j).map(|&c| c == b'@' || c == b'v').unwrap_or(false)
                && lines[i + 1].get(j).cloned().map(is_node).unwrap_or(false)
            {
                let e = h.add_edge(hnodes[i - 1][j], hnodes[i + 1][j]);
                hdirected.insert(e);
            }
            // diagonals
            if i > 0
                && i + 1 < nrows
                && j > 0
                && lines[i - 1].get(j - 1).map(|&c| c == b'\\').unwrap_or(false)
                && lines[i].get(j).map(|&c| c == b'@').unwrap_or(false)
                && lines[i + 1].get(j + 1).cloned().map(is_node).unwrap_or(false)
            {
                let e = h.add_edge(hnodes[i - 1][j - 1], hnodes[i + 1][j + 1]);
                hdirected.insert(e);
            }
            if i > 0
                && i + 1 < nrows
                && j > 0
                && lines[i - 1].get(j - 1).cloned().map(is_node).unwrap_or(false)
                && lines[i].get(j).map(|&c| c == b'@').unwrap_or(false)
                && lines[i + 1].get(j + 1).map(|&c| c == b'\\').unwrap_or(false)
            {
                let e = h.add_edge(hnodes[i + 1][j + 1], hnodes[i - 1][j - 1]);
                hdirected.insert(e);
            }
            if i > 0
                && i + 1 < nrows
                && j > 0
                && lines[i - 1].get(j + 1).map(|&c| c == b'/').unwrap_or(false)
                && lines[i].get(j).map(|&c| c == b'@').unwrap_or(false)
                && lines[i + 1].get(j - 1).cloned().map(is_node).unwrap_or(false)
            {
                let e = h.add_edge(hnodes[i - 1][j + 1], hnodes[i + 1][j - 1]);
                hdirected.insert(e);
            }
            if i > 0
                && i + 1 < nrows
                && j > 0
                && lines[i - 1].get(j + 1).cloned().map(is_node).unwrap_or(false)
                && lines[i].get(j).map(|&c| c == b'@').unwrap_or(false)
                && lines[i + 1].get(j - 1).map(|&c| c == b'/').unwrap_or(false)
            {
                let e = h.add_edge(hnodes[i + 1][j - 1], hnodes[i - 1][j + 1]);
                hdirected.insert(e);
            }
        }
    }

    let get_weight = |i: usize, j: usize| -> Result<usize, Error> {
        let mut beg = j;
        while beg > 0 && lines[i][beg - 1].is_ascii_digit() {
            beg -= 1;
        }
        let mut end = j;
        while lines[i].get(end).map(|c| c.is_ascii_digit()).unwrap_or(false) {
            end += 1;
        }
        Ok(from_utf8(&lines[i][beg..end])?.parse::<usize>()?)
    };

    // insert crossing edges
    for j in 0..ncols {
        for i in 0..nrows {
            // horizontal
            if j > 0
                && j + 1 < lines[i].len()
                && lines[i][j - 1] == b'-'
                && lines[i][j + 1] == b'-'
                && (lines[i][j] == b'|' || lines[i][j].is_ascii_digit())
            {
                let e = h.add_edge(hnodes[i][j - 1], hnodes[i][j + 1]);
                let f = h.add_edge(hnodes[i][j + 1], hnodes[i][j - 1]);
                if lines[i][j] != b'|' {
                    let w = get_weight(i, j)?;
                    hweights.insert(e, w);
                    hweights.insert(f, w);
                }
            }
            // vertical
            if i > 0
                && i + 1 < nrows
                && lines[i - 1].get(j).map(|&c| c == b'|').unwrap_or(false)
                && lines[i + 1].get(j).map(|&c| c == b'|').unwrap_or(false)
                && lines[i]
                    .get(j)
                    .map(|&c| c == b'-' || c.is_ascii_digit())
                    .unwrap_or(false)
            {
                let e = h.add_edge(hnodes[i - 1][j], hnodes[i + 1][j]);
                let f = h.add_edge(hnodes[i + 1][j], hnodes[i - 1][j]);
                if lines[i][j] != b'-' {
                    let w = get_weight(i, j)?;
                    hweights.insert(e, w);
                    hweights.insert(f, w);
                }
            }
            // main diagonal
            if i > 0
                && j > 0
                && i + 1 < nrows
                && lines[i - 1].get(j - 1).map(|&c| c == b'\\').unwrap_or(false)
                && lines[i + 1].get(j + 1).map(|&c| c == b'\\').unwrap_or(false)
                && lines[i]
                    .get(j)
                    .map(|&c| c == b'/' || c.is_ascii_digit())
                    .unwrap_or(false)
            {
                let e = h.add_edge(hnodes[i - 1][j - 1], hnodes[i + 1][j + 1]);
                let f = h.add_edge(hnodes[i + 1][j + 1], hnodes[i - 1][j - 1]);
                if lines[i][j] != b'/' {
                    let w = get_weight(i, j)?;
                    hweights.insert(e, w);
                    hweights.insert(f, w);
                }
            }
            // secondary diagonal
            if i > 0
                && j > 0
                && i + 1 < nrows
                && lines[i - 1].get(j + 1).map(|&c| c == b'/').unwrap_or(false)
                && lines[i + 1].get(j - 1).map(|&c| c == b'/').unwrap_or(false)
                && lines[i]
                    .get(j)
                    .map(|&c| c == b'\\' || c.is_ascii_digit())
                    .unwrap_or(false)
            {
                let e = h.add_edge(hnodes[i - 1][j + 1], hnodes[i + 1][j - 1]);
                let f = h.add_edge(hnodes[i + 1][j - 1], hnodes[i - 1][j + 1]);
                if lines[i][j] != b'\\' {
                    let w = get_weight(i, j)?;
                    hweights.insert(e, w);
                    hweights.insert(f, w);
                }
            }
        }
    }

    // insert edges jumping over multi-digit horizontal numbers
    for i in 0..nrows {
        for j in 1..ncols {
            if lines[i].get(j - 1).map(|&c| c == b'-').unwrap_or(false) {
                let mut k = j;
                while lines[i].get(k).map(|c| c.is_ascii_digit()).unwrap_or(false) {
                    k += 1;
                }
                if k >= j + 2 && lines[i].get(k).map(|&c| c == b'-').unwrap_or(false) {
                    let e = h.add_edge(hnodes[i][j - 1], hnodes[i][k]);
                    let f = h.add_edge(hnodes[i][k], hnodes[i][j - 1]);
                    let weight = from_utf8(&lines[i][j..k])?.parse::<usize>()?;
                    hweights.insert(e, weight);
                    hweights.insert(f, weight);
                }
            }
        }
    }

    let h = h.into_graph();

    // construct the graph from the helper graph
    let mut b = G::Builder::new();
    let mut bnodes = HashMap::new();
    let mut weights = vec![];
    let mut namednodes = HashMap::new();

    for i in 0..nrows {
        for j in 0..lines[i].len() {
            if lines[i][j] == b'*' {
                bnodes.insert(hnodes[i][j], b.add_node());
            } else if is_node(lines[i][j]) {
                let u = b.add_node();
                namednodes.insert(lines[i][j] as char, u);
                bnodes.insert(hnodes[i][j], u);
            }
        }
    }

    let mut bnodes_ordered = bnodes.iter().collect::<Vec<_>>();
    bnodes_ordered.sort_by_key(|&(&h_u, _)| h.node_id(h_u));
    for (&h_u, &u) in bnodes_ordered {
        let mut queue = VecDeque::new();
        let mut seen = HashSet::new();
        queue.push_back((h_u, 0, false));
        seen.insert(h_u);
        while let Some((h_v, w, directed)) = queue.pop_front() {
            if let Some(&v) = if h_v != h_u { bnodes.get(&h_v) } else { None } {
                // v is connected to u, add edge
                if directed || h.node_id(h_u) < h.node_id(h_v) {
                    b.add_edge(u, v);
                    weights.push(w);
                }
            } else {
                // otherwise continue search
                for (e, h_w) in h.outedges(h_v) {
                    if !seen.contains(&h_w) {
                        seen.insert(h_w);
                        queue.push_back((
                            h_w,
                            w + hweights.get(&e).unwrap_or(&0),
                            directed || hdirected.contains(&e),
                        ));
                    }
                }
            }
        }
    }

    Ok(Data {
        graph: b.into_graph(),
        nodes: namednodes,
        weights,
    })
}

fn is_node(ch: u8) -> bool {
    ch == b'*' || (ch.is_ascii_alphabetic() && ch != b'v')
}

fn is_node_or(ch: u8, chars: &[u8]) -> bool {
    is_node(ch) || chars.contains(&ch)
}

#[cfg(test)]
mod tests {
    use super::{from_ascii, Data};
    use crate::traits::{FiniteGraph, IndexGraph, Undirected};
    use crate::LinkedListGraph;

    #[test]
    fn test_ascii() {
        for txt in &[
            "a---*---b",
            "
        a
        |
        *
        |
        b",
            r"
        a
         \
          *
         /
        b",
            r"
        a      *--b
         \    /
          ----",
            r"
        a    -
         \  / \
          \/   |
          /\  /
         b  *-",
            r"
        b   --
         \ /  \
          \    |
         / \  /
        a   *-",
            r"
        b  a
        |  |
    ----|-----
   /    |  |  \
  |     | /    |
  |   --|-     |
   \ /  |     /
    -   *-----",
            r"
        b  a
        |  |
    -8--|-----
   /    |  |  \
  |     | /    |
  |   --|-     |
   \ /  |     /
    -   *-10--",
        ] {
            let data = from_ascii::<LinkedListGraph>(txt).unwrap();
            let g = data.graph;
            let a = data.nodes[&'a'];
            let b = data.nodes[&'b'];

            assert_eq!(g.num_nodes(), 3);
            assert_eq!(g.num_edges(), 2);

            assert_eq!(g.nodes().filter(|&u| g.neighs(u).count() == 1).count(), 2);
            assert_eq!(g.nodes().filter(|&u| g.neighs(u).count() == 2).count(), 1);
            assert_eq!(g.neighs(a).count(), 1);
            assert_eq!(g.neighs(b).count(), 1);
        }
    }

    #[test]
    fn test_ascii_with_weights() {
        for txt in &[
            r"
        a        b
         \      /
         223   10
           \  /
            *-",
            r"
        a  b
        |  |
    ----|-----
   /   223 |  \
  |     | /    |
  |   --|-     |
   \ /  |     /
    -   *-10--",
        ] {
            let Data {
                graph: g,
                weights,
                nodes,
            } = from_ascii::<LinkedListGraph>(txt).unwrap();
            let a = nodes[&'a'];
            let b = nodes[&'b'];

            assert_eq!(g.num_nodes(), 3);
            assert_eq!(g.num_edges(), 2);

            assert_eq!(g.nodes().filter(|&u| g.neighs(u).count() == 1).count(), 2);
            assert_eq!(g.nodes().filter(|&u| g.neighs(u).count() == 2).count(), 1);

            for (e, _) in g.neighs(a) {
                assert_eq!(weights[g.edge_id(e)], 223);
            }

            for (e, _) in g.neighs(b) {
                assert_eq!(weights[g.edge_id(e)], 10);
            }
        }
    }

    #[test]
    fn test_ascii_directed() {
        use crate::traits::*;

        for txt in &[
            r"
   *  *  *
    \ | /
     @v@
   *->a<-*
     @^@
    / | \
   *  *  *",
            r"
   *  *  *
    \ | /
     @@@
   *-@a@-*
     @@@
    / | \
   *  *  *",
        ] {
            let Data { graph: g, nodes, .. } = from_ascii::<LinkedListGraph>(txt).unwrap();
            let a = nodes[&'a'];

            assert_eq!(g.num_nodes(), 9);
            assert_eq!(g.num_edges(), 8);
            for u in g.nodes() {
                if u == a {
                    assert_eq!(g.inedges(u).count(), 8);
                    assert_eq!(g.outedges(u).count(), 0);
                } else {
                    assert_eq!(g.inedges(u).count(), 0);
                    assert_eq!(g.outedges(u).count(), 1);
                }
            }
        }
    }

    #[test]
    /// This is a regression test for non-deterministic behaviour. The
    /// `from_ascii` function created edges in random orders, because it iterated
    /// over the entries of a (randomized) hashmap.
    ///
    /// We basically run the algorithm 100 times (on the same, 3-node path) and
    /// check whether the neighbors of the middle node have the same order. It
    /// basically failed every time.
    fn test_deterministic() {
        use crate::string::{from_ascii, Data};
        use crate::traits::*;
        use crate::LinkedListGraph;

        let mut prev = vec![];
        for i in 0..100 {
            let Data { graph: g, nodes, .. } = from_ascii::<LinkedListGraph>("*-s-*").unwrap();
            let s = nodes[&'s'];
            let next = g.neighs(s).map(|(_, v)| g.node_id(v)).collect::<Vec<_>>();

            if i > 0 {
                assert_eq!(prev, next);
            }
            prev = next;
        }
    }
}
