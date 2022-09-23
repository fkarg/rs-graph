// Copyright (c) 2016-2021 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! Reading files in `SteinLib` format.
//!
//! This reader supports the following extensions to the `SteinLib` format:
//!
//! 1. Additional drawing attributes section
//!
//!   ```ignore
//!   SECTION Drawing
//!   A <u> <v> <attribute>...
//!   E <u> <v> <attribute>...
//!   END
//!   ```
//!
//!   This is a list of drawing attributes for each edge. Possible
//!   attributes are
//!   - `bl` the arc should be bend to the left
//!   - `br` the arc should be bend to the right

use crate::IndexGraph;

use std::result;

mod parser;
pub use self::parser::{read, SteinlibError as Error};

/// Type of values with optional error code.
pub type Result<T> = result::Result<T, Error>;

/// Edge drawing attributes.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EdgeAttr {
    /// Arc should be bend to the left.
    BendLeft,
    /// Arc should be bend to the right.
    BendRight,
}

/// An SteinLib instance.
pub struct Instance<G>
where
    G: for<'a> IndexGraph<'a>,
{
    /// The graph.
    pub graph: G,
    /// The edge weights.
    pub weights: Vec<f64>,
    /// The node coordinates.
    pub coordinates: Vec<Vec<f64>>,
    /// The edge attributes.
    pub edgeattrs: Vec<Vec<EdgeAttr>>,
}
