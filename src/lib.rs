// Copyright (c) 2015-2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//#![forbid(unsafe_code)]

//! A library for basic graph data structures and algorithms.

mod num {
    pub use num_iter as iter;
    pub use num_traits as traits;
}

// # Data structures

pub mod traits;
pub use self::traits::{Digraph, Graph};
pub use self::traits::{IndexDigraph, IndexGraph};
pub use self::traits::{NumberedDigraph, NumberedGraph};

pub mod adapters;
pub use self::adapters::{reverse, Network, ReverseDigraph};

pub mod adjacencies;

pub mod filtered;

pub mod builder;
pub use crate::builder::{Buildable, Builder};

pub mod linkedlistgraph;
pub use self::linkedlistgraph::LinkedListGraph;

pub mod vecgraph;
pub use self::vecgraph::VecGraph;

pub mod attributes;
pub use self::attributes::{AttributedGraph, EdgeAttributes, NodeAttributes};

/// Graph classes
pub mod classes;

/// The default graph type.
///
/// A vector graph with up to 2^31 nodes and edges.
pub type Net = self::VecGraph<u32>;

pub mod collections;

// # Algorithms

pub mod algorithms;
pub mod branching;
pub mod maxflow;
pub mod mcf;
pub mod mst;
pub mod search;
pub mod shortestpath;

// # Drawing

pub mod draw;
pub mod string;

#[cfg(any(feature = "dimacs"))]
pub mod dimacs;
#[cfg(any(feature = "mps"))]
pub mod mps;
#[cfg(any(feature = "steinlib"))]
pub mod steinlib;
