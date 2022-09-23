/*
 * Copyright (c) 2020-2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! Graph adapters.
//!
//! Graph adapters are small types wrapping another graph type. A graph
//! adapter provides a modified view on the underlying graph. For instance,
//! the [`ReverseDigraph`] adapter swaps the direction of each (directed)
//! edge of a wrapped digraph.
//!
//! Adapters do not copy the underlying graph, they just change the meaning
//! of the methods.

pub mod network;
pub use self::network::{Network, NetworkEdge};

mod reversedigraph;
pub use self::reversedigraph::{reverse, ReverseDigraph};
