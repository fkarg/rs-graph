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

//! Minimum Cost Flow algorithms.

pub mod simplex;
pub use simplex::{network_simplex, NetworkSimplex};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SolutionState {
    /// Unknown state, the problem has not been solved, yet
    Unknown,
    /// The problem has been solved to optimality
    Optimal,
    /// The problem is infeasible
    Infeasible,
    /// The problem is unbounded
    Unbounded,
}
