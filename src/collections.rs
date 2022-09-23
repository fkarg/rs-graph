/*
 * Copyright (c) 2018, 2020, 2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! Some traits and implementations of data structures to be used in algorithms.

mod map;
mod priqueue;
mod queue;
mod set;
mod stack;

pub use self::map::{ItemMap, NodeVecMap};
pub use self::priqueue::{BinHeap, ItemPriQueue};
pub use self::queue::ItemQueue;
pub use self::set::ItemSet;
pub use self::stack::ItemStack;
