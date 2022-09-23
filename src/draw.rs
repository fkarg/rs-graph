// Copyright (c) 2016, 2017, 2018 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! Visualizing graphs.

use crate::traits::GraphType;

/// Trait for node attributes.
pub trait NodeAttr {
    fn set_name(&mut self, name: Option<&str>);

    fn set_label(&mut self, label: Option<usize>);
}

/// Trait for edge attributes.
pub trait EdgeAttr {
    fn set_name(&mut self, name: Option<&str>);

    fn set_label(&mut self, label: Option<usize>);
}

/// Trait for drawing sequences of graphs.
pub trait GraphDrawer<'a, G>
where
    G: GraphType<'a>,
{
    type NodeAttr: NodeAttr;

    type EdgeAttr: EdgeAttr;

    /// Return the default node attribute.
    fn node_default(&self) -> &Self::NodeAttr;

    /// Return the default node attribute.
    fn node_default_mut(&mut self) -> &mut Self::NodeAttr;

    /// Return the attributes of a node.
    fn node(&self, u: G::Node) -> &Self::NodeAttr;

    /// Return the attributes of a node.
    fn node_mut(&mut self, u: G::Node) -> &mut Self::NodeAttr;

    /// Return the default edge attribute.
    fn edge_default(&self) -> &Self::EdgeAttr;

    /// Return the default edge attribute.
    fn edge_default_mut(&mut self) -> &mut Self::EdgeAttr;

    /// Return the attributes of an edge.
    fn edge(&self, e: G::Edge) -> &Self::EdgeAttr;

    /// Return the attributes of an edge.
    fn edge_mut(&mut self, e: G::Edge) -> &mut Self::EdgeAttr;

    /// Add drawing with current attributes.
    fn add_drawing(&mut self);
}
