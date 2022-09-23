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

#![recursion_limit = "256"]
#![forbid(unsafe_code)]

//! This crate provides automatic graph derivations.
//!
//! In order to automatically implement graph traits for a struct that contains
//! the actual graph data structure in a field, add #[derive(Graph)] to the
//! struct. The field containing the graph must either be named `graph` or be
//! attributed with `#[graph]`. All graph traits (`Graph`, `Digraph`, and
//! `IndexGraph`) that are implemented for the nested graph, are implemented for
//! the annotated struct, too.
//!
//! # Example
//!
//! ```
//! use rs_graph_derive::Graph;
//! use rs_graph::traits::*;
//! use rs_graph::linkedlistgraph::*;
//! use rs_graph::classes;
//!
//! #[derive(Graph)]
//! struct MyGraph {
//!     #[graph] graph: LinkedListGraph, // #[graph] not needed for fields named `graph`.
//!     balances: Vec<f64>,
//!     bounds: Vec<f64>,
//! }
//!
//! impl From<LinkedListGraph> for MyGraph {
//!     fn from(g: LinkedListGraph) -> MyGraph {
//!         let n = g.num_nodes();
//!         let m = g.num_edges();
//!         MyGraph {
//!             graph: g,
//!             balances: vec![0.0; n],
//!             bounds: vec![0.0; m],
//!         }
//!     }
//! }
//!
//! impl MyGraph {
//!     fn balance_mut(&mut self, u: Node) -> &mut f64 {
//!         &mut self.balances[self.graph.node_id(u)]
//!     }
//!
//!     fn bound_mut(&mut self, e: Edge) -> &mut f64 {
//!         &mut self.bounds[self.graph.edge_id(e)]
//!     }
//! }
//!
//! # fn main() {
//! let mut g: MyGraph = classes::path::<LinkedListGraph>(5).into();
//! let (s, t) = (g.id2node(0), g.id2node(4));
//! *g.balance_mut(s) = 1.0;
//! *g.balance_mut(t) = -1.0;
//! for eid in 0..g.num_edges() { *g.bound_mut(g.id2edge(eid)) = eid as f64; }
//! # }
//! ```
//!
//! # Attributed graphs
//!
//! Some algorithms require the presence of specific node or edge attributes.
//! These requirements are represented by `NodeAttributes` and `EdgeAttributes`
//! traits from `rs_graph::attributes`. These traits can also be automatically
//! implemented using `#[derive(Graph)]` given that the wrapped graph is an
//! `IndexGraph`. The node/edge attributes must be collected in indexable arrays
//! (slice, `Vec`, ...) of an appropriate size and be annotated with `nodeattrs`
//! or `edgeattrs` attributes. Note that it is the responsibility of the user to
//! ensure that these vectors have to correct size.
//!
//! # Example
//!
//! ```
//! use rs_graph_derive::Graph;
//! use rs_graph::{traits::*};
//! use rs_graph::linkedlistgraph::*;
//! use rs_graph::classes;
//! use rs_graph::attributes::{NodeAttributes, EdgeAttributes, AttributedGraph};
//!
//! #[derive(Clone, Default)]
//! struct NodeData {
//!     balance: f64,
//! }
//!
//! #[derive(Clone, Default)]
//! struct EdgeData {
//!     bound: f64,
//! }
//!
//! #[derive(Graph)]
//! struct MyGraph {
//!     #[graph] graph: LinkedListGraph,
//!     #[nodeattrs(NodeData)] nodedata: Vec<NodeData>,
//!     #[edgeattrs(EdgeData)] edgedata: Vec<EdgeData>,
//! }
//!
//! #[derive(Graph)]
//! struct MyGraph2 {
//!     #[graph] graph: LinkedListGraph,
//!     #[nodeattrs(NodeData)] nodedata: Vec<NodeData>,
//!     #[edgeattrs(EdgeData)] edgedata: Vec<EdgeData>,
//! }
//!
//! impl From<LinkedListGraph> for MyGraph {
//!     fn from(g: LinkedListGraph) -> MyGraph {
//!         let n = g.num_nodes();
//!         let m = g.num_edges();
//!         MyGraph {
//!             graph: g,
//!             nodedata: vec![Default::default(); n],
//!             edgedata: vec![Default::default(); m],
//!         }
//!     }
//! }
//!
//! # fn main() {
//! let mut g: MyGraph = classes::peterson::<LinkedListGraph>().into();
//! let (s, t) = (g.id2node(0), g.id2node(4));
//! g.node_mut(s).balance = 1.0;
//! g.node_mut(t).balance = -1.0;
//! for eid in 0..g.num_edges() { g.edge_mut(g.id2edge(eid)).bound = eid as f64; }
//!
//! {
//!     let (g, mut attrs) = g.split();
//!     // this would also work: let (g, mut attrs) = attrs.split();
//!     for u in g.nodes() {
//!         for (e, v) in g.outedges(u) {
//!             attrs.node_mut(v).balance = 42.0 + g.node_id(v) as f64;
//!         }
//!     }
//! }
//! for u in g.nodes() {
//!     assert_eq!(g.node(u).balance, 42.0 + g.node_id(u) as f64);
//! }
//! # }
//! ```
//!

extern crate proc_macro;
use proc_macro2;
use quote::quote;
use syn::{self, parse_quote};

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro2::TokenStream as TokenStream2;

fn get_attr_var(field: &syn::Field, index: usize, attrname: &str) -> Option<(syn::Ident, syn::Path)> {
    for attr in field.attrs.iter() {
        if attr.path.is_ident(attrname) {
            return Some((
                field
                    .ident
                    .clone()
                    .unwrap_or_else(|| syn::Ident::new(&format!("{}", index), Span::call_site())),
                match attr
                    .parse_meta()
                    .unwrap_or_else(|_| panic!("Missing `{}` type", attrname))
                {
                    syn::Meta::List(list) => {
                        assert_eq!(
                            list.nested.len(),
                            1,
                            "expected exactly one type argument for `{}`",
                            attrname
                        );
                        if let Some(syn::NestedMeta::Meta(syn::Meta::Path(id))) = list.nested.iter().next() {
                            id.clone()
                        } else {
                            panic!("expected exactly one type argument for `{}`", attrname);
                        }
                    }
                    _ => panic!("expected exactly one type argument for `{}`", attrname),
                },
            ));
        }
    }

    None
}

#[proc_macro_derive(Graph, attributes(graph, nodeattrs, edgeattrs))]
pub fn graph(input: TokenStream) -> TokenStream {
    let input: TokenStream2 = input.into();
    let mut ast: syn::DeriveInput = syn::parse2(input).unwrap();
    let vis = &ast.vis;
    let name = &ast.ident;
    let generics = &mut ast.generics;

    let mut have_graph_attr = false;
    let mut var = None;
    let mut typ = None;

    let mut nodeattrs = None;
    let mut edgeattrs = None;

    // Collect all fields with attribute #[graph] or named `graph`.
    if let syn::Data::Struct(syn::DataStruct { ref fields, .. }) = ast.data {
        for (i, ref field) in fields.iter().enumerate() {
            if let Some(attrvar) = get_attr_var(field, i, "nodeattrs") {
                if nodeattrs.is_some() {
                    panic!("Only one field can be tagged `nodeattrs`");
                }
                nodeattrs = Some(attrvar);
            }

            if let Some(attrvar) = get_attr_var(field, i, "edgeattrs") {
                if edgeattrs.is_some() {
                    panic!("Only one field can be tagged `edgeattrs`");
                }
                edgeattrs = Some(attrvar);
            }

            if field.attrs.iter().any(|attr| attr.path.is_ident("graph")) {
                if have_graph_attr {
                    panic!("Only one field can be tagged `graph`");
                }
                have_graph_attr = true;
            } else if field.ident.as_ref().map(|s| s == "graph").unwrap_or(false) {
                if have_graph_attr {
                    continue;
                }
            } else {
                continue;
            }
            var = Some(
                field
                    .ident
                    .clone()
                    .unwrap_or_else(|| syn::Ident::new(&format!("{}", i), Span::call_site())),
            );
            typ = Some(&field.ty);
        }
    }

    if var.is_none() {
        panic!("No field `graph` or field with attribute #[graph] found");
    }

    // Implement all graph traits the nested graph implements.

    let ident_it = syn::Ident::new("__rs_graph_I__", Span::call_site());
    let ident_lt = syn::Lifetime::new("'__rs_graph_z__", Span::call_site());
    let ty_generics = generics.clone();
    let mut it_generics = generics.clone();
    it_generics
        .params
        .push(syn::GenericParam::Type(ident_it.clone().into()));
    generics
        .params
        .push(syn::GenericParam::Lifetime(syn::LifetimeDef::new(ident_lt.clone())));

    let gens = [
        "GraphType",
        "FiniteGraph",
        "FiniteDigraph",
        "Undirected",
        "Directed",
        "IndexGraph",
    ]
    .iter()
    .map(|name| {
        let name = syn::Ident::new(name, Span::call_site());
        let mut g = generics.clone();
        g.make_where_clause()
            .predicates
            .push(parse_quote!(#typ: ::rs_graph::traits::#name<#ident_lt>));
        g
    })
    .collect::<Vec<_>>();

    let (basegraph_impl, _, basegraph_where) = gens[0].split_for_impl();
    let (finitegraph_impl, _, finitegraph_where) = gens[1].split_for_impl();
    let (finitedigraph_impl, _, finitedigraph_where) = gens[2].split_for_impl();
    let (undirected_impl, _, undirected_where) = gens[3].split_for_impl();
    let (directed_impl, _, directed_where) = gens[4].split_for_impl();
    let (indexgraph_impl, _, indexgraph_where) = gens[5].split_for_impl();

    let mut expanded = quote! {
        impl #it_generics ::rs_graph::traits::GraphIterator<#name #ty_generics> for WrapIt<#ident_it> where #ident_it: GraphIterator<#typ> {
            type Item = #ident_it :: Item;

            fn next(&mut self, g: &#name #ty_generics) -> Option<Self::Item> {
                self.0.next(&g.#var)
            }
        }

        impl #basegraph_impl ::rs_graph::traits::GraphType<#ident_lt> for #name #ty_generics #basegraph_where
        {
            type Node = <#typ as ::rs_graph::traits::GraphType<#ident_lt>>::Node;

            type Edge = <#typ as ::rs_graph::traits::GraphType<#ident_lt>>::Edge;
        }

        impl #finitegraph_impl ::rs_graph::traits::FiniteGraph<#ident_lt> for #name #ty_generics #finitegraph_where
        {
            type NodeIt = ::rs_graph::traits::WrapIt<<#typ as ::rs_graph::traits::FiniteGraph<#ident_lt>>::NodeIt>;

            type EdgeIt = ::rs_graph::traits::WrapIt<<#typ as ::rs_graph::traits::FiniteGraph<#ident_lt>>::EdgeIt>;

            fn num_nodes(&self) -> usize {
                self.#var.num_nodes()
            }

            fn num_edges(&self) -> usize {
                self.#var.num_edges()
            }

            fn nodes_iter(&#ident_lt self) -> Self::NodeIt {
                ::rs_graph::traits::WrapIt(self.#var.nodes_iter())
            }

            fn edges_iter(&#ident_lt self) -> Self::EdgeIt {
                ::rs_graph::traits::WrapIt(self.#var.edges_iter())
            }

            fn enodes(&#ident_lt self, e: Self::Edge) -> (Self::Node, Self::Node) {
                self.#var.enodes(e)
            }
        }

        impl #finitedigraph_impl ::rs_graph::traits::FiniteDigraph<#ident_lt> for #name #ty_generics #finitedigraph_where
        {
            fn src(&#ident_lt self, e: Self::Edge) -> Self::Node {
                self.#var.src(e)
            }

            fn snk(&#ident_lt self, e: Self::Edge) -> Self::Node {
                self.#var.snk(e)
            }
        }

        impl #undirected_impl ::rs_graph::traits::Undirected<#ident_lt> for #name #ty_generics #undirected_where
        {
            type NeighIt = ::rs_graph::traits::WrapIt<<#typ as ::rs_graph::traits::Undirected<#ident_lt>>::NeighIt>;

            fn neigh_iter(&#ident_lt self, u: Self::Node) -> Self::NeighIt {
                ::rs_graph::traits::WrapIt(self.#var.neigh_iter(u))
            }
        }

        impl #directed_impl ::rs_graph::traits::Directed<#ident_lt> for #name #ty_generics #directed_where
        {
            type OutIt= ::rs_graph::traits::WrapIt<<#typ as ::rs_graph::traits::Directed<#ident_lt>>::OutIt>;

            type InIt = ::rs_graph::traits::WrapIt<<#typ as ::rs_graph::traits::Directed<#ident_lt>>::InIt>;

            type IncidentIt = ::rs_graph::traits::WrapIt<<#typ as ::rs_graph::traits::Directed<#ident_lt>>::IncidentIt>;

            type DirectedEdge = <#typ as ::rs_graph::traits::Directed<#ident_lt>>::DirectedEdge;

            fn out_iter(&#ident_lt self, u: Self::Node) -> Self::OutIt {
                ::rs_graph::traits::WrapIt(self.#var.out_iter(u))
            }

            fn in_iter(&#ident_lt self, u: Self::Node) -> Self::InIt {
                ::rs_graph::traits::WrapIt(self.#var.in_iter(u))
            }

            fn incident_iter(&#ident_lt self, u: Self::Node) -> Self::IncidentIt {
                ::rs_graph::traits::WrapIt(self.#var.incident_iter(u))
            }
        }

        impl #indexgraph_impl ::rs_graph::traits::IndexGraph<#ident_lt> for #name #ty_generics #indexgraph_where
        {
            fn node_id(&self, u: Self::Node) -> usize {
                self.#var.node_id(u)
            }

            fn id2node(&#ident_lt self, id: usize) -> Self::Node {
                self.#var.id2node(id)
            }

            fn edge_id(&self, e: Self::Edge) -> usize {
                self.#var.edge_id(e)
            }

            fn id2edge(&#ident_lt self, id: usize) -> Self::Edge {
                self.#var.id2edge(id)
            }
        }
    };

    let mut attrdefs = TokenStream2::new();
    let mut attrsets = TokenStream2::new();
    let mut attrsets2 = TokenStream2::new();
    if let Some((attrvar, attrtyp)) = nodeattrs.as_ref() {
        expanded.extend(quote! {
            impl #indexgraph_impl ::rs_graph::attributes::NodeAttributes<#ident_lt, #typ, #attrtyp> for #name #ty_generics #indexgraph_where
            {
                fn node(&self, u: <#typ as ::rs_graph::traits::GraphType<#ident_lt>>::Node) -> &#attrtyp {
                    &self.#attrvar[self.#var.node_id(u)]
                }

                fn node_mut(&mut self, u: <#typ as ::rs_graph::traits::GraphType<#ident_lt>>::Node) -> &mut #attrtyp {
                    &mut self.#attrvar[self.#var.node_id(u)]
                }
            }
        });
        attrdefs.extend(quote!(nodeattrs: &#ident_lt mut [#attrtyp],));
        attrsets.extend(quote!(nodeattrs: &mut self.#attrvar,));
        attrsets2.extend(quote!(nodeattrs: self.nodeattrs,));
    }

    if let Some((attrvar, attrtyp)) = edgeattrs.as_ref() {
        expanded.extend(quote! {
            impl #indexgraph_impl ::rs_graph::attributes::EdgeAttributes<#ident_lt, #typ, #attrtyp> for #name #ty_generics #indexgraph_where
            {
                fn edge(&self, u: <#typ as ::rs_graph::traits::GraphType<#ident_lt>>::Edge) -> &#attrtyp {
                    &self.#attrvar[self.#var.edge_id(u)]
                }

                fn edge_mut(&mut self, u: <#typ as ::rs_graph::traits::GraphType<#ident_lt>>::Edge) -> &mut #attrtyp {
                    &mut self.#attrvar[self.#var.edge_id(u)]
                }
            }
        });
        attrdefs.extend(quote!(edgeattrs: &#ident_lt mut [#attrtyp],));
        attrsets.extend(quote!(edgeattrs: &mut self.#attrvar,));
        attrsets2.extend(quote!(edgeattrs: self.edgeattrs,));
    }

    if !attrdefs.is_empty() {
        let (_, orig_ty_generics, orig_where) = ty_generics.split_for_impl();
        let attrstruct = syn::Ident::new(&format!("{}_Attributes", name), Span::call_site());
        expanded.extend(quote! {
            #vis struct #attrstruct<#ident_lt> {
                graph: &#ident_lt #typ,
                #attrdefs
            }

            impl #basegraph_impl ::rs_graph::attributes::AttributedGraph<#ident_lt> for #name #orig_ty_generics #orig_where {
                type Graph = #typ;
                type Attributes = #attrstruct<#ident_lt>;
                fn split<'b>(&'b mut self) -> (&'b #typ, #attrstruct<'b>) {
                        (
                            &self.#var,
                            #attrstruct {
                                graph: &self.#var,
                                #attrsets
                            },
                        )
                }
            }

            impl<#ident_lt> ::rs_graph::attributes::AttributedGraph<#ident_lt> for #attrstruct<#ident_lt> {
                type Graph = #typ;
                type Attributes = #attrstruct<#ident_lt>;
                fn split<'b>(&'b mut self) -> (&'b #typ, #attrstruct<'b>) {
                    (self.graph, #attrstruct {
                        graph: self.graph,
                        #attrsets2
                    })
                }
            }
        });

        if let Some((_, attrtyp)) = nodeattrs.as_ref() {
            expanded.extend(quote! {
                impl #indexgraph_impl ::rs_graph::attributes::NodeAttributes<#ident_lt, #typ, #attrtyp> for #attrstruct<#ident_lt> #ty_generics #indexgraph_where
                {
                    fn node(&self, u: <#typ as ::rs_graph::traits::GraphType<#ident_lt>>::Node) -> &#attrtyp {
                        &self.nodeattrs[self.#var.node_id(u)]
                    }

                    fn node_mut(&mut self, u: <#typ as ::rs_graph::traits::GraphType<#ident_lt>>::Node) -> &mut #attrtyp {
                        &mut self.nodeattrs[self.#var.node_id(u)]
                    }
                }
            });
        }

        if let Some((_, attrtyp)) = edgeattrs.as_ref() {
            expanded.extend(quote! {
                impl #indexgraph_impl ::rs_graph::attributes::EdgeAttributes<#ident_lt, #typ, #attrtyp> for #attrstruct<#ident_lt> #ty_generics #indexgraph_where
                {
                    fn edge(&self, u: <#typ as ::rs_graph::traits::GraphType<#ident_lt>>::Edge) -> &#attrtyp {
                        &self.edgeattrs[self.#var.edge_id(u)]
                    }

                    fn edge_mut(&mut self, u: <#typ as ::rs_graph::traits::GraphType<#ident_lt>>::Edge) -> &mut #attrtyp {
                        &mut self.edgeattrs[self.#var.edge_id(u)]
                    }
                }
            });
        }
    }

    expanded.into()
}
