// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementation of the loop contracts code generation.
//!

use proc_macro::TokenStream;
use proc_macro_error2::abort_call_site;
use quote::{format_ident, quote};
use syn::spanned::Spanned;
use syn::token::AndAnd;
use syn::{BinOp, Expr, ExprBinary, Stmt, LocalInit, PatIdent, parse_quote, Local, Pat};
use proc_macro2::{Ident, Span, TokenStream as TokenStream2};
use super::contracts::helpers::{chunks_by, is_token_stream_2_comma, matches_path};

/// Expand loop contracts macros.
///
/// A while loop of the form
/// ``` rust
///  while guard {
///      body
///  }
/// ```
/// will be annotated as
/// ``` rust
/// #[inline(never)]
/// #[kanitool::fn_marker = "kani_register_loop_contract"]
/// const fn kani_register_loop_contract_id<T, F: FnOnce() -> T>(f: F) -> T {
///     unreachable!()
/// }
///  while kani_register_loop_contract_id(|| -> bool {inv};) && guard {
///      body
///  }
/// ```
pub fn loop_invariant(attr: TokenStream, item: TokenStream) -> TokenStream {
    // parse the stmt of the loop
    let mut loop_stmt: Stmt = syn::parse(item.clone()).unwrap();

    // name of the loop invariant as closure of the form
    // __kani_loop_invariant_#startline_#startcol_#endline_#endcol
    let mut inv_name: String = "__kani_loop_invariant".to_owned();
    let loop_id = generate_unique_id_from_span(&loop_stmt);
    inv_name.push_str(&loop_id);

    // expr of the loop invariant
    let inv_expr: Expr = syn::parse(attr).unwrap();

    // ident of the register function
    let mut register_name: String = "kani_register_loop_contract".to_owned();
    register_name.push_str(&loop_id);
    let register_ident = format_ident!("{}", register_name);

    match loop_stmt {
        Stmt::Expr(ref mut e, _) => match e {
            Expr::While(ref mut ew) => {
                let new_cond: Expr = syn::parse(
                    quote!(
                        #register_ident(&||->bool{#inv_expr}, 0))
                    .into(),
                )
                .unwrap();
                *(ew.cond) = Expr::Binary(ExprBinary {
                    attrs: Vec::new(),
                    left: Box::new(new_cond),
                    op: BinOp::And(AndAnd::default()),
                    right: ew.cond.clone(),
                });
            }
            _ => {
                abort_call_site!("`#[kani::loop_invariant]` is now only supported for while-loops.";
                    note = "for now, loop contracts is only supported for while-loops.";
                )
            }
        },
        _ => abort_call_site!("`#[kani::loop_invariant]` is now only supported for while-loops.";
            note = "for now, loop contracts is only supported for while-loops.";
        ),
    }
    let t = quote!(
        {
        // Dummy function used to force the compiler to capture the environment.
        // We cannot call closures inside constant functions.
        // This function gets replaced by `kani::internal::call_closure`.
        #[inline(never)]
        #[kanitool::fn_marker = "kani_register_loop_contract"]
        const fn #register_ident<F: Fn() -> bool>(_f: &F, _transformed: usize) -> bool {
            true
        }
        #loop_stmt});
    println!("{}", t.to_string());    
    t.into()
}

fn generate_unique_id_from_span(stmt: &Stmt) -> String {
    // Extract the span of the expression
    let span = stmt.span().unwrap();

    // Get the start and end line and column numbers
    let start = span.start();
    let end = span.end();

    // Create a tuple of location information (file path, start line, start column, end line, end column)
    format!("_{:?}_{:?}_{:?}_{:?}", start.line(), start.column(), end.line(), end.column())
}

const WRAPPER_ARG: &str = "_loop_wrapper_arg";
const CLOSURE_ARG: &str = "_kani_loop_assign_closure";
pub fn loop_assign(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr : Vec<Expr> = chunks_by(TokenStream2::from(attr), is_token_stream_2_comma)
        .map(syn::parse2)
        .filter_map(|expr| match expr {
            Err(e) => {
                None
            }
            Ok(expr) => Some(expr),
        })
        .collect();
    let wrapper_arg_ident = Ident::new(WRAPPER_ARG, Span::call_site());
    let closure_ident = Ident::new(CLOSURE_ARG, Span::call_site());
    let mut loop_stmt: Stmt = syn::parse(item.clone()).unwrap();
    let (mut loop_body, loop_guard) = match loop_stmt {
        Stmt::Expr(ref mut e, _) => match e {
            Expr::While(ew) => (ew.body.clone(), ew.cond.clone()),
            _ => panic!(),
        },
        _ => panic!(),
    };
    let body_stmts = loop_body.stmts.clone();
    let closure_args = attr.iter().map (|e| {let i : Expr = parse_quote!(#e as * const _); i});

    let mut closure_stmts : Vec<Stmt> = parse_quote!(
        let #wrapper_arg_ident = (#(#closure_args),*);
        let mut #closure_ident = |i|{};
        #closure_ident(#wrapper_arg_ident);
    );
    closure_stmts.extend(body_stmts);

    match loop_stmt {
        Stmt::Expr(ref mut e, _) => match e {
            Expr::While(ew) => ew.body.stmts = closure_stmts.clone(),
            _ => panic!(),
        },
        _ => panic!(),
    };
    let t = quote! (#loop_stmt);
    //let t = quote! ({#wrapper_assign; #closure_def;});
    println!("{}", t.to_string());
    assert!(1==0);
    //quote!({#(#body_stmts)*})     (#(#attr)*)     
    t.into()
    //item
}
