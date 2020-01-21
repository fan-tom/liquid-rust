#![feature(plugin_registrar)]
#![feature(box_syntax, rustc_private, box_patterns, entry_insert)]
//#![feature(plugin)]
//#![plugin(peg_syntax_ext)]

#[macro_use]
extern crate rustc;
extern crate rustc_data_structures;
//extern crate rustc_plugin;
//extern crate rustc_plugin_impl;
extern crate rustc_driver;
extern crate rustc_target;
extern crate syntax;
extern crate syntax_pos;


use std::{
    collections::{HashMap, HashSet},
    convert::identity
};

use failure::Error;
use itertools::*;
//use pest::Parser;
use rustc::{
    hir,
    lint::{EarlyContext, EarlyLintPassObject, LateContext, LateLintPassObject, LintArray, LintContext, LintPass},
    mir::{
        HasLocalDecls,
        LocalDecl,
        visit::Visitor
    },
    ty::{
        DefIdTree,
        Instance,
        layout::MaybeResult
    }
};
use rustc_data_structures::sync::Once;
use rustc_driver::plugin::Registry;
use syntax::{
    ast::{
        self,
        Attribute,
        Ident,
        Name,
        Path
    },
    source_map,
    print::pprust
};
use syntax_pos::Span;

use rustpeg_parser::RestrictionParser;

use crate::{
    mir_analyzer::MirAnalyzer,
    restriction_expr::Expr,
    refinements_registry::Restricter,
    visitor::Visitable,
};
use crate::refinements_registry::{RestrictionRegistry, FunctionRestrictions};

//use parser::Rule;

//use rustproof::MirData;


mod z3_interface;
//mod parser;
mod refined_type;
mod rustpeg_parser;
mod mir_analyzer;
mod expr;
mod restriction_expr;
mod refinements_registry;
mod visitor;
mod restriction_converter;
mod inference_ctx;
mod refinable_entity;
mod name_registry;
mod folder;
mod utils;
mod error;

declare_lint!(LIQUID_RUST_LINT, Deny, "Liquid rust");

struct EarlyPass;

struct LatePass {
    z3_ctx: z3::Context,
    refinement_registry: Restricter,
}

impl LintPass for LatePass {
    fn name(&self) -> &'static str {
        "liquid"
    }

//    fn get_lints(&self) -> LintArray {
//        lint_array!(LIQUID_RUST_LINT) // We'll get to this later, kind of...
//    }
}

impl LintPass for EarlyPass {
    fn name(&self) -> &'static str {
        "liquid"
    }

//    fn get_lints(&self) -> LintArray {
//        lint_array!() // We'll definitely get to this later!
//    }
}

#[plugin_registrar]
pub fn register_plugins(reg: &mut Registry) {
    reg.lint_store.register_early_pass(|| box EarlyPass as EarlyLintPassObject);
    reg.lint_store.register_late_pass(|| box LatePass::new() as LateLintPassObject);
}

impl rustc::lint::EarlyLintPass for EarlyPass {
    fn check_expr(&mut self, cx: &EarlyContext, expr: &ast::Expr) {
        if let ast::ExprKind::Type(lhs, rhs) = &expr.kind {
            println!("Early pass, type: {:?}: {:?}", lhs, rhs);
        }
    }

    fn check_stmt(&mut self, cx: &EarlyContext, stmt: &ast::Stmt) {
        if let ast::StmtKind::Local(loc) = &stmt.kind {
            if let Some(ty) = &loc.ty {
//                ty.
//                let ty_attrs = ty.attrs();
//                let refinements = attrs_to_refinements(ty_attrs)
            }
            println!("Early pass, local: {:?}: {:?}({:?})", loc.pat, loc.ty, loc.ty.as_ref().map(|t| &t.kind));
        }
    }
}

impl<'a, 'tcx> rustc::lint::LateLintPass<'a, 'tcx> for LatePass {
    fn check_body(&mut self, cx: &LateContext<'a, 'tcx>, body: &hir::Body) {

//        let mir = cx.tcx.instance_mir()
//        println!("Late pass, body: {:?}", body);
    }

    /*    fn check_attribute(&mut self, cx: &LateContext<'a, 'tcx>, attr: &'tcx ast::Attribute) {
            println!("Late pass, attribute: {:?}", attr)
        }*/


    fn check_stmt(&mut self, cx: &LateContext<'a, 'tcx>, stmt: &'tcx hir::Stmt) {
        if let hir::StmtKind::Local(loc) = &stmt.kind {
            // no need to check definition without init
            // but we must check actual init point somewhere else
//            println!("Late pass, local: {:?}: {:?}({:?})", loc.pat, loc.ty, loc.ty.as_ref().map(|t| &t.node));
            if let Some(init) = &loc.init {
                if let hir::ExprKind::Lit(source_map::Spanned { node: ast::LitKind::Int(lit_value, _), .. }) = init.kind {
                    let attrs = if let Some(ty) = &loc.ty {
                        if let hir::TyKind::Path(hir::QPath::Resolved(_, path)) = &ty.kind {
                            if let hir::def::Res::Def(hir::def::DefKind::TyAlias, def_id) = path.res {
                                let map = cx.tcx.hir();
                                map.as_local_hir_id(def_id)
                                    .map(|nid| {
                                        let attrs = map.attrs(nid);
                                        let base_ty = map.find(nid).unwrap();
//                                        if let hir::Node
//                                        println!("Late pass, ty alias base type: {:?}", base_ty);
//                                        println!("Late pass, attrs: {:?}", attrs);
                                        attrs
                                    })
                            } else {
                                return;
                            }
                        } else {
                            return;
                        }
                    } else {
                        return;
                    };
                    if let Some(attrs) = attrs {
                        for attr in attrs {
                            let attr_inner = &attr.tokens;
                            let attr_str =

                                cx.sess().source_map().span_to_snippet(attr.span).unwrap();
//                            println!("Late pass, attr str: {}", attr_str);
                        }
//                        self.attr_to_z3_ast(&attr_str, )
                    }
                }
            }
        } else {
//            println!("Late pass, stmt: {:?}", stmt);
        }
    }

    fn check_pat(&mut self, cx: &LateContext<'a, 'tcx>, pat: &'tcx hir::Pat) {
        println!("Late pass, pattern: {:?}", pat.kind)
    }

    fn check_expr(&mut self, cx: &LateContext<'a, 'tcx>, expr: &'tcx hir::Expr) {
        use hir::ExprKind::*;
        match &expr.kind {
            Assign(lhs, rhs) => {
                let lhs_ty = cx.tables.expr_ty(&lhs);
                let rhs_ty = cx.tables.expr_ty(&rhs);
//                println!("Late pass, assign: {:?} of type {:?} to {:?} of type {:?}",
//                         rhs,
//                         rhs_ty,
//                         lhs,
//                         lhs_ty);
            }
            _ => println!("Late pass, expr: {:?}", expr)
        }
    }

    fn check_ty(&mut self, _: &LateContext, ty: &hir::Ty) {
        println!("Late pass, ty: {:?}", ty)
    }

    fn check_fn(&mut self, cx: &LateContext<'a, 'tcx>, fn_kind: hir::intravisit::FnKind<'tcx>,
                fn_decl: &'tcx hir::FnDecl, body: &'tcx hir::Body, span: Span, hir_id: hir::HirId) {
        use hir::intravisit::FnKind;

        match fn_kind {
            // simple non-generic function
            FnKind::ItemFn(syntax_pos::symbol::Ident { name, .. },
                           hir::Generics { params, .. },
                           header,
                           vis,
                           attr) if params.len() == 0 => {
                let def_id = cx.tcx.hir().local_def_id(hir_id);
                let (requires, ensures): (Vec<_>, Vec<_>) = cx.tcx.get_attrs(def_id)
                    .iter()
                    .filter_map(|attr| {
                        let parsed = || {
                            let input = pprust::tts_to_string(attr.tokens.clone());
                            println!("Parsing attribute {}({:?})", input, attr);
                            RestrictionParser::parse(&input)
                                .map(|v| v.into_iter().map(|(a, e)| (a.to_string(), e)).collect::<Vec<_>>())
                                .map_err(|e| cx.span_lint(LIQUID_RUST_LINT, attr.span, &e.to_string()))
                        };
                        match &*attr.path.segments[0].ident.as_str() {
                            "requires" => Some(Either::Left(parsed())),
                            "ensures" => Some(Either::Right(parsed())),
                            _ => None
                        }
                    }
                    )
                    .partition_map(identity);

                println!("Raw requirements: {:?}", requires);

                let (requires, ensures) = if let (Ok::<_, ()>(r), Ok::<_, ()>(e)) = (requires
                                               .into_iter()
                                               .try_fold(HashMap::new(), |mut hm: HashMap<_, _>, r| {
                                                   hm.extend(r?);
                                                   Ok(hm)
                                               }),
                                           ensures
                                               .into_iter()
                                               .try_fold(HashMap::new(), |mut hm: HashMap<_, _>, r| {
                                                   hm.extend(r?);
                                                   Ok(hm)
                                               }),
                ) {
                    println!("Requirements: {:?}", r);
                    (r, e)
                } else {
                    println!("Found errors in specs, exit");
                    return
                };
                let mir = cx.tcx.instance_mir(Instance::mono(cx.tcx, def_id).def);
                let function_arguments_names = mir
                    .args_iter()
                    .filter_map(|i| Some(mir.local_decls[i].name?.as_str().to_string()))
                    .collect::<Vec<_>>();
                if let Err(e) = self.check_requires_wf(&function_arguments_names, &requires) {
                    println!("Error in requirements");
                    cx.span_lint(LIQUID_RUST_LINT, span,
                                 &e.into_iter()
                                     .map(|(a, u)| format!("unknown variables in predicate over {}: {}", a, u.into_iter().join(", ")))
                                     .join(", ")
                    )
                }
//                self.check_ensures_wf(function_arguments_names, ensures).unwrap();
                self.refinement_registry.add(def_id, FunctionRestrictions::new(requires, ensures.get("result").cloned()));
                let mut mir_analyzer = MirAnalyzer::new(
                    def_id,
                    mir,
                    cx.tcx,
                    Default::default(),
                    Default::default(),
                    Default::default(),
                    &mut self.refinement_registry
                ).unwrap();
                match mir_analyzer.check() {
                    Ok(res) => if !res {
                        for err in mir_analyzer.errors() {
                            if let Some(span) = err.span {
//                                cx.span_lint_help(LIQUID_RUST_LINT, span, &err.description, "This is help")
//                                cx.span_lint_note(LIQUID_RUST_LINT, span, &err.description, span, "This is note")
                                cx.span_lint(LIQUID_RUST_LINT, span, &err.description)
                            } else {
                                cx.lint(LIQUID_RUST_LINT, &err.description)
                            }
                        }
                    }
                    Err(err) => {
                        panic!("Error while mir check: {}", err)
                    }
                }

                println!("Late pass, fn: name: {:?},\nattrs: {:?}\n gen params: {:?},\n mir: {:#?}", name, attr, params, mir);
            }
            _ => {}
        }
    }
}

impl LatePass {
    fn new() -> Self {
        Self {
            z3_ctx: z3::Context::new(&z3::Config::new()),
            refinement_registry: Default::default(),
        }
    }


    fn check_function_call(&self) -> Result<(), ()> {
        Ok(())
    }

    /// foo.bar();
    fn check_method_call(&self) -> Result<(), ()> {
        Ok(())
    }

    /// x = y;
    fn check_variable_assign(&self) -> Result<(), ()> {
        Ok(())
    }

    /// let x[: Foo] [= bar];
    fn check_binding(&self) -> Result<(), ()> {
        Ok(())
    }

    /// (x: Foo + y)
    fn check_type_ascription(&self) -> Result<(), ()> {
        Ok(())
    }

    fn attr_to_z3_ast(&mut self, attr: &str, base_type: hir::Ty) -> Result<(), Error> {
//        unimplemented!()
        let restriction = RestrictionParser::parse(attr)?;
        println!("attr parsed: {:?}", restriction);
//        let tokens = attrs.span.;

//        for token in tokens {
//
//        }
        Ok(())
    }

    fn check_requires_wf<'e>(&self, function_arguments_names: &[impl AsRef<str>], requires: impl IntoIterator<Item=(&'e String, &'e Expr)>) -> Result<(), HashMap<&'e str, HashSet<&'e str>>> {
        let mut unknown_vars = HashMap::<_, HashSet<_>>::new();
        requires
            .into_iter()
            .for_each(|(arg, expr)| {
                println!("Checking requirement {}", expr);
                expr.accept(&mut |e: &'e Expr| {
                    println!("Visiting expr {}", e);
                    if let Expr::Var(ref s) = e {
                        println!("Checking var {} in requirement", s);
                        if s != arg && !function_arguments_names
                            .iter()
                            .take_while(|a| a.as_ref() != arg)
                            .any(|a| a.as_ref() == s.as_str()) {
                            unknown_vars
                                .entry(arg.as_str())
                                .or_default()
                                .insert(s.as_str());
                        }
                    }
                });
            });
        println!("End checking requirements, unknown vars: {:?}", unknown_vars);
        if unknown_vars.is_empty() {
            Ok(())
        } else {
            Err(unknown_vars)
        }
    }
//    fn check_restriction_wellformedness(&self, args: & [], restriction: & [Expr])
}
