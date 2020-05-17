#![feature(plugin_registrar)]
#![feature(box_syntax, rustc_private, box_patterns, entry_insert, try_trait, associated_type_defaults, type_ascription)]

#[macro_use]
extern crate rustc;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_target;
extern crate syntax;
extern crate syntax_pos;

use rustc::{
    hir,
    lint::{EarlyContext, EarlyLintPassObject, LateContext, LateLintPassObject, LintContext, LintPass},
};
use rustc_driver::plugin::Registry;
use syntax::{
    ast,
    source_map,
    ast::{FnDecl, NodeId},
    visit::FnKind
};
use syntax_pos::Span;


use crate::{
    mir_analyzer::MirAnalyzer,
    refinements_registry::{
        Restricter,
        RestrictionRegistry
    },
    restriction_extractor::extract_restrictions
};

mod z3_interface;
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
mod restriction_extractor;
mod to_smt;
mod smt_ctx;

mod typable;
declare_lint!(LIQUID_RUST_LINT, Deny, "Liquid rust");

struct EarlyPass;

struct LatePass {
    refinement_registry: Restricter,
}

impl LintPass for LatePass {
    fn name(&self) -> &'static str {
        "liquid"
    }
}

impl LintPass for EarlyPass {
    fn name(&self) -> &'static str {
        "liquid"
    }
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
            println!("Early pass, local: {:?}: {:?}({:?})", loc.pat, loc.ty, loc.ty.as_ref().map(|t| &t.kind));
        }
    }
}

impl<'a, 'tcx> rustc::lint::LateLintPass<'a, 'tcx> for LatePass {
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
                let (restrictions, mir) = extract_restrictions(cx.tcx, def_id);
                self.refinement_registry.add(def_id, restrictions);
                let mir = match mir {
                    Ok(mir) => mir,
                    Err(e) => {
                        return cx.span_lint(LIQUID_RUST_LINT, span, &e.to_string());
                    },
                };
                println!("Late pass, fn: name: {:?},\nattrs: {:?}\n gen params: {:?},\n mir: {:#?}", name, attr, params, mir);
                let mut mir_analyzer = MirAnalyzer::new(
                    def_id,
                    mir,
                    cx.tcx,
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

            }
            _ => {}
        }
    }
}

impl LatePass {
    fn new() -> Self {
        Self { refinement_registry: Default::default() }
    }
}
