#![feature(plugin_registrar)]
#![feature(box_syntax, rustc_private, box_patterns)]

#[macro_use]
extern crate rustc;
extern crate rustc_data_structures;
extern crate rustc_plugin;
extern crate syntax;
extern crate syntax_pos;

use failure::Error;
use pest::Parser;
use rustc::hir;
use rustc::lint::{EarlyContext, EarlyLintPassObject, LateContext, LateLintPassObject, LintArray, LintContext, LintPass};
use rustc::mir::{HasLocalDecls, LocalDecl};
use rustc::mir::visit::Visitor;
use rustc::ty::{DefIdTree, Instance};
use rustc_plugin::Registry;
use syntax::ast;
use syntax::source_map;
use syntax_pos::Span;

use parser::Rule;

use crate::mir_analyzer::MirAnalyzer;

//use rustproof::MirData;


mod z3_interface;
mod parser;
mod refined_type;
mod mir_analyzer;
mod expr;

struct EarlyPass;

struct LatePass {
    z3_ctx: z3::Context,
}

impl LintPass for LatePass {
    fn name(&self) -> &'static str {
        "liquid"
    }

    fn get_lints(&self) -> LintArray {
        lint_array!() // We'll get to this later, kind of...
    }
}

impl LintPass for EarlyPass {
    fn name(&self) -> &'static str {
        "liquid"
    }

    fn get_lints(&self) -> LintArray {
        lint_array!() // We'll definitely get to this later!
    }
}

#[plugin_registrar]
pub fn register_plugins(reg: &mut Registry) {
    reg.register_early_lint_pass(box EarlyPass as EarlyLintPassObject);
    reg.register_late_lint_pass(box LatePass::new() as LateLintPassObject);
}

impl rustc::lint::EarlyLintPass for EarlyPass {
    fn check_expr(&mut self, cx: &EarlyContext, expr: &ast::Expr) {
        if let ast::ExprKind::Type(lhs, rhs) = &expr.node {
            println!("Early pass, type: {:?}: {:?}", lhs, rhs);
        }
    }

    fn check_stmt(&mut self, cx: &EarlyContext, stmt: &ast::Stmt) {
        if let ast::StmtKind::Local(loc) = &stmt.node {
            if let Some(ty) = &loc.ty {
//                ty.
//                let ty_attrs = ty.attrs();
//                let refinements = attrs_to_refinements(ty_attrs)
            }
            println!("Early pass, local: {:?}: {:?}({:?})", loc.pat, loc.ty, loc.ty.as_ref().map(|t| &t.node));
        }
    }
}

impl<'a, 'tcx> rustc::lint::LateLintPass<'a, 'tcx> for LatePass {
    fn check_body(&mut self, cx: &LateContext<'a, 'tcx>, body: &hir::Body) {

//        let mir = cx.tcx.instance_mir()
        println!("Late pass, body: {:?}", body);
    }

    /*    fn check_attribute(&mut self, cx: &LateContext<'a, 'tcx>, attr: &'tcx ast::Attribute) {
            println!("Late pass, attribute: {:?}", attr)
        }*/


    fn check_stmt(&mut self, cx: &LateContext<'a, 'tcx>, stmt: &'tcx hir::Stmt) {
        if let hir::StmtKind::Local(loc) = &stmt.node {
            // no need to check definition without init
            // but we must check actual init point somewhere else
            println!("Late pass, local: {:?}: {:?}({:?})", loc.pat, loc.ty, loc.ty.as_ref().map(|t| &t.node));
            if let Some(init) = &loc.init {
                if let hir::ExprKind::Lit(source_map::Spanned { node: ast::LitKind::Int(lit_value, _), .. }) = init.node {
                    let attrs = if let Some(ty) = &loc.ty {
                        if let hir::TyKind::Path(hir::QPath::Resolved(_, path)) = &ty.node {
                            if let hir::def::Res::Def(hir::def::DefKind::TyAlias, def_id) = path.res {
                                let map = cx.tcx.hir();
                                map.as_local_node_id(def_id)
                                    .map(|nid| {
                                        let attrs = map.attrs(nid);
                                        let base_ty = map.find(nid).unwrap();
//                                        if let hir::Node
                                        println!("Late pass, ty alias base type: {:?}", base_ty);
                                        println!("Late pass, attrs: {:?}", attrs);
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
                            println!("Late pass, attr str: {}", attr_str);
                        }
//                        self.attr_to_z3_ast(&attr_str, )
                    }
                }
            }
        } else {
            println!("Late pass, stmt: {:?}", stmt);
        }
    }

    fn check_pat(&mut self, cx: &LateContext<'a, 'tcx>, pat: &'tcx hir::Pat) {
        println!("Late pass, pattern: {:?}", pat.node)
    }

    fn check_expr(&mut self, cx: &LateContext<'a, 'tcx>, expr: &'tcx hir::Expr) {
        use hir::ExprKind::*;
        match &expr.node {
            Assign(lhs, rhs) => {
                let lhs_ty = cx.tables.expr_ty(&lhs);
                let rhs_ty = cx.tables.expr_ty(&rhs);
                println!("Late pass, assign: {:?} of type {:?} to {:?} of type {:?}",
                         rhs,
                         rhs_ty,
                         lhs,
                         lhs_ty);
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
                let def_id = cx.tcx.hir().local_def_id_from_hir_id(hir_id);
                let mir = cx.tcx.instance_mir(Instance::mono(cx.tcx, def_id).def);
                let mir_analyzer = MirAnalyzer::new(mir, cx.tcx, Default::default(), Default::default(), Default::default());
                mir_analyzer.check();
                println!("Late pass, fn: name: {:?},\n gen params: {:?},\n mir: {:#?}", name, params, mir);
            }
            _ => {}
        }
    }
}

impl LatePass {
    fn new() -> Self {
        Self {
            z3_ctx: z3::Context::new(&z3::Config::new())
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
        let restriction = parser::RestrictionParser::parse(Rule::restriction, attr)?;
        println!("attr parsed: {}", restriction);
//        let tokens = attrs.span.;

//        for token in tokens {
//
//        }
        Ok(())
    }
}
