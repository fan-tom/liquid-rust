use std::cell::RefCell;
use std::collections::hash_map::RandomState;
use std::collections::HashMap;
use std::fmt;
use std::fmt::Debug;

use derive_more::*;
use failure::format_err;
use itertools::Itertools;
use rustc::hir::def_id::DefId;
use rustc::mir::{BasicBlockData, Body, Constant, HasLocalDecls, Local, LocalDecl, LocalKind, Operand, Place, PlaceBase, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind, UnOp, BasicBlock};
use rustc::ty::{Const as RustConst, Ty, TyKind, TyS, Instance};
use rustc::ty::subst::SubstsRef;
use rustc::ty::TyCtxt;
//use rustc_data_structures::indexed_vec::IndexVec;

use crate::refinements_registry::{FunctionRestrictions, RestrictionRegistry, RestrictionMap};

use super::{
    expr::*,
    refined_type::{Predicate, Refinement},
    restriction_expr::Expr as RestrictionExpr,
};
use crate::restriction_converter::RestrictionToExprConverter;
use crate::inference_ctx::InferenceCtx;
use syntax_pos::Symbol;
use rustproof_libsmt::backends::z3::Z3;
use rustproof_libsmt::backends::smtlib2::SMTLib2;
use rustproof_libsmt::theories::{core, integer};
use rustproof_libsmt::backends::backend::{SMTBackend, SMTRes};
use rustproof_libsmt::logics::lia::LIA;
use crate::z3_interface::{smt_from_pred, sort_from_ty};
use crate::name_registry::NameRegistry;
use crate::visitor::Visitable;
use crate::folder::Foldable;
use crate::refinable_entity::RefinableEntity;
use maplit::*;
use crate::error::TypeError;
use crate::utils::ANN_RET_NAME;

type VarNameTy = String;

trait LocalByName {
    fn local_by_name(&self, idxs: impl Iterator<Item=Local>, name: &str) -> Option<(Local, &LocalDecl)>;
}

impl LocalByName for Body<'_> {
    fn local_by_name(&self, mut idxs: impl Iterator<Item=Local>, name: &str) -> Option<(Local, &LocalDecl)> {
        idxs.find_map(|local| {
            let local_decl = &self.local_decls[local];
            if let Some(sym) = local_decl.name {
                if sym.as_str() == name {
                    Some((local, local_decl))
                } else {
                    None
                }
            } else {
                None
            }
        })
    }
}

pub(super) struct MirAnalyzer<'tcx, R: RestrictionRegistry> {
    /// DefId of entity (function/const) this MirAnalyzer belongs to
    def_id: DefId,
    mir: &'tcx Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    precondition: InferenceCtx<'tcx>,
    postcondition: InferenceCtx<'tcx>,
    /// map of <local name> -> <refinements from pre/postconditions and refined type aliases>
    type_annotations: HashMap<VarNameTy, Refinement<'tcx>>,
    block_inference_cache: RefCell<HashMap<BasicBlock, InferenceCtx<'tcx>>>,
    /// registry to get globals/functions refinements from
    restriction_registry: R,
    /// all type errors, collected during body check
    errors: Vec<TypeError>,
}

impl<'tcx, R: RestrictionRegistry> MirAnalyzer<'tcx, R> {
    pub fn new(
        def_id: DefId,
        mir: &'tcx Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        precondition: Option<RestrictionExpr>,
        postcondition: Option<RestrictionExpr>,
        type_annotations: HashMap<VarNameTy, Refinement<'tcx>>,
        restriction_registry: R,
    ) -> Result<Self, failure::Error> {
//        let precondition = MirAnalyzer::resolve_restriction_expr(mir, precondition)?;
        Ok(Self {
            def_id,
            mir,
            tcx,
            precondition: Default::default(),
            postcondition: Default::default(),
            type_annotations,
            block_inference_cache: HashMap::with_capacity(mir.basic_blocks().len()).into(),
            restriction_registry,
            errors: Default::default(),
        })
    }

    pub fn errors(&self) -> &[TypeError] {
        &self.errors
    }

    fn resolve_restriction_expr(mir: &Body, expr: RestrictionExpr) -> Result<InferenceCtx<'tcx>, failure::Error> {
        unimplemented!();
        /*
        Ok(match expr {
            RestrictionExpr::V => { Expr::V }
            RestrictionExpr::Var(v) => {
                if v == ANN_RET_NAME {
                    let ret_type = mir.return_ty().sty.clone();
                    let e = Expr::Var(Place::Base(PlaceBase::Local(RETURN_PLACE)));
                    let pred = PredicateConjunction::from_expr(e);
                    let r = Refinement::new(ret_type, pred);
                    InferenceCtx::new()
                } else if let Some(local) = mir.local_decls()
                    .into_iter_enumerated()
                    .take(mir.arg_count)
                    .filter_map(|(i, l)| Some((i, l.name?)))
                    .find(|(_, name)| name == v)
                    .map(|(i, _)| i) {
                    Expr::Var(Place::Base(PlaceBase::Local(local)))
                } else {
                    format_err!("No such argument: {}", v)?
                }
            }
            RestrictionExpr::Const(c) => { Expr::Const(c) }
            RestrictionExpr::UnaryOp(op, box e) => {
                Expr::UnaryOp(op, box MirAnalyzer::resolve_restriction_expr(mir, e)?)
            }
            RestrictionExpr::BinaryOp(op, box lhs, box rhs) => {
                Expr::BinaryOp(op,
                               box MirAnalyzer::resolve_restriction_expr(mir, lhs)?,
                               box MirAnalyzer::resolve_restriction_expr(mir, rhs)?,
                )
            }
        })
        */
    }

    /// Perform function mir liquid type inference and check
    pub fn check(&mut self) -> Result<bool, failure::Error> {
        let init_refinements = self.init_locals_refinements();
        let basic_blocks = self.mir.basic_blocks();
        if let Some(return_bb) = basic_blocks
            .iter_enumerated()
            .find_map(|(idx, data): (_, &BasicBlockData)|
                if let TerminatorKind::Return = data.terminator().kind {
                    Some(idx)
                } else {
                    None
                }) {
            let ictx = InferenceCtx::default();
            let res = self.get_basic_block_base_lqt(return_bb)?;
            println!("fun lqt: {}", res);
        } else {
            unimplemented!("What to do with diverging functions?");
        }
        Ok(self.errors.is_empty())
    }

//    fn local_from_place(&self, place: &Place) -> Local {
//        match place {
//            Place::Base(PlaceBase::Local(l)) = l,
//            Place::Base(_) => unimplemented!(""),
//            Place::Projection(_) => unimplemented!("projection to local")
//        }
//    }

    fn place_from_operand<'o>(&self, operand: &'o Operand<'tcx>) -> &'o Place<'tcx> {
        match operand {
            Operand::Move(p) | Operand::Copy(p) => p,
            Operand::Constant(c) => { unreachable!("constant operand") }
        }
    }

    /// Infer most common types among all liquid types in inference ctxs array
    fn calculate_strongest_conjunction(&self, pred_lqt: impl IntoIterator<Item=InferenceCtx<'tcx>> + Debug) -> InferenceCtx<'tcx> {
//        println!("need to calculate strongest conjunction of\n {}", pred_lqt);
        let refinements: HashMap<_, Vec<Refinement>> = pred_lqt
            .into_iter()
            .map(|ic| {
                ic.into_inner()
            })
            .fold(HashMap::new(), |mut acc, item| {
                item
                    .into_iter()
                    .for_each(|(k, v)| acc.entry(k).or_default().push(v));
                acc
            });
        let disjoined = refinements
            .into_iter()
            .map(|(k, v)| {
                let refinement = Refinement::from_alternatives(v).unwrap();
                (k, refinement)
            })
            .collect();
        InferenceCtx::new(disjoined)
    }

    /// Infer lqt when all predecessors lqt are inferred
    fn infer_block_lqt(&self, idx: BasicBlock, mut ctx: InferenceCtx<'tcx>) -> InferenceCtx<'tcx> {
        let block = &self.mir.basic_blocks()[idx];
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(box (lhs, rhs)) => {
                    let rhs_lqt = self.infer_lqt(&rhs, &ctx);
                    // it is SSA, we assign just once, so refine lhs
                    ctx.refine(RefinableEntity::from_place(lhs.clone(), self.def_id), rhs_lqt);
                }
                StatementKind::FakeRead(_, _) => {
                    // no ideas what to do here
                    // nothing to do here
                }
                StatementKind::SetDiscriminant { box place, variant_index } => {
                    // need to introduce special syntax of refinement to track
                    // enum tag value
                    let expr = Expr::BinaryOp(BinOp::Is, box Expr::V, box Expr::Const(Const::UInt {
                        size: unimplemented!(),
                        bits: variant_index.as_u32() as u128,
                    }));
                    let predicate = expr.into();
                    let refinement = Refinement::new(place.ty(self.mir, self.tcx).ty.kind.clone(), predicate);
                    ctx.refine(RefinableEntity::from_place(place.clone(), self.def_id), refinement)
                }
                StatementKind::StorageLive(_) => {
                    // ??????
                }
                StatementKind::StorageDead(_) => {
                    // ??????
                }
                StatementKind::InlineAsm(_) => {
                    // nothing to do here
                }
                StatementKind::Retag(_, _) => {
                    // something special to miri
                }
                StatementKind::AscribeUserType(_, _) => {
                    // here may be refined type in source code
                    // but in MIR we have only base type of alias
                    // need to find a way to link them
                }
                StatementKind::Nop => {
                    // nop
                }
            }
        }
        ctx
    }

    // in bits
    fn get_scalar_size(&self, scalar: Ty) -> u64 {
        match &scalar.kind {
            TyKind::Bool => 8,
            TyKind::Int(ty) => ty.bit_width().unwrap() as u64,
            TyKind::Uint(ty) => ty.bit_width().unwrap() as u64,
            TyKind::Float(ty) => ty.bit_width() as u64,
            t => unimplemented!("{:?}", t)
        }
    }

    /// Get basic block lqt adhered by condition when control is passed to target
    fn get_basic_block_lqt_for_target(&mut self, bb: BasicBlock, target_block: BasicBlock) -> Result<InferenceCtx<'tcx>, failure::Error> {
        let mut base_lqt = self.get_basic_block_base_lqt(bb)?.clone();

        let block = &self.mir.basic_blocks()[bb];
        let terminator = block.terminator();

        Ok(match terminator.kind {
            TerminatorKind::Goto { target } => {
                debug_assert!(target_block == target);
                // no additional refinements
                base_lqt
            }
            TerminatorKind::SwitchInt { ref discr, switch_ty, ref values, ref targets } => {
                // we refine discriminant with corresponding value in target.
                // unwrap as we know target exists
                let target_idx = targets.iter().find_position(|&&bb| bb == target_block).unwrap().0;
                let value_size = self.get_scalar_size(switch_ty);
                let discr_local = self.place_from_operand(&discr);
                let cnst = |value| match &switch_ty.kind {
                    TyKind::Bool => Ok(Const::Bool(value!=0)),
                    TyKind::Int(_) => Ok(Const::Int { size: value_size, bits: value }),
                    TyKind::Uint(_) => Ok(Const::UInt { size: value_size, bits: value }),
                    t => Err(failure::format_err!("Invalid switch ty: {:?}", t))
                };
                if let Some(&value) = values.get(target_idx) {
                    let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box Expr::Const(cnst(value)?));
                    let refinement = Refinement::new(switch_ty.kind.clone(), expr.into());
                    base_lqt.refine(RefinableEntity::from_place(discr_local.clone(), self.def_id), refinement);
                } else {
                    // otherwise discr is not equal to any of values
                    for &v in values.iter() {
                        let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box Expr::Const(cnst(v)?));
                        let refinement = Refinement::new(switch_ty.kind.clone(), Predicate::from_expr(expr).negated());
                        base_lqt.refine(RefinableEntity::from_place(discr_local.clone(), self.def_id), refinement);
                    }
                };
                base_lqt
            }
            TerminatorKind::Call { ref func, ref args, ref destination, cleanup, from_hir_call } => {
                if let Some((ref dst, target)) = *destination {
                    // TODO: may be target_block == cleanup
                    assert_eq!(target_block, target);
                    if let &Operand::Constant(box Constant { literal: RustConst { ty: TyS { kind: TyKind::FnDef(func_def, subst), .. }, ..}, .. }) = func {
                        let self_id = self.def_id;
                        if *func_def == self_id {
                            unimplemented!("Recursive call analysis is not implemented");
                        }
                        let tcx = self.tcx;
                        if let Some(descr) = self.check_function_call_precondition(*func_def, tcx.empty_substs_for_def_id(*func_def), args, base_lqt.clone())? {
                            self.errors.push(TypeError::new(descr, terminator.source_info.span));
//                            panic!("Found precondition violation");
                        }
                        let self_body = self.mir;
                        let reft = self.function_refinement(*func_def)?;
                        base_lqt.refine(RefinableEntity::from_place(dst.clone(), self_id), Refinement::new(dst.ty(self_body.local_decls(), tcx).ty.kind.clone(), reft.post().fold(&mut RestrictionToExprConverter(self_body, "return", *func_def))?.into()));
                        // need to precondition refinements for arguments and postcondition refinements for destination
//                        unimplemented!();
                        base_lqt
                    } else {
                        unreachable!()
                    }
                } else {
                    unimplemented!()
                }
            }
            TerminatorKind::Assert { ref cond, expected, ref msg, target, cleanup } => {
                let local = self.place_from_operand(&cond);
                let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box Expr::Const(Const::Bool(expected)));
                let pred = Predicate::from_expr(expr);

                let pred = if target == target_block {
                    pred
                } else if let Some(target) = cleanup {
                    assert_eq!(target, target_block);
                    pred.negated()
                } else {
                    unreachable!()
                };
                let refinement = Refinement::new(TyKind::Bool, pred);
                base_lqt.refine(RefinableEntity::from_place(local.clone(), self.def_id), refinement);
                base_lqt
            }
            // explicitly list all rest variants to not skip something
            TerminatorKind::Resume |
            TerminatorKind::Abort |
            TerminatorKind::Return |
            TerminatorKind::Unreachable |
            TerminatorKind::Drop { .. } |
            TerminatorKind::DropAndReplace { .. } |
            TerminatorKind::Yield { .. } |
            TerminatorKind::GeneratorDrop |
            TerminatorKind::FalseEdges { .. } |
            TerminatorKind::FalseUnwind { .. } => unreachable!()
        })
    }

    /// Calculate basic block lqt without terminator analysis
    fn get_basic_block_base_lqt(&mut self, current_block: BasicBlock) -> Result<InferenceCtx<'tcx>, failure::Error> {
        if let Some(res) = self.block_inference_cache.borrow().get(&current_block) {
            return Ok(res.clone());
        }
        let predecessors = self.mir.predecessors_for(current_block);
        let pred_lqt: Vec<_> = if predecessors.is_empty() {
            let mut locals_init_lqt = self.init_locals_refinements();
            let self_refinement = self.self_refinement();
            let self_precondition = self_refinement.pre().clone();
            let precond = self.preconditions_to_inference_ctx(&self_precondition, self.mir, self.def_id)?;
            locals_init_lqt.merge(precond);
            vec![locals_init_lqt]
        } else {
            predecessors
                // TODO: parallelize
                .iter()
                .map(|&bb| self.get_basic_block_lqt_for_target(bb, current_block))
                .collect::<Result<Vec<_>, _>>()?
        };
        let ctx = self.calculate_strongest_conjunction(pred_lqt);

        let val = self.infer_block_lqt(current_block, ctx);
        Ok(self.block_inference_cache.borrow_mut().entry(current_block).or_insert(val).clone())
    }

    fn self_refinement(&mut self) -> &FunctionRestrictions {
        // unwrap as we sure that current function is registered in registry
//        unimplemented!();
        self.restriction_registry.get_or_extract_restrictions(self.def_id, self.tcx).unwrap()
    }

    /// Get function pre and postconditions
    fn function_refinement(&mut self, func_id: DefId) -> Result<&FunctionRestrictions, failure::Error>{
//        unimplemented!();
        self.restriction_registry.get_or_extract_restrictions(func_id, self.tcx)
    }

    fn preconditions_to_inference_ctx(&self, restrictions: &RestrictionMap, mir: &'tcx Body, fun_id: DefId) -> Result<InferenceCtx<'tcx>, failure::Error> {
        restrictions
            .into_iter()
            .try_fold(InferenceCtx::default(), |mut ctx, (var, restriction)| -> Result<_, failure::Error> {
                let (local, local_decl) = mir.local_by_name(mir.args_iter(), &var).ok_or(failure::format_err!("Unknown variable {}", var))?;
                let refinement = Refinement::new(local_decl.ty.kind.clone(), restriction.clone().fold(&mut RestrictionToExprConverter(mir, &var, fun_id))?.into());
                ctx.refine(RefinableEntity::from_place(local.into(), fun_id), refinement);
                Ok(ctx)
            })
    }

    /// there may be constant in args, we need to add them to ctx
    /// we also need to unify formal arguments with actual
    /// i.e given that `fn foo(a,b,c) {...}` is called as `foo(x,y,z)`
    /// we need to add assertions `a=x`,`b=y`,`c=z` to ctx
    fn merge_ctx_with_args(&self, mut ctx: InferenceCtx<'tcx>, args: &[Operand<'tcx>], mir: &Body, fun_id: DefId) -> InferenceCtx<'tcx> {

        for (actual, formal) in args.into_iter().zip(mir.args_iter()) {
            match actual {
                Operand::Constant(box value) => {
                    ctx.refine(RefinableEntity::from_place(formal.into(), fun_id), Refinement::new(
                        value.literal.ty.kind.clone(),
                        Expr::BinaryOp(BinOp::Eq, box Expr::V, box value.literal.into()).into()
                    )
                    )
                }
                Operand::Copy(value) | Operand::Move(value) => {
                    ctx.refine(RefinableEntity::from_place(formal.into(), fun_id), Refinement::new(
                        value.ty(&self.mir.local_decls, self.tcx).ty.kind.clone(),
                        Expr::BinaryOp(BinOp::Eq, box Expr::V, box Expr::from_place(value.clone(), self.def_id)).into()
                    ))
                }
            }
        }
        ctx
    }

    fn check_function_call_precondition(&mut self, func_def: DefId, subst: SubstsRef<'tcx>, args: &[Operand<'tcx>], ctx: InferenceCtx<'tcx>) -> Result<Option<String>, failure::Error> {
        println!("checking function call precondition of {:?}:\nsubst: {:?}\nargs: {:?}", func_def, subst, args);
        // Argument is either constant or place
        // If it is place, its refinement already exists in ctx
        // If it is constant, we need to add refinement to corresponding formal argument of function
        let tcx = self.tcx;
        let reft = self.function_refinement(func_def)?;
        let fun_body = tcx.instance_mir(Instance::new(func_def, subst).def);
        let precondition = reft.pre().clone();
        let mut need = self.preconditions_to_inference_ctx(&precondition, fun_body, func_def)?;
        let mut given = self.merge_ctx_with_args(ctx, args, fun_body, func_def);
        // Need to convert restriction map to refinement map, build Z3 expression and check its inverse to be not provable
        let bodies = hashmap!{self.def_id => self.mir, func_def => fun_body};
        let pp = |ctx: &mut InferenceCtx| {
            ctx.refinements_mut()
                .iter()
                .map(|(e, p)|
                    format!("{}: {}",
                            e.name(bodies
                                .get(&e.fun_id())
                                .expect(&format!("No body for function id {:?}", e.fun_id()))
                            )
                                .unwrap_or(format!("{}", e)), p)
                )
                .join("\n")
        };
        let need_pp = pp(&mut need);
        println!("given: {}\nneed:{}",
                 pp(&mut given),
                 need_pp,
        );
        if let Some(model) = self.check_implication_holds(given, need, &bodies)? {
            Ok(Some(format!("Constraint violation:\nConstraint: {}\nModel: {}", need_pp, model)))
        } else {
            Ok(None)
        }
    }

    // checks that /\P->/\Q holds (!(/\P->/\Q) is not provable)
    fn check_implication_holds(&self, mut p: InferenceCtx<'tcx>, mut q: InferenceCtx<'tcx>, bodies: &HashMap<DefId, &Body<'tcx>>) -> Result<Option<String>, failure::Error> {
        println!("Check implication holds:\np: {:#?}\nq: {:#?}", p, q);
        let mut z3 = Z3::new_with_binary("./z3");
        let mut solver = SMTLib2::new(Some(LIA));
        solver.set_logic(&mut z3);
        let mut names = HashMap::new();
        let mut name_registry = NameRegistry::new(bodies);
//        names.insert(String::from("!v"), solver.new_var(Some("!v"), sort_from_ty(&v_ty).unwrap()));
        let mut processor = |ctx: &mut InferenceCtx<'tcx>| {
            for (var, reft) in ctx.refinements_mut() {
                if !names.contains_key(var) {
                    let ty = reft.base_type();
                    if let Some(sort) = sort_from_ty(ty) {
                        let name = name_registry.get(var.clone());
                        names.insert(var.clone(), solver.new_var(Some(name), sort));
                    } else {
                        println!("Cannot convert type {:?} of var: {} to sort, ignoring", ty, var);
                    }
                }
                *reft.predicate_mut() = reft.predicate().clone().accept(&mut |expr| {
//                    println!("Checking {:?}", expr);
                    if let Expr::V = expr {
//                        println!("Converting v to {:?}", var);
                        Expr::Var(var.clone())
                    } else {
                        expr
                    }
                });
            }
        };
        processor(&mut p);
//        for (var, reft) in q.refinements_mut() {
//            names.entry(var.clone()).or_insert_with(|| {
//                let name = name_registry.get(var.clone());
//                let ty = reft.base_type();
//                solver.new_var(Some(name), sort_from_ty(ty).expect(&format!("Cannot convert {:?} to sort", ty)))
//            });
//            *reft.predicate_mut() = reft.predicate().clone().accept(&mut |expr| if let Expr::V = expr {
//                println!("Converting q v to {:?}", var);
//                Expr::Var(var.clone())
//            } else {
//                expr
//            });
//        }
        processor(&mut q);
//        let mut declarator = |e: &Expr| {
//            if let Expr::Var(place) = e {
//                if let PlaceBase::Local(local) = place.base {
//                    names.entry(place).or_insert_with(|| {
//                        let name = name_registry.get(local);
//                        let ty = &self.mir.local_decls[local].ty.kind;
//                        solver.new_var(Some(name), sort_from_ty(ty).expect(&format!("Cannot convert {:?} to sort", ty)))
//                    });
//                } else {
//                    println!("Static as Var not implemented: {:?}", place);
//                }
//            }
//        };

//        p.into_iter().for_each(|expr| expr.accept(&mut declarator));
//        q.into_iter().for_each(|expr| expr.accept(&mut declarator));

        println!("Check implication holds after :\np: {:#?}\nq: {:#?}", p, q);
        let ps = p.predicates()
            .map(|e| smt_from_pred(&mut solver, &names, &e))
            .collect::<Vec<_>>();
        let qs = q.predicates()
            .map(|e| smt_from_pred(&mut solver, &names, &e))
            .collect::<Vec<_>>();

        let p_all = match ps.len() {
            0 => solver.new_const(core::OpCodes::Const(true)),
            1 => ps[0],
            _ => solver.assert(core::OpCodes::And, &ps),
        };
        let q_all = match qs.len() {
            0 => solver.new_const(core::OpCodes::Const(true)),
            1 => qs[0],
            _ => solver.assert(core::OpCodes::And, &qs),
        };
        let imply = solver.assert(core::OpCodes::Imply, &[p_all, q_all]);
        let _ = solver.assert(core::OpCodes::Not, &[imply]);

        println!("Solver: {:#?}", solver);
        let (_, sat) = solver.solve(&mut z3, false);

        match sat {
            SMTRes::Unsat(_, _) => Ok(None),
            SMTRes::Sat(_, Some(model)) => Ok(Some(model)),
            SMTRes::Sat(_, None) => Ok(Some("No model received".into())),
            SMTRes::Error(err, _) => Err(failure::err_msg(err))
        }
    }

    /// Infer lqt of rvalue in cxt
    fn infer_lqt(&self, v: &Rvalue<'tcx>, ctx: &InferenceCtx<'tcx>) -> Refinement<'tcx> {
        match *v {
            // simple assign one value to another, no less no more
            Rvalue::Use(ref oprnd) => {
                match oprnd {
                    Operand::Copy(ref p) | Operand::Move(ref p) => {
                        // we get rid of intermediate x=y, directly copy y's refinement to x
//                        ctx.get_refinement(&RefinableEntity::from_place(p.clone(), self.def_id))
                        // we cannot just copy rhs refinement to lhs, as rhs may be referred in path predicate
                        let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box Expr::from_place(p.clone(), self.def_id));
                        Refinement::new(p.ty(self.mir.local_decls(), self.tcx).ty.kind.clone(), expr.into())
                    }
                    Operand::Constant(box c) => {
                        let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box c.literal.into());
                        Refinement::new(c.literal.ty.kind.clone(), expr.into())
//                        unimplemented!("constant assign")
                    }
                }
            }
            Rvalue::Repeat(_, _) => unimplemented!("array literal"),
            Rvalue::Ref(_, _, _) => unimplemented!("reference"),
            Rvalue::Len(_) => unimplemented!("rvalue len"),
            Rvalue::Cast(_, _, _) => unimplemented!("cast"),

            // TODO: handle checked op properly, as it returns tuple (bool, ty)
            | Rvalue::CheckedBinaryOp(op, ref lhs, ref rhs) => unimplemented!("checked op"),
            | Rvalue::BinaryOp(op, ref lhs, ref rhs) => {
                let oper = Expr::binary_op(op.into(), Expr::from_operand(lhs.clone(), self.def_id), Expr::from_operand(rhs.clone(), self.def_id));
                let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box oper);
                let pred = expr.into();
                let lhs_ty = lhs.ty(self.mir.local_decls(), self.tcx);
                let rhs_ty = rhs.ty(self.mir.local_decls(), self.tcx);
                Refinement::new(op.ty(self.tcx, lhs_ty, rhs_ty).kind.clone(), pred)
            }

            Rvalue::NullaryOp(op, rhs) => {
                unimplemented!("nullary op")
            }
            Rvalue::UnaryOp(op, ref rhs) => {
                let oper = Expr::UnaryOp(op.into(), box Expr::from_operand(rhs.clone(), self.def_id));
                let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box oper);
                let pred = expr.into();
                let rhs_ty = rhs.ty(self.mir.local_decls(), self.tcx);
//                let op_ty = match op {
//                    UnOp::Not => &self.tcx.types.bool.kind,
//                    UnOp::Neg => {
//                        &rhs.ty(self.mir.local_decls(), self.tcx).kind
//                    }
//                };
                Refinement::new(rhs_ty.kind.clone(), pred)
            }
            Rvalue::Discriminant(ref p) => {
                // need new operator <discr_of> to describe value of target place
                unimplemented!("discr read")
            }
            Rvalue::Aggregate(_, _) => unimplemented!("aggregate create"),
        }
    }

    fn refine_function_call(&self, func: &Operand, args: &[Operand]) -> Refinement {
        unimplemented!()
    }

    fn assign_init_refinement(&self) {}

    fn get_argument_refinement(&self, arg: &LocalDecl<'tcx>) -> Refinement<'tcx> {
        // assume arguments are always named
        let name = arg.name.unwrap().as_str();
        let ty = arg.ty.kind.clone();
        self.type_annotations.get(&*name).cloned().unwrap_or_else(|| Refinement::unknown(ty))
    }

    fn get_return_refinement(&self, _: &LocalDecl) -> Refinement<'tcx> {
        let ty = self.mir.return_ty().kind.clone();
        self.type_annotations.get(ANN_RET_NAME).cloned().unwrap_or_else(|| Refinement::unknown(ty))
    }

    fn get_tmp_refinement(&self, arg: &LocalDecl<'tcx>) -> Refinement<'tcx> {
        let ty = arg.ty.kind.clone();
        Refinement::unknown(ty)
    }

    /// let x: Foo = bar;
    fn get_var_refinement(&self, arg: &LocalDecl<'tcx>) -> Refinement<'tcx> {
        // TODO: handle user provided type
        let ty = arg.ty.kind.clone();
        Refinement::unknown(ty)
    }

    fn init_locals_refinements(&self) -> InferenceCtx<'tcx> {
        let locals = self.mir.local_decls();
        let mut ctx = InferenceCtx::default();
        for (idx, local) in locals.iter_enumerated() {
            let refinement = match self.mir.local_kind(idx) {
                // do we need to handle pre/postconditions separately?
                LocalKind::Arg => self.get_argument_refinement(local),
                LocalKind::ReturnPointer => self.get_return_refinement(local),
                LocalKind::Var => self.get_var_refinement(local),
                LocalKind::Temp => self.get_tmp_refinement(local)
            };
            ctx.refine(RefinableEntity::from_place(idx.into(), self.def_id), refinement)
        }
        ctx
    }
}
