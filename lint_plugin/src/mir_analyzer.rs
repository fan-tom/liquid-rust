use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::Debug
};

use itertools::Itertools;
use rustc::{
    hir::def_id::DefId,
    mir::{Field, BasicBlockData, Body, Constant, HasLocalDecls, Local, LocalDecl, LocalKind, Operand, Place, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind, BasicBlock, ProjectionElem},
    ty::{
        Const as RustConst,
        Ty,
        TyKind,
        TyS,
        Instance,
        TyCtxt
    }
};

use crate::{
    refinements_registry::{FunctionRestrictions, RestrictionRegistry, RestrictionMap},
    restriction_converter::RestrictionToExprConverter,
    inference_ctx::InferenceCtx,
    z3_interface::{smt_from_pred, sort_from_ty},
    name_registry::NameRegistry,
    folder::Foldable,
    refinable_entity::RefinableEntity,
    error::TypeError,
    utils::ANN_RET_NAME
};

use super::{
    expr::*,
    refined_type::{Predicate, Refinement},
    restriction_expr::Expr as RestrictionExpr,
};
use rustproof_libsmt::{
    backends::{
        z3::Z3,
        smtlib2::SMTLib2,
        backend::{SMTBackend, SMTRes}
    },
    theories::core,
    logics::lia::LIA
};
use maplit::*;

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
        type_annotations: HashMap<VarNameTy, Refinement<'tcx>>,
        restriction_registry: R,
    ) -> Result<Self, failure::Error> {
        Ok(Self {
            def_id,
            mir,
            tcx,
            type_annotations,
            block_inference_cache: HashMap::with_capacity(mir.basic_blocks().len()).into(),
            restriction_registry,
            errors: Default::default(),
        })
    }

    pub fn errors(&self) -> &[TypeError] {
        &self.errors
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
            let mut res = self.get_basic_block_base_lqt(return_bb)?;
            println!("fun lqt: {}", res);
            let body = self.mir;
            let fun_id = self.def_id;
            let self_post = self.self_refinement().post();
            let mut need = Self::postcondition_to_inference_ctx(self_post, body, fun_id)?;
            if let Some(model) = self.check_implication_holds(&mut res, &mut need, &hashmap! {self.def_id => self.mir})? {
                self.errors.push(TypeError::new(format!("Constraint violation:\nConstraint: {}\nModel: {}", need, model), self.mir.span));
            }
        } else {
            unimplemented!("What to do with diverging functions?");
        }
        Ok(self.errors.is_empty())
    }

    fn place_from_operand<'o>(&self, operand: &'o Operand<'tcx>) -> &'o Place<'tcx> {
        match operand {
            Operand::Move(p) | Operand::Copy(p) => p,
            Operand::Constant(_) => { unreachable!("constant operand") }
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
//                    ctx.refine(RefinableEntity::from_place(lhs.clone(), self.def_id), rhs_lqt);
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
                    TyKind::Bool => Ok(Const::Bool(value != 0)),
                    TyKind::Int(_) => Ok(Const::Int { size: value_size, bits: value }),
                    TyKind::Uint(_) => Ok(Const::UInt { size: value_size, bits: value }),
                    t => Err(failure::format_err!("Invalid switch ty: {:?}", t))
                };
                let discr_re = RefinableEntity::from_place(discr_local.clone(), self.def_id);
                if let Some(&value) = values.get(target_idx) {
                    let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box Expr::Const(cnst(value)?));
                    let refinement = Refinement::new(switch_ty.kind.clone(), expr.into());
                    base_lqt.refine(discr_re.clone(), refinement);
                } else {
                    // otherwise discr is not equal to any of values
                    for &v in values.iter() {
                        let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box Expr::Const(cnst(v)?));
                        let refinement = Refinement::new(switch_ty.kind.clone(), Predicate::from_expr(expr).negated());
                        base_lqt.refine(discr_re.clone(), refinement);
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
                        println!("checking function call precondition of {:?}:\nsubst: {:?}\nargs: {:?}", func_def, subst, args);
                        let fun_body = self.tcx.instance_mir(Instance::new(*func_def, subst).def);
                        let args_mapping = self.formal_to_actual_mapping(args, fun_body, *func_def);
                        let FunctionRestrictions(precondition, postcondition) = self.function_refinement(*func_def)?.clone();
                        let mut given = base_lqt.clone();
                        Self::merge_ctx_with_args2(&mut given, args_mapping.clone());
                        if let Some(descr) = self.check_function_call_precondition(*func_def, fun_body, precondition, given.clone())? {
                            self.errors.push(TypeError::new(descr, terminator.source_info.span));
//                            panic!("Found precondition violation");
                        }
                        let self_body = self.mir;
                        base_lqt.refine(
                            RefinableEntity::from_place(dst.clone(), self_id),
                            Refinement::new(
                                dst.ty(self_body.local_decls(), tcx).ty.kind.clone(),
                                postcondition
                                    .fold(&mut RestrictionToExprConverter(fun_body, "return", *func_def))?
                                    // here we replace all references to formal arguments in postcondition with corresponding actual parameters
                                    .accept(&mut |e|
                                        if let Expr::Var(formal) = e {
                                            args_mapping.get(&formal).expect(&format!("No actual parameter for {} in args mapping", formal)).1.clone()
                                        } else {
                                            e
                                        }
                                    )
                                    .into(),
                            ),
                        );
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
            let precond = Self::preconditions_to_inference_ctx(&self_precondition, self.mir, self.def_id)?;
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
        self.function_refinement(self.def_id).unwrap()
    }

    /// Get function pre and postconditions
    fn function_refinement(&mut self, func_id: DefId) -> Result<&FunctionRestrictions, failure::Error> {
        self.restriction_registry.get_or_extract_restrictions(func_id, self.tcx)
    }

    fn postcondition_to_inference_ctx(restriction: &RestrictionExpr, mir: &'tcx Body, fun_id: DefId) -> Result<InferenceCtx<'tcx>, failure::Error> {
        let mut ctx = InferenceCtx::default();
        let refinement = Refinement::new(mir.return_ty().kind.clone(), restriction.clone().fold(&mut RestrictionToExprConverter(mir, ANN_RET_NAME, fun_id))?.into());
        ctx.refine(RefinableEntity::from_place(RETURN_PLACE.into(), fun_id), refinement);
        Ok(ctx)
    }

    fn preconditions_to_inference_ctx(restrictions: &RestrictionMap, mir: &'tcx Body, fun_id: DefId) -> Result<InferenceCtx<'tcx>, failure::Error> {
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
            let target = RefinableEntity::from_place(formal.into(), fun_id);
            match actual {
                Operand::Constant(box value) => {
                    ctx.refine(target, Refinement::new(
                        value.literal.ty.kind.clone(),
                        Expr::BinaryOp(BinOp::Eq, box Expr::V, box value.literal.into()).into(),
                    ),
                    )
                }
                Operand::Copy(value) | Operand::Move(value) => {
                    ctx.refine(target, Refinement::new(
                        value.ty(&self.mir.local_decls, self.tcx).ty.kind.clone(),
                        Expr::BinaryOp(BinOp::Eq, box Expr::V, box Expr::from_place(value.clone(), self.def_id)).into(),
                    ))
                }
            }
        }
        ctx
    }

    fn merge_ctx_with_args2(ctx: &mut InferenceCtx<'tcx>, mapping: HashMap<RefinableEntity<'tcx>, (TyKind<'tcx>, Expr<'tcx>)>) {
        for (formal, (ty, expr)) in mapping {
            ctx.refine(formal, Refinement::new(ty, Expr::BinaryOp(BinOp::Eq, box Expr::V, box expr).into()));
        }
    }

    /// Return mapping from formal parameter to actual argument, actually to Expr::Var or Expr::Const
    fn formal_to_actual_mapping(&self, args: &[Operand<'tcx>], body: &Body, fun_id: DefId) -> HashMap<RefinableEntity<'tcx>, (TyKind<'tcx>, Expr<'tcx>)> {
        args.into_iter()
            .zip(body.args_iter())
            .map(|(actual, formal)|
                (RefinableEntity::from_place(formal.into(), fun_id),
                 match actual {
                     Operand::Constant(box value) => (value.literal.ty.kind.clone(), value.literal.into()),
                     Operand::Copy(value) | Operand::Move(value) => (
                         value.ty(&self.mir.local_decls, self.tcx).ty.kind.clone(),
                         Expr::from_place(value.clone(), self.def_id)
                     )
                 })
            )
            .collect()
    }

    fn check_function_call_precondition(&mut self, func_def: DefId, fun_body: &'tcx Body, precondition: RestrictionMap, mut given: InferenceCtx<'tcx>) -> Result<Option<String>, failure::Error> {
        // Argument is either constant or place
        // If it is place, its refinement already exists in ctx
        // If it is constant, we need to add refinement to corresponding formal argument of function
        let mut need = Self::preconditions_to_inference_ctx(&precondition, fun_body, func_def)?;
        // Need to convert restriction map to refinement map, build Z3 expression and check its inverse to be not provable
        let bodies = hashmap! {self.def_id => self.mir, func_def => fun_body};
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
        if let Some(model) = self.check_implication_holds(&mut given, &mut need, &bodies)? {
            Ok(Some(format!("Constraint violation:\nConstraint: {}\nModel: {}", need_pp, model)))
        } else {
            Ok(None)
        }
    }

    // checks that /\P->/\Q holds (!(/\P->/\Q) is not provable)
    fn check_implication_holds(&self, p: &mut InferenceCtx<'tcx>, q: &mut InferenceCtx<'tcx>, bodies: &HashMap<DefId, &Body<'tcx>>) -> Result<Option<String>, failure::Error> {
        println!("Check implication holds:\np: {}\nq: {}", p, q);
        let z3exec = std::env::var("LIQUID_Z3").ok();
        let mut z3 = z3exec.map(|e| Z3::new_with_binary(&e)).unwrap_or_default();
        let mut solver = SMTLib2::new(Some(LIA));
        solver.set_logic(&mut z3);
        let mut names = HashMap::new();
        let mut name_registry = NameRegistry::new(bodies);
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
        processor(p);
        processor(q);

        println!("Check implication holds after :\np: {}\nq: {}", p, q);
        let ps = p.predicates()
            .map(|e| smt_from_pred(&mut solver, &names, &e))
            .collect::<Vec<_>>();
        let qs = q.predicates()
            .map(|e| smt_from_pred(&mut solver, &names, &e))
            .collect::<Vec<_>>();

//        let p_all = match ps.len() {
//            0 => solver.new_const(core::OpCodes::Const(true)),
//            1 => ps[0],
//            _ => solver.assert(core::OpCodes::And, &ps),
//        };
        let q_all = match qs.len() {
            0 => solver.new_const(core::OpCodes::Const(true)),
            1 => qs[0],
            _ => solver.assert(core::OpCodes::And, &qs),
        };
//        let imply = solver.assert(core::OpCodes::Imply, &[p_all, q_all]);
        let not_imply = solver.assert(core::OpCodes::Not, &[q_all]);

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
    fn infer_lqt(&self, v: &Rvalue<'tcx>, target_place: Place<'tcx>, ctx: &mut InferenceCtx<'tcx>) {
        match *v {
            // simple assign one value to another, no less no more
            Rvalue::Use(ref oprnd) => {
                let rhs_lqt = match oprnd {
                    Operand::Copy(ref p) | Operand::Move(ref p) => {
                        // we cannot just copy rhs refinement to lhs, as rhs may be referred in path predicate
                        let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box Expr::from_place(p.clone(), self.def_id));
                        Refinement::new(p.ty(self.mir.local_decls(), self.tcx).ty.kind.clone(), expr.into())
                    }
                    Operand::Constant(box c) => {
                        let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box c.literal.into());
                        Refinement::new(c.literal.ty.kind.clone(), expr.into())
//                        unimplemented!("constant assign")
                    }
                };
                ctx.refine(RefinableEntity::from_place(target_place, self.def_id), rhs_lqt);
            }
            Rvalue::Repeat(_, _) => unimplemented!("array literal"),
            Rvalue::Ref(_, _, _) => unimplemented!("reference"),
            Rvalue::Len(_) => unimplemented!("rvalue len"),
            Rvalue::Cast(_, _, _) => unimplemented!("cast"),

            // { v: (ty, bool) | v.0 = lhs <op> rhs }
            | Rvalue::CheckedBinaryOp(op, ref lhs, ref rhs) => {
//                unimplemented!("checked op")
                let oper = Expr::binary_op(op.into(), Expr::from_operand(lhs.clone(), self.def_id), Expr::from_operand(rhs.clone(), self.def_id));
                // { v: ty | v = lhs <op> rhs }
                let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box oper);
                let pred = expr.into();
                let lhs_ty = lhs.ty(self.mir.local_decls(), self.tcx);
                let rhs_ty = rhs.ty(self.mir.local_decls(), self.tcx);
                let op_ty = op.ty(self.tcx, lhs_ty, rhs_ty);
                let rhs_lqt = Refinement::new(op_ty.kind.clone(), pred);
                let value_place = Place {
                    base: target_place.base,
                    projection: {
                        let mut projection = target_place.projection.to_vec();
                        projection.push(ProjectionElem::Field(Field::from(0usize), op_ty));
                        self.tcx.intern_place_elems(&projection)
                    },
                };
                ctx.refine(RefinableEntity::from_place(value_place, self.def_id), rhs_lqt);
            }
            | Rvalue::BinaryOp(op, ref lhs, ref rhs) => {
                let oper = Expr::binary_op(op.into(), Expr::from_operand(lhs.clone(), self.def_id), Expr::from_operand(rhs.clone(), self.def_id));
                // { v: ty | v = lhs <op> rhs }
                let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box oper);
                let pred = expr.into();
                let lhs_ty = lhs.ty(self.mir.local_decls(), self.tcx);
                let rhs_ty = rhs.ty(self.mir.local_decls(), self.tcx);
                let rhs_lqt = Refinement::new(op.ty(self.tcx, lhs_ty, rhs_ty).kind.clone(), pred);
                ctx.refine(RefinableEntity::from_place(target_place, self.def_id), rhs_lqt);
            }

            Rvalue::NullaryOp(op, rhs) => {
                unimplemented!("nullary op")
            }
            Rvalue::UnaryOp(op, ref rhs) => {
                let oper = Expr::UnaryOp(op.into(), box Expr::from_operand(rhs.clone(), self.def_id));
                let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box oper);
                let pred = expr.into();
                let rhs_ty = rhs.ty(self.mir.local_decls(), self.tcx);
                let rhs_lqt = Refinement::new(rhs_ty.kind.clone(), pred);
                ctx.refine(RefinableEntity::from_place(target_place, self.def_id), rhs_lqt);
            }
            Rvalue::Discriminant(ref p) => {
                // need new operator <discr_of> to describe value of target place
                unimplemented!("discr read")
            }
            Rvalue::Aggregate(_, _) => unimplemented!("aggregate create"),
        }
    }

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
