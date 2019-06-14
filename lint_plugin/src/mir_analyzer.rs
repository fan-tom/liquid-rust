use std::collections::HashMap;

use itertools::Itertools;
use rustc::hir::def_id::DefId;
use rustc::mir::{BasicBlock, BasicBlockData, Body, Constant, HasLocalDecls, Local, LocalDecl, LocalKind, Operand, Place, Rvalue, StatementKind, TerminatorKind, UnOp};
use rustc::ty::{Const as RustConst, Ty, TyKind, TyS};
use rustc::ty::TyCtxt;
use rustc_data_structures::indexed_vec::IndexVec;

use super::{
    expr::*,
    refined_type::{PredicateConjunction, Refinement},
};

const ANN_RET_NAME: &str = "return";

type VarNameTy = String;

/// Holds inferred types of local variables;
#[derive(Clone, Debug, Default)]
pub struct InferenceCtx<'tcx> {
    // need some type here to represent qualifiable entities, such as function args,
    // function return, locals, temps, struct fields and slice elems.
    // seems that Place is power enough for that purpose
    refinements: HashMap<Place<'tcx>, Refinement<'tcx>>,
}

impl<'tcx> InferenceCtx<'tcx> {
    pub fn new(refinements: HashMap<Place<'tcx>, Refinement<'tcx>>) -> Self {
        Self { refinements }
    }

    fn place_refinement(&self, p: &Place<'tcx>) -> Refinement<'tcx> {
        self.refinements[p].clone()
    }

    fn refine(&mut self, var: Place<'tcx>, lqt: Refinement<'tcx>) {
        // we need to assign more specific type to var, provided by lqt
        // and also check that it is compatible with existing one
        // conjoin predicates
        if let Some(existing_refinement) = self.refinements.get_mut(&var) {
            existing_refinement.adjust(lqt).unwrap();
        } else {
            self.refinements.insert(var, lqt);
        }
    }

    fn updated(&self, var: Place<'tcx>, lqt: Refinement<'tcx>) -> Self {
        let mut res = self.clone();
        res.refine(var, lqt);
        res
    }
}

pub(super) struct MirAnalyzer<'a, 'gcx, 'mir, 'tcx> {
    mir: &'mir Body<'tcx>,
    tcx: TyCtxt<'a, 'gcx, 'tcx>,
    precondition: Vec<InferenceCtx<'tcx>>,
    postcondition: Vec<InferenceCtx<'tcx>>,
    /// map of <local name> -> <refinements from pre/postconditions and refined type aliases>
    type_annotations: HashMap<VarNameTy, Refinement<'tcx>>,
}

impl<'a, 'gcx, 'mir, 'tcx> MirAnalyzer<'a, 'gcx, 'mir, 'tcx> {
    pub fn new(mir: &'mir Body<'tcx>, tcx: TyCtxt<'a, 'gcx, 'tcx>, precondition: Vec<InferenceCtx<'tcx>>, postcondition: Vec<InferenceCtx<'tcx>>, type_annotations: HashMap<VarNameTy, Refinement<'tcx>>) -> Self {
        Self { mir, tcx, precondition, postcondition, type_annotations }
    }

    /// Perform function mir liquid type inference and check
    pub fn check(&self) {
        let init_refinements = self.assign_init_refinements();
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
            let res = self.get_basic_block_base_lqt(return_bb);
            println!("fun lqt: {:?}", res);
        } else {
            unreachable!("What to do with diverging functions?");
        }
    }

//    fn local_from_place(&self, place: &Place) -> Local {
//        match place {
//            Place::Base(PlaceBase::Local(l)) => l,
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
    fn calculate_strongest_conjunction(&self, pred_lqt: Vec<InferenceCtx<'tcx>>) -> InferenceCtx<'tcx> {
        println!("need to calculate strongest conjunction of\n {:?}", pred_lqt);
        let refinements: HashMap<Place, Vec<Refinement>> = pred_lqt
            .into_iter()
            .map(|ic| {
                ic.refinements
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
                StatementKind::Assign(lhs, rhs) => {
                    let rhs_lqt = self.infer_lqt(&rhs, &ctx);
                    // it is SSA, we assign just once, so refine lhs
                    ctx.refine(lhs.clone(), rhs_lqt);
                }
                StatementKind::FakeRead(_, _) => {
                    // no ideas what to do here
                    // nothing to do here
                }
                StatementKind::SetDiscriminant { place, variant_index } => {
                    // need to introduce special syntax of refinement to track
                    // enum tag value
                    let expr = Expr::BinaryOp(BinOp::Is, box Expr::V, box Expr::Const(Const::UInt {
                        size: unimplemented!(),
                        bits: variant_index.as_u32() as u128,
                    }));
                    let predicate = PredicateConjunction::from_expr(expr);
                    let refinement = Refinement::new(place.ty(self.mir, self.tcx).ty.sty, predicate);
                    ctx.refine(place.clone(), refinement)
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
                StatementKind::AscribeUserType(_, _, _) => {
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

    fn get_scalar_size(&self, scalar: Ty) -> u8 {
        unimplemented!()
    }

    /// Get basic block lqt adhered by condition when control is passed to target
    fn get_basic_block_lqt_for_target(&self, bb: BasicBlock, target_block: BasicBlock) -> InferenceCtx<'tcx> {
        let mut base_lqt = self.get_basic_block_base_lqt(bb);

        let block = &self.mir.basic_blocks()[bb];

        match block.terminator().kind {
            TerminatorKind::Goto { target } => {
                assert_eq!(target_block, target);
                // no additional refinements
                base_lqt
            }
            TerminatorKind::SwitchInt { ref discr, switch_ty, ref values, ref targets } => {
                // we refine discriminant with corresponding value in target.
                // unwrap as we know target exists
                let target_idx = targets.iter().find_position(|&&bb| bb == target_block).unwrap().0;
                let value_size = self.get_scalar_size(switch_ty);
                let discr_local = self.place_from_operand(&discr).clone();
                if let Some(&value) = values.get(target_idx) {
                    let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box Expr::Const(Const::Int { size: value_size, bits: value }));
                    let refinement = Refinement::new(switch_ty.sty.clone(), PredicateConjunction::from_expr(expr));
                    base_lqt.refine(discr_local, refinement);
                } else {
                    // otherwise discr is not equal to any of values
                    values.iter().for_each(|&v| {
                        let expr = Expr::BinaryOp(BinOp::Ne, box Expr::V, box Expr::Const(Const::Int { size: value_size, bits: v }));
                        let refinement = Refinement::new(switch_ty.sty.clone(), PredicateConjunction::from_expr(expr));
                        base_lqt.refine(discr_local.clone(), refinement);
                    });
                };
                base_lqt
            }
            TerminatorKind::Call { ref func, ref args, ref destination, cleanup, from_hir_call } => {
                if let Some((ref dst, target)) = *destination {
                    // TODO: may be target_block == cleanup
                    assert_eq!(target_block, target);
                    if let Operand::Constant(box Constant { ty: TyS { sty: TyKind::FnDef(func_def, _), .. }, .. }) = func {
                        let (pre, post) = self.function_refinement(*func_def);
                        base_lqt.refine(dst.clone(), post);
                        // need to precondition refinements for arguments and postcondition refinements for destination
                        unimplemented!();
                        base_lqt
                    } else {
                        unreachable!()
                    }
                } else {
                    unimplemented!()
                }
            }
            TerminatorKind::Assert { ref cond, expected, ref msg, target, cleanup } => {
                let local = self.place_from_operand(&cond).clone();
                let expr = if target == target_block {
                    Expr::BinaryOp(BinOp::Eq, box Expr::V, box Expr::Const(Const::Bool(expected)))
                } else if let Some(target) = cleanup {
                    assert_eq!(target, target_block);
                    Expr::BinaryOp(BinOp::Ne, box Expr::V, box Expr::Const(Const::Bool(expected)))
                } else {
                    unreachable!()
                };
                let pred = PredicateConjunction::from_expr(expr);
                let refinement = Refinement::new(TyKind::Bool, pred);
                base_lqt.refine(local, refinement);
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
        }
    }

    /// Calculate basic block lqt without terminator analysis
    fn get_basic_block_base_lqt(&self, current_block: BasicBlock) -> InferenceCtx<'tcx> {
        let predecessors = self.mir.predecessors_for(current_block);
        let pred_lqt: Vec<_> = if predecessors.is_empty() {
            self.precondition.clone()
        } else {
            predecessors
                // TODO: parallelize
                .iter()
                .map(|&bb| self.get_basic_block_lqt_for_target(bb, current_block))
                .collect_vec()
        };
        let ctx = self.calculate_strongest_conjunction(pred_lqt);

        self.infer_block_lqt(current_block, ctx)
    }

    /// Get function pre and postconditions
    fn function_refinement(&self, func_id: DefId) -> (Refinement<'tcx>, Refinement<'tcx>) {
        unimplemented!("function ")
    }

    /// Infer lqt of rvalue in cxt
    fn infer_lqt(&self, v: &Rvalue<'tcx>, ctx: &InferenceCtx<'tcx>) -> Refinement<'tcx> {
        match *v {
            // simple assign one value to another, no less no more
            Rvalue::Use(ref oprnd) => {
                match oprnd {
                    Operand::Copy(ref p) | Operand::Move(ref p) => {
                        ctx.place_refinement(p)
                    }
                    Operand::Constant(box Constant { literal: RustConst { val, .. }, .. }) => {
                        unimplemented!("constant assign")
                    }
                }
            }
            Rvalue::Repeat(_, _) => unimplemented!("array literal"),
            Rvalue::Ref(_, _, _) => unimplemented!("reference"),
            Rvalue::Len(_) => unimplemented!("rvalue len"),
            Rvalue::Cast(_, _, _) => unimplemented!("cast"),
            Rvalue::BinaryOp(op, ref lhs, ref rhs) => {
                let oper = Expr::BinaryOp(op.into(), box lhs.clone().into(), box rhs.clone().into());
                let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box oper);
                let pred = PredicateConjunction::from_expr(expr);
                let lhs_ty = lhs.ty(self.mir.local_decls(), self.tcx);
                let rhs_ty = rhs.ty(self.mir.local_decls(), self.tcx);
                Refinement::new(op.ty(self.tcx, lhs_ty, rhs_ty).sty.clone(), pred)
            }
            Rvalue::CheckedBinaryOp(_, _, _) => unimplemented!("checked binop"),
            Rvalue::NullaryOp(op, rhs) => {
                unimplemented!("nullary op")
            }
            Rvalue::UnaryOp(op, ref rhs) => {
                let oper = Expr::UnaryOp(op.into(), box rhs.clone().into());
                let expr = Expr::BinaryOp(BinOp::Eq, box Expr::V, box oper);
                let pred = PredicateConjunction::from_expr(expr);
                let rhs_ty = rhs.ty(self.mir.local_decls(), self.tcx);
                let op_ty = match op {
                    UnOp::Not => &self.tcx.types.bool.sty,
                    UnOp::Neg => {
                        &rhs.ty(self.mir.local_decls(), self.tcx).sty
                    }
                };
                Refinement::new(op_ty.clone(), pred)
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
        let ty = arg.ty.sty.clone();
        self.type_annotations.get(name.get()).cloned().unwrap_or_else(|| Refinement::unknown(ty))
    }

    fn get_return_refinement(&self, _: &LocalDecl) -> Refinement {
        let ty = self.mir.return_ty().sty.clone();
        self.type_annotations.get(ANN_RET_NAME).cloned().unwrap_or_else(|| Refinement::unknown(ty))
    }

    fn get_tmp_refinement(&self, arg: &LocalDecl<'tcx>) -> Refinement<'tcx> {
        let ty = arg.ty.sty.clone();
        Refinement::unknown(ty)
    }

    /// let x: Foo = bar;
    fn get_var_refinement(&self, arg: &LocalDecl<'tcx>) -> Refinement<'tcx> {
        // TODO: handle user provided type
        let ty = arg.ty.sty.clone();
        Refinement::unknown(ty)
    }

    fn assign_init_refinements(&self) -> IndexVec<Local, Refinement> {
        let locals = self.mir.local_decls();
        let mut res = IndexVec::with_capacity(locals.len());
        for (idx, local) in locals.iter_enumerated() {
            let refinement = match self.mir.local_kind(idx) {
                LocalKind::Arg => self.get_argument_refinement(local),
                LocalKind::ReturnPointer => self.get_return_refinement(local),
                LocalKind::Var => self.get_var_refinement(local),
                LocalKind::Temp => self.get_tmp_refinement(local)
            };
            let mut refinement = Some(refinement);
            // we produce just one item from closure, so unwrap never called on None
            res.ensure_contains_elem(idx, move || refinement.take().unwrap());
        }
        res
    }
}
