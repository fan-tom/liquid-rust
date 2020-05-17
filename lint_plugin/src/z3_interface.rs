use std::{
    collections::{
        hash_map::RandomState,
        HashMap,
    }
};

use failure::_core::hint::unreachable_unchecked;
use rustc::ty::TyKind;
use rustproof_libsmt::{
    backends::{
        backend::{
            SMTBackend,
            Logic,
        },
        smtlib2::SMTLib2,
    },
    logics::{
        lia::{LIA, LIA_Fn, LIA_Sorts},
        qf_aufbv::*,
    },
    theories::{bitvec, core, integer},
};

use crate::{
    expr::{BinOp, Const, Expr, UnaryOp},
    refinable_entity::RefinableEntity,
    refined_type::Predicate,
    to_smt::{Decls, DefaultSmtConverterCtx, SmtConverterCtx, SMTIdx, ToSmt},
    typable::{Ty, Typable, Typer},
};
use crate::utils::IntoFish;
use rustc::ty::layout::MaybeResult;

type Solver = SMTLib2<LIA>;
type Names<'tcx, 'e> = HashMap<RefinableEntity<'tcx>, <Solver as SMTBackend>::Idx>;

impl<'tcx, C: SmtConverterCtx<'tcx, QF_AUFBV>> ToSmt<'tcx, QF_AUFBV, C> for Const {
    type Output = SMTIdx<QF_AUFBV>;
    fn to_smt(&self, ctx: &mut C) -> Option<Self::Output> {
        Some(if let Const::Bool(value) = self {
            ctx.new_const(core::OpCodes::Const(*value))
        } else {
            // TODO: think about how to avoid double match
            let bits = self.try_to_u64().expect(&format!("Cannot get bits of {:?}", self));
            match self {
                Const::Int { size, .. } | Const::UInt { size, .. } => ctx.new_const(bitvec::OpCodes::Const(bits, *size as usize)),
                _ => unsafe { unreachable_unchecked() }
            }
        })
    }
}

impl<'tcx, C: SmtConverterCtx<'tcx, LIA>> ToSmt<'tcx, LIA, C> for Const {
    type Output = SMTIdx<LIA>;
    fn to_smt(&self, ctx: &mut C) -> Option<Self::Output> {
        if let Const::Bool(value) = self {
            ctx.new_const(core::OpCodes::Const(*value))
        } else {
            let bits = self.try_to_i64().unwrap();
            match self {
                Const::Int { size, .. } | Const::UInt { size, .. } => ctx.new_const(integer::OpCodes::Const(bits)),
                _ => unsafe { unreachable_unchecked() }
            }
        }.into()
    }
}

fn smt_from_const(
    s: &mut Solver,
    _const: &Const,
) -> <Solver as SMTBackend>::Idx {
    match _const {
        Const::Bool(value) => s.new_const(core::OpCodes::Const(*value)),
        value @ Const::Int { .. } | value @ Const::UInt { .. } => s.new_const(integer::OpCodes::Const(value.try_to_i64().unwrap())),
    }
}

impl<'tcx, C: SmtConverterCtx<'tcx, QF_AUFBV>> ToSmt<'tcx, QF_AUFBV, C> for TyKind<'_> {
    type Output = QF_AUFBV_Sorts;
    fn to_smt(&self, _: &mut C) -> Option<Self::Output> {
        match self {
            TyKind::Bool => Some(core::Sorts::Bool.into()),
            TyKind::Int(v) => v.bit_width().map(|w| bitvec::Sorts::BitVector(w).into()),
            TyKind::Uint(v) =>
            // TODO: handle isize and usize, currently they return None
                v.bit_width().map(|w| bitvec::Sorts::BitVector(w).into()),
            _ => {
                return None;
            }
        }
    }
}

impl<'tcx, C: SmtConverterCtx<'tcx, LIA>> ToSmt<'tcx, LIA, C> for TyKind<'_> {
    type Output = LIA_Sorts;
    fn to_smt(&self, _: &mut C) -> Option<Self::Output> {
        Some(match self {
            TyKind::Bool => core::Sorts::Bool.into(),
            TyKind::Int(_) | TyKind::Uint(_) => integer::Sorts::Int.into(),
            _ => return None
        })
    }
}

pub fn sort_from_ty(ty: &TyKind) -> Option<LIA_Sorts> {
    let sort: LIA_Sorts = match ty {
//        explicit::Type::TBool => core::Sorts::Bool.into(),
        TyKind::Bool => core::Sorts::Bool.into(),
//        explicit::Type::TInt => integer::Sorts::Int.into(),
        TyKind::Int(_) | TyKind::Uint(_) => integer::Sorts::Int.into(),
        _ => {
            return None;
        }
//        TyKind::Float(_) => {},
//        TyKind::Char => {},
//        TyKind::Adt(_, _) => {},
//        TyKind::Foreign(_) => {},
//        TyKind::Str => {},
//        TyKind::Array(_, _) => {},
//        TyKind::Slice(_) => {},
//        TyKind::RawPtr(_) => {},
//        TyKind::Ref(_, _, _) => {},
//        TyKind::FnDef(_, _) => {},
//        TyKind::FnPtr(_) => {},
//        TyKind::Dynamic(_, _) => {},
//        TyKind::Closure(_, _) => {},
//        TyKind::Generator(_, _, _) => {},
//        TyKind::GeneratorWitness(_) => {},
//        TyKind::Never => {},
//        TyKind::Tuple(_) => {},
//        TyKind::Projection(_) => {},
//        TyKind::UnnormalizedProjection(_) => {},
//        TyKind::Opaque(_, _) => {},
//        TyKind::Param(_) => {},
//        TyKind::Bound(_, _) => {},
//        TyKind::Placeholder(_) => {},
//        TyKind::Infer(_) => {},
//        TyKind::Error => {},
    };
    Some(sort)
}

impl<'tcx, L: Logic, C: SmtConverterCtx<'tcx, L>> ToSmt<'tcx, L, C> for RefinableEntity<'tcx> {
    type Output = SMTIdx<L>;
    fn to_smt(&self, ctx: &mut C) -> Option<Self::Output> {
        ctx.get_name(self)
        // TODO: fix that shit
           .expect(&format!("Unknown variable to convert into SMT {:?}", self))
           .into()
    }
}

fn smt_from_var(
    s: &mut Solver,
    names: &Names,
    ref_entity: &RefinableEntity,
) -> <Solver as SMTBackend>::Idx {
    *names.get(ref_entity).ok_or(failure::format_err!("Unknown variable {:?}", ref_entity)).unwrap()
//    match place.base {
//        PlaceBase::Local(local) => {
//            let name = names.get(local);
//            s.new_var(
//                Some(name),
//                sort_from_ty(&decl.ty.kind).expect("Unexpected type"),
//            )
//        },
//        PlaceBase::Static(_) => { unimplemented!() },
//    }
}

fn smt_from_op(
    s: &mut Solver,
    names: &Names,
    op: UnaryOp,
//    vars: &HashMap<String, <Solver as SMTBackend>::Idx>,
    expr: &Expr) -> <Solver as SMTBackend>::Idx {

//    use lambdal::Op as O;
//    use common::Op2;

    let expr = &[smt_from_expr(s, names, expr)];

    match op {
        UnaryOp::Not => s.assert(core::OpCodes::Not, expr),
        UnaryOp::Neg => s.assert(integer::OpCodes::Neg, expr),
    }
}

fn smt_from_binop(
    s: &mut Solver,
    names: &Names,
    op: BinOp,
    lhs: &Expr,
    rhs: &Expr,
) -> <Solver as SMTBackend>::Idx {
    let lhs = smt_from_expr(s, names, lhs);
    let rhs = smt_from_expr(s, names, rhs);
    let opcode: LIA_Fn = match op {
        BinOp::And => core::OpCodes::And.into(),
        BinOp::Or => core::OpCodes::Or.into(),
        BinOp::Imp => core::OpCodes::Imply.into(),
        BinOp::Equiv => core::OpCodes::Cmp.into(),
        BinOp::Lt => integer::OpCodes::Lt.into(),
        BinOp::Le => integer::OpCodes::Lte.into(),
        BinOp::Gt => integer::OpCodes::Gt.into(),
        BinOp::Ge => integer::OpCodes::Gte.into(),
        BinOp::Eq => integer::OpCodes::Cmp.into(),
        BinOp::Add => integer::OpCodes::Add.into(),
        BinOp::Sub => integer::OpCodes::Sub.into(),
        BinOp::Mul => integer::OpCodes::Mul.into(),
        BinOp::Div => integer::OpCodes::Div.into(),
        op => unimplemented!("{}", op),
    };
    s.assert(opcode, &[lhs, rhs])
}

impl<'tcx, C: SmtConverterCtx<'tcx, QF_AUFBV> + Typer<'tcx>> ToSmt<'tcx, QF_AUFBV, C> for Predicate<'tcx> {
    type Output = SMTIdx<QF_AUFBV>;
    fn to_smt(&self, ctx: &mut C) -> Option<Self::Output> {
        match self {
            Predicate::Basic(expr) => expr.to_smt(ctx)?,
            Predicate::Not(box pred) => {
                let smt_pred = pred.to_smt(ctx)?;
                ctx.assert(core::OpCodes::Not, &[smt_pred])
            }
            Predicate::Conj(preds) => {
                let smt_preds = preds
                    .into_iter()
                    .map(|p| p.to_smt(ctx))
                    .collect::<Option<Vec<_>>>()?;
                ctx.assert(core::OpCodes::And, &smt_preds)
            }
        }.into()
    }
}

impl<'tcx, C: SmtConverterCtx<'tcx, LIA> + Typer<'tcx>> ToSmt<'tcx, LIA, C> for Predicate<'tcx> {
    type Output = SMTIdx<LIA>;
    fn to_smt(&self, ctx: &mut C) -> Option<Self::Output> {
        match self {
            Predicate::Basic(expr) => expr.to_smt(ctx),
            Predicate::Not(box pred) => {
                let smt_pred = pred.to_smt(ctx)?;
                ctx.assert(core::OpCodes::Not, &[smt_pred]).into()
            }
            Predicate::Conj(preds) => {
                let smt_preds = preds
                    .into_iter()
                    .map(|p| p.to_smt(ctx))
                    .collect::<Option<Vec<_>>>()?;
                ctx.assert(core::OpCodes::And, &smt_preds).into()
            }
        }
    }
}

pub fn smt_from_pred(
    s: &mut Solver,
    // TODO: maybe convert to appropriate format
    // before to not pass mir so deep
    names: &Names,
    pred: &Predicate) -> <Solver as SMTBackend>::Idx {
    match pred {
        Predicate::Basic(expr) => smt_from_expr(s, names, expr),
        Predicate::Not(box pred) => {
            let smt_pred = smt_from_pred(s, names, pred);
            s.assert(core::OpCodes::Not, &[smt_pred])
        }
        Predicate::Conj(preds) => {
            let smt_preds = preds
                .into_iter()
                .map(|p| smt_from_pred(s, names, p))
                .collect::<Vec<_>>();
            s.assert(core::OpCodes::And, &smt_preds)
        }
    }
}

impl<'tcx, C: SmtConverterCtx<'tcx, QF_AUFBV> + Typer<'tcx>> ToSmt<'tcx, QF_AUFBV, C> for Expr<'tcx> {
    type Output = SMTIdx<QF_AUFBV>;
    fn to_smt(&self, ctx: &mut C) -> Option<Self::Output> {
        use Expr as E;
        match self {
            E::V => None,
            E::Const(_const) => _const.to_smt(ctx),
            E::Var(ref_entity) => ref_entity.to_smt(ctx),
            E::UnaryOp(op, expr) => {
                let exprs = &[expr.to_smt(ctx)?];

                match op {
                    UnaryOp::Not => ctx.assert(core::OpCodes::Not, exprs),
                    UnaryOp::Neg => ctx.assert(bitvec::OpCodes::BvNeg, exprs),
                }.into()
            }
            E::BinaryOp(op, lhs, rhs) => {
                let lhs_idx = lhs.to_smt(ctx)?;
                let rhs_idx = rhs.to_smt(ctx)?;
                let opcode: QF_AUFBV_Fn = match op {
                    BinOp::And => core::OpCodes::And.into(),
                    BinOp::Or => core::OpCodes::Or.into(),
                    BinOp::Imp => core::OpCodes::Imply.into(),
                    BinOp::Equiv => core::OpCodes::Cmp.into(),
                    BinOp::Add => bitvec::OpCodes::BvAdd.into(),
                    BinOp::Sub => bitvec::OpCodes::BvSub.into(),
                    op => {
                        let ty = lhs.ty(ctx).expect(&format!("Expected one of Ty::Int, UInt, Bool, got {}", lhs));
                        match ty {
                            Ty::UInt(size) => {
                                match op {
                                    BinOp::Eq => {
                                        let lhs_cmp = ctx.assert(bitvec::OpCodes::BvComp.to::<QF_AUFBV_Fn>(), &[lhs_idx, rhs_idx]);
                                        let tru = ctx.new_const(bitvec::OpCodes::Const(1, 1));
                                        println!("Emitting uint bvcomp: {} === {}", lhs, rhs);
                                        return Some(ctx.assert(core::OpCodes::Cmp.to::<QF_AUFBV_Fn>(), &[lhs_cmp, tru]));
                                    }
                                    BinOp::Lt => bitvec::OpCodes::BvULt.into(),
                                    BinOp::Le => bitvec::OpCodes::BvULe.into(),
                                    BinOp::Gt => bitvec::OpCodes::BvUGt.into(),
                                    BinOp::Ge => bitvec::OpCodes::BvUGe.into(),
                                    BinOp::Mul => bitvec::OpCodes::BvMul.into(),
                                    BinOp::Div => bitvec::OpCodes::BvUDiv.into(),
                                    BinOp::MulOverflows => {
                                        let arg = ctx.assert(bitvec::OpCodes::BvUMulDoesNotOverflow, &[lhs_idx, rhs_idx]);
                                        return Some(ctx.assert(core::OpCodes::Not, &[arg]));
                                    }
                                    BinOp::AddOverflows => core::OpCodes::Fun(format!("bvu{}add_overflows", size)).into(),
                                    BinOp::SubOverflows => core::OpCodes::Fun(format!("bvu{}sub_overflows", size)).into(),

                                    _ => unimplemented!("{}", op),
                                }
                            }
                            Ty::Int(size) => {
                                match op {
                                    BinOp::Eq => {
                                        let lhs_cmp = ctx.assert(bitvec::OpCodes::BvComp.into(): QF_AUFBV_Fn, &[lhs_idx, rhs_idx]);
                                        let tru = ctx.new_const(bitvec::OpCodes::Const(1, 1));
                                        println!("Emitting int bvcomp: {} === {}", lhs, rhs);
                                        return Some(ctx.assert(core::OpCodes::Cmp.into(): QF_AUFBV_Fn, &[lhs_cmp, tru]));
                                    }
                                    BinOp::Lt => bitvec::OpCodes::BvSLt.into(),
                                    BinOp::Le => bitvec::OpCodes::BvSLe.into(),
                                    BinOp::Gt => bitvec::OpCodes::BvSGt.into(),
                                    BinOp::Ge => bitvec::OpCodes::BvSGe.into(),
                                    BinOp::Mul => bitvec::OpCodes::BvMul.into(),
                                    BinOp::Div => bitvec::OpCodes::BvSDiv.into(),
                                    // TODO: what about underflow?
                                    BinOp::MulOverflows => {
                                        let arg = ctx.assert(bitvec::OpCodes::BvSMulDoesNotOverflow, &[lhs_idx, rhs_idx]);
                                        return Some(ctx.assert(core::OpCodes::Not, &[arg]));
                                    }
                                    BinOp::AddOverflows => core::OpCodes::Fun(format!("bvs{}add_overflows", size)).into(),
                                    BinOp::SubOverflows => core::OpCodes::Fun(format!("bvs{}sub_overflows", size)).into(),
                                    _ => unimplemented!("{}", op),
                                }
                            }
                            Ty::Bool => {
                                if op == &BinOp::Eq {
                                    println!("Emitting Core::Cmp");
                                    core::OpCodes::Cmp.into()
                                } else {
                                    panic!("Expected Bool type and Eq, got {} and {}", lhs, op)
                                }
                            }
                        }
                    }
                };
                ctx.assert(opcode, &[lhs_idx, rhs_idx]).into()
            }
        }
    }
}

impl<'tcx, C: SmtConverterCtx<'tcx, LIA> + Typer<'tcx>> ToSmt<'tcx, LIA, C> for Expr<'tcx> {
    type Output = SMTIdx<LIA>;
    fn to_smt(&self, ctx: &mut C) -> Option<Self::Output> {
        use Expr as E;
        match self {
            E::V => None,
            E::Const(_const) => _const.to_smt(ctx),
            E::Var(ref_entity) => ref_entity.to_smt(ctx),
            E::UnaryOp(op, expr) => {
                let exprs = &[expr.to_smt(ctx)?];

                match op {
                    UnaryOp::Not => ctx.assert(core::OpCodes::Not, exprs),
                    UnaryOp::Neg => ctx.assert(integer::OpCodes::Neg, exprs),
                }.into()
            }
            E::BinaryOp(op, lhs, rhs) => {
                let lhs_idx = lhs.to_smt(ctx)?;
                let rhs_idx = rhs.to_smt(ctx)?;
                let opcode: LIA_Fn = match op {
                    BinOp::And => core::OpCodes::And.into(),
                    BinOp::Or => core::OpCodes::Or.into(),
                    BinOp::Imp => core::OpCodes::Imply.into(),
                    BinOp::Equiv => core::OpCodes::Cmp.into(),
                    BinOp::Eq => core::OpCodes::Cmp.into(),
                    BinOp::Add => integer::OpCodes::Add.into(),
                    BinOp::Sub => integer::OpCodes::Sub.into(),
                    BinOp::Lt => integer::OpCodes::Lt.into(),
                    BinOp::Le => integer::OpCodes::Lte.into(),
                    BinOp::Gt => integer::OpCodes::Gt.into(),
                    BinOp::Ge => integer::OpCodes::Gte.into(),
                    BinOp::Mul => integer::OpCodes::Mul.into(),
                    BinOp::Div => integer::OpCodes::Div.into(),
                    _ => unimplemented!("{}", op),
                };
                ctx.assert(opcode, &[lhs_idx, rhs_idx]).into()
            }
        }
    }
}

pub fn smt_from_expr(
    s: &mut Solver,
    // TODO: maybe convert to appropriate format
    // before to not pass mir so deep
    names: &Names,
    expr: &Expr) -> <Solver as SMTBackend>::Idx {
    use Expr as E;

    match expr {
        E::V => unimplemented!(),
        E::Const(_const) => smt_from_const(s, _const),
        E::Var(ref_entity) => smt_from_var(s, names, ref_entity),
        E::UnaryOp(op, expr) => smt_from_op(s, names, *op, expr),
        E::BinaryOp(op, lhs, rhs) => smt_from_binop(s, names, *op, lhs, rhs),
//        E::Let(ref id, ref e1, ref e2) => {
//            let id_idx = match vars.get(id) {
//                Some(idx) => *idx,
//                None => panic!("key {} not found in {:?}", id, vars),
//            };
//            let eq_exprs = &[id_idx, smt_from_expr(s, vars, e1)];
//            let _ = s.assert(integer::OpCodes::Cmp, eq_exprs);
//            smt_from_expr(s, vars, e2)
//        }
//        E::App(ref e1, ref e2) => {
//            if **e1 == Imm::Var(String::from("not")) {
//                let exprs = &[smt_from_imm(s, vars, e2)];
//                s.assert(core::OpCodes::Not, exprs)
//            } else {
//                panic!("TODO: only supported app is not");
//            }
//        }
//        E::Op(ref op) => smt_from_op(s, vars, op),
//        _ => {
//            panic!("smt_from_expr unimplemented {:?}", q);
//        }
    }
}

#[test]
fn test_solving_for_model() {
    use z3::*;
//    let _ = env_logger::try_init();
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = ctx.named_int_const("x");
    let y = ctx.named_int_const("y");
    let zero = ctx.from_i64(0);
    let two = ctx.from_i64(2);
    let seven = ctx.from_i64(7);

    let solver = Solver::new(&ctx);
    solver.assert(&x.gt(&y));
    solver.assert(&y.gt(&zero));
    solver.assert(&y.rem(&seven)._eq(&two));
    solver.assert(&x.add(&[&two]).gt(&seven));
    assert!(solver.check());

    let model = solver.get_model();
    let xv = model.eval(&x).unwrap().as_i64().unwrap();
    let yv = model.eval(&y).unwrap().as_i64().unwrap();
    println!("x: {}", xv);
    println!("y: {}", yv);
    assert!(xv > yv);
    assert_eq!(yv % 7, 2);
    assert!(xv + 2 > 7);
}