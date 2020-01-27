use rustproof_libsmt::{
    backends::{
        smtlib2::SMTLib2,
        backend::SMTBackend
    },
    logics::lia::{LIA, LIA_Sorts, LIA_Fn},
    theories::{core, integer}
};
use std::collections::HashMap;
use crate::{
    expr::{Expr, Const, UnaryOp, BinOp},
    refinable_entity::RefinableEntity,
    refined_type::Predicate
};
use rustc::ty::TyKind;

type Solver = SMTLib2<LIA>;
type Names<'tcx, 'e> = HashMap<RefinableEntity<'tcx>, <Solver as SMTBackend>::Idx>;

fn smt_from_const(
    s: &mut Solver,
    _const: &Const,
) -> <Solver as SMTBackend>::Idx {
    match _const {
        Const::Bool(value) => s.new_const(core::OpCodes::Const(*value)),
        value @ Const::Int { .. } | value @ Const::UInt { .. } => s.new_const(integer::OpCodes::Const(value.try_to_i64().unwrap())),
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
        },
        Predicate::Conj(preds) => {
            let smt_preds = preds
                .into_iter()
                .map(|p| smt_from_pred(s, names, p))
                .collect::<Vec<_>>();
            s.assert(core::OpCodes::And, &smt_preds)
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