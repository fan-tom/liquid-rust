use rustc::{
    mir::{self, Local, Operand, Place},
    ty::{TyKind, Const as RustConst},
};
use rustc::mir::Constant;
use rustc_target::abi::Size;
use derive_more::*;
use crate::refinable_entity::RefinableEntity;
use rustc::hir::def_id::DefId;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Display)]
pub enum BinOp {
    #[display(fmt = "+")]
    Add,
    #[display(fmt = "_")]
    Sub,
    #[display(fmt = "*")]
    Mul,
    #[display(fmt = "/")]
    Div,
    #[display(fmt = "<")]
    Lt,
    #[display(fmt = "<=")]
    Le,
    #[display(fmt = "=")]
    Eq,
    #[display(fmt = ">")]
    Gt,
    #[display(fmt = ">=")]
    Ge,
    // used only to convert from mir::BinOp, transformed to Expr::UnaryOp(Not, Expr::BinaryOp(Eq, ...
    #[display(fmt = "!=")]
    Ne,
    // for enum variant
    #[display(fmt = "is")]
    Is,
    // to be used only in annotations
    #[display(fmt = "=>")]
    Imp,
    // is it the same as Eq?
    #[display(fmt = "<=>")]
    Equiv,
    #[display(fmt = "||")]
    Or,
    #[display(fmt = "&&")]
    And,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Display)]
pub enum UnaryOp {
    // !<bool> or !<bits>
    #[display(fmt = "!")]
    Not,
    // -
    #[display(fmt = "-")]
    Neg,
}

#[derive(Clone, Debug, Eq, PartialEq, Display)]
pub enum Const {
    #[display(fmt = "{}", _0)]
    Bool(bool),
    #[display(fmt = "{}", r#"self.try_to_i64().map(|n| n.to_string()).unwrap_or(format!("<{}>({} bits)", bits, size))"#)]
    Int {
        // size in bits
        size: u64,
        bits: u128,
    },
    #[display(fmt = "{}", r#"self.try_to_i64().map(|n| n.to_string()).unwrap_or(format!("<{}>({} bits)", bits, size))"#)]
    UInt {
        // size in bits
        size: u64,
        bits: u128,
    },
}

impl Const {
    pub fn try_to_i64(&self) -> Option<i64> {
        match self {
            Const::Int { size, bits } => {
                Some(
                    if size <= &8 {
                        (*bits as i8) as i64
                    } else if size <= &16 {
                        (*bits as i16) as i64
                    } else if size <= &32 {
                        (*bits as i32) as i64
                    } else if size <= &64 {
                        *bits as i64
                    } else {
                        None?
                    }
                )
            },
            Const::UInt { size, bits } if size < &64 => {
                Some(*bits as i64)
            },
            _ => None,
        }
    }
}

impl From<mir::BinOp> for BinOp {
    fn from(op: mir::BinOp) -> Self {
        match op {
            mir::BinOp::Add => BinOp::Add,
            mir::BinOp::Sub => BinOp::Sub,
            mir::BinOp::Mul => BinOp::Mul,
            mir::BinOp::Div => BinOp::Div,
            mir::BinOp::Lt => BinOp::Lt,
            mir::BinOp::Gt => BinOp::Gt,
            mir::BinOp::Ne => BinOp::Ne,
            mir::BinOp::Ge => BinOp::Ge,
            mir::BinOp::Eq => BinOp::Eq,
            mir::BinOp::Le => BinOp::Le,
            o => unimplemented!("{:?}", o),
        }
    }
}

impl From<mir::UnOp> for UnaryOp {
    fn from(op: mir::UnOp) -> Self {
        match op {
            mir::UnOp::Neg => UnaryOp::Neg,
            mir::UnOp::Not => UnaryOp::Not,
        }
    }
}

/// Not used yet
pub enum Predicate<'tcx> {
    Const(Const),
    Rel(Expr<'tcx>),
}

#[derive(Clone, Debug, Eq, PartialEq, Display)]
pub enum Expr<'tcx> {
    #[display(fmt = "v")]
    V,
    #[display(fmt = "{:?}", _0)]
    Var(RefinableEntity<'tcx>),
    #[display(fmt = "{}", _0)]
    Const(Const),
    #[display(fmt = "{} {}", _0, _1)]
    UnaryOp(UnaryOp, Box<Expr<'tcx>>),
    #[display(fmt = "{} {} {}", _1, _0, _2)]
    BinaryOp(BinOp, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
}

impl<'tcx> Expr<'tcx> {
    pub fn r#true() -> Self {
        Expr::Const(Const::Bool(true))
    }

    pub fn binary_op(op: BinOp, lhs: Expr<'tcx>, rhs: Expr<'tcx>) -> Self {
        if op == BinOp::Ne {
            Expr::UnaryOp(UnaryOp::Not, box Expr::binary_op(BinOp::Eq, lhs, rhs))
        } else {
            Expr::BinaryOp(op, box lhs, box rhs)
        }
    }

    pub fn from_place(place: Place<'tcx>, fun_id: DefId) -> Self {
        Self::Var(RefinableEntity::from_place(place, fun_id))
    }

    pub fn from_operand(op: Operand<'tcx>, fun_id: DefId) -> Self {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                Expr::from_place(place, fun_id)
            }
            Operand::Constant(c) => c.literal.into()
        }
    }
}

//impl<'tcx> From<Operand<'tcx>> for Expr<'tcx> {
//    fn from(op: Operand<'tcx>) -> Self {
//        match op {
//            Operand::Copy(e) | Operand::Move(e) => {
//                Expr::Var(e)
//            }
//            Operand::Constant(c) => c.literal.into()
//        }
//    }
//}

impl From<&RustConst<'_>> for Expr<'_> {
    fn from(c: &RustConst) -> Self {
        let cnst = match &c.ty.kind {
            TyKind::Bool => Const::Bool(c.val.try_to_scalar().unwrap().to_bool().unwrap()),
            TyKind::Uint(ty) => {
                let size = Size::from_bits(ty.bit_width().unwrap() as u64);
                let bits = c.val.try_to_bits(size).unwrap();
                Const::Int { bits, size: size.bits() }
            }
            TyKind::Int(ty) => {
                let size = Size::from_bits(ty.bit_width().unwrap() as u64);
                let bits = c.val.try_to_bits(size).unwrap();
                Const::Int { bits, size: size.bits() }
            }
            t => unimplemented!("{:?}", t)
        };
        Expr::Const(cnst)
    }
}

mod visitor {
    use crate::visitor::{Visitable, Visitor};
    use super::*;

    impl Visitable for Expr<'_> {
        fn accept<'s>(&'s self, v: &mut impl Visitor<'s, Self>) {
            match self {
                Expr::UnaryOp(_, expr) => expr.accept(v),
                Expr::BinaryOp(_, lhs, rhs) => {
                    lhs.accept(v);
                    rhs.accept(v);
                },
                _ => {}
            }
            v.visit(self);
        }
    }
}

mod folder {
    use crate::folder::{Foldable, Folder};
    use super::*;

    impl<'tcx> Foldable for Expr<'tcx> {
        fn accept(self, v: &mut impl Folder<Self>) -> Expr<'tcx> {
            let self_folded = match self {
                Expr::UnaryOp(op, expr) => Expr::UnaryOp(op, box expr.accept(v)),
                Expr::BinaryOp(op, lhs, rhs) => Expr::BinaryOp(
                    op,
                    box lhs.accept(v),
                    box rhs.accept(v)),
                e => e,
            };
            v.fold(self_folded)
        }
    }
}