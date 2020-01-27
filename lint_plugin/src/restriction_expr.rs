pub use crate::expr::{UnaryOp, BinOp, Const, Expr as ParsedExpr};
use derive_more::*;
use crate::visitor::{Visitable, Visitor};

#[derive(Clone, Debug, Eq, PartialEq, Display)]
pub enum Expr {
    #[display(fmt = "v")]
    V,
    #[display(fmt = "{:?}", _0)]
    Var(String),
    #[display(fmt = "{}", _0)]
    Const(Const),
    #[display(fmt = "{} {}", _0, _1)]
    UnaryOp(UnaryOp, Box<Expr>),
    #[display(fmt = "{} {} {}", _1, _0, _2)]
    BinaryOp(BinOp, Box<Expr>, Box<Expr>),
}

impl Visitable for Expr {
    fn accept<'s>(&'s self, v: &mut impl Visitor<'s, Self>) {
        match self {
            Expr::UnaryOp(_, expr) => {
                expr.accept(v)
            },
            Expr::BinaryOp(_, lhs, rhs) => {
                lhs.accept(v);
                rhs.accept(v);
            },
            _ => {}
        }
        v.visit(self)
    }
}

impl Expr {
    pub fn r#true() -> Self {
        Expr::Const(Const::Bool(true))
    }

    pub fn r#false() -> Self {
        Expr::Const(Const::Bool(false))
    }

    pub fn not(e: Expr) -> Self {
        Expr::UnaryOp(UnaryOp::Not, box e)
    }
}

pub mod fold {
    use super::{Expr, UnaryOp, BinOp, Const};
    pub trait Folder<'e, T>
    {
        fn fold_v(&mut self) -> T;
        fn fold_var(&mut self, var: &'e str) -> T;
        fn fold_const(&mut self, _const: &'e Const) -> T;
        fn fold_unary_op(&mut self, op: UnaryOp, expr: &'e Expr) -> T;
        fn fold_binary_op(&mut self, op: BinOp, lhs: &'e Expr, rhs: &'e Expr) -> T;
    }

    impl Expr {
        pub fn fold<'e, T>(&'e self, folder: &mut impl Folder<'e, T>) -> T {
            match self {
                Expr::V => folder.fold_v(),
                Expr::Var(str) => folder.fold_var(str),
                Expr::Const(c) => folder.fold_const(c),
                Expr::UnaryOp(op, expr) => folder.fold_unary_op(*op, expr),
                Expr::BinaryOp(op, lhs, rhs) => folder.fold_binary_op(*op, lhs, rhs)
            }
        }
    }
}

mod walker {
    use super::{Expr, UnaryOp, BinOp, Const};
    pub trait Walker {
        fn walk_v(&mut self) {}
        fn walk_var(&mut self) {}
    }
}
