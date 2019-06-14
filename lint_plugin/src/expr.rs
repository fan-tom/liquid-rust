use rustc::mir::{self, Operand, Local};

#[derive(Clone, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Lt,
    Le,
    Eq,
    Gt,
    Ge,
    Ne,
    // for enum variant
    Is
}

#[derive(Clone, Debug)]
pub enum UnaryOp {
    // !<bool> or !<bits>
    Not,
    // -
    Neg
}

#[derive(Clone, Debug)]
pub enum Const {
    Bool(bool),
    Int {
        size: u8,
        bits: u128,
    },
    UInt {
        size: u8,
        bits: u128,
    }
}

impl From<mir::BinOp> for BinOp {
    fn from(op: mir::BinOp) -> Self {
        match op {
            mir::BinOp::Add => BinOp::Add,
            mir::BinOp::Sub => BinOp::Sub,
            mir::BinOp::Mul => BinOp::Mul,
            mir::BinOp::Div => BinOp::Div,
            _ => unimplemented!(),
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
pub enum Predicate {
    Const(Const),
    Rel(Expr)
}

#[derive(Clone, Debug)]
pub enum Expr {
    V,
    Var(Local),
    Const(Const),
    UnaryOp(UnaryOp, Box<Expr>),
    BinaryOp(BinOp, Box<Expr>, Box<Expr>)
}

impl Expr {
    pub fn r#true() -> Self {
        Expr::Const(Const::Bool(true))
    }

}

impl<'tcx> From<Operand<'tcx>> for Expr {
    fn from(op: Operand) -> Self {
        match op {
            Operand::Copy(e) | Operand::Move(e) => {
                unimplemented!()
            },
            Operand::Constant(_) => unimplemented!()
        }
    }
}

//impl TryFrom