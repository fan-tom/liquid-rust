use crate::restriction_expr::{Const as RestrictionConst, Expr as RestrictionExpr};
use crate::expr::{UnaryOp, Const, BinOp, Expr};
use rustc::mir::Body;
use rustc::hir::def_id::DefId;
use crate::restriction_expr::fold::Folder;
use crate::typable::{Ty, Typer, Typable};

pub struct RestrictionToExprConverter<'tcx, 'name, T: Typer<'tcx>> {
    pub mir: &'tcx Body<'tcx>,
    pub name: &'name str,
    pub fun_id: DefId,
    pub typer: T,
}

impl<'e, 'tcx, T: Typer<'tcx>> Folder<'e, Result<Expr<'tcx>, failure::Error>> for RestrictionToExprConverter<'tcx, '_, T> {
    fn fold_v(&mut self) -> Result<Expr<'tcx>, failure::Error> {
        Ok(Expr::V)
    }

    fn fold_var(&mut self, var: &'e str) -> Result<Expr<'tcx>, failure::Error> {
        if var == self.name {
            Ok(Expr::V)
        } else if let Some(place) = self.mir.args_iter().find_map(|l| {
            if let Some(name) = self.mir.local_decls[l].name {
                if name.as_str() == var {
                    Some(l.into())
                } else {
                    None
                }
            } else {
                None
            }
        }) {
            Ok(Expr::from_place(place, self.fun_id))
        } else {
            Err(failure::format_err!("Unknown variable {}", var))
        }
    }

    fn fold_const(&mut self, _const: &'e RestrictionConst, ty: Option<Ty>) -> Result<Expr<'tcx>, failure::Error> {
        match _const {
            RestrictionConst::Bool(v) => Ok(Expr::Const(Const::Bool(*v))),
            RestrictionConst::Int(v) => {
                Ok(match ty {
                    Some(Ty::UInt(size)) => {
                        assert!(*v >= 0, "{:?} for negative const {}", ty, v);
                        Expr::Const(Const::UInt {
                            size: size as u64,
                            bits: *v as u128
                        })
                    },
                    Some(Ty::Int(size)) => {
                        let expr = Expr::Const(
                            Const::Int {
                                size: size as u64,
                                bits: *v as u128
                            }
                        );
                        if *v < 0 {
                            Expr::UnaryOp(UnaryOp::Neg, box expr)
                        } else {
                            expr
                        }
                    },
                    _ => panic!("Cannot convert {}: expected number Ty, found {:?}", _const, ty)
                })
            }
        }
    }

    fn fold_unary_op(&mut self, op: UnaryOp, expr: &'e RestrictionExpr) -> Result<Expr<'tcx>, failure::Error> {
        Ok(Expr::UnaryOp(op, box expr.fold(self)?))
    }

    fn fold_binary_op(&mut self, op: BinOp, lhs: &'e RestrictionExpr, rhs: &'e RestrictionExpr) -> Result<Expr<'tcx>, failure::Error> {
        let (new_lhs, new_rhs) = if let RestrictionExpr::Const(c) = lhs {
            let new_rhs = rhs.fold(self)?;
            (self.fold_const(c, new_rhs.ty(&self.typer))?, new_rhs)
        } else if let RestrictionExpr::Const(c) = rhs {
            let new_lhs = lhs.fold(self)?;
            let lhs_ty = new_lhs.ty(&self.typer);
            (new_lhs, self.fold_const(c, lhs_ty)?)
        } else {
            (lhs.fold(self)?, rhs.fold(self)?)
        };
        Ok(Expr::BinaryOp(op, box new_lhs, box new_rhs))
    }
}