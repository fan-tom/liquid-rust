use crate::restriction_expr::{Folder, Expr as RestrictionExpr};
use crate::expr::{UnaryOp, Const, BinOp, Expr};
use rustc::mir::Body;
use rustc::hir::def_id::DefId;

pub struct RestrictionToExprConverter<'tcx, 'name>(pub &'tcx Body<'tcx>, pub &'name str, pub DefId);

impl<'e, 'tcx> Folder<'e, Result<Expr<'tcx>, failure::Error>> for RestrictionToExprConverter<'tcx, '_> {
    fn fold_v(&mut self) -> Result<Expr<'tcx>, failure::Error> {
        Ok(Expr::V)
    }

    fn fold_var(&mut self, var: &'e str) -> Result<Expr<'tcx>, failure::Error> {
        if var == self.1 {
            Ok(Expr::V)
        } else if let Some(place) = self.0.args_iter().find_map(|l| {
            if let Some(name) = self.0.local_decls[l].name {
                if name.as_str() == var {
                    Some(l.into())
                } else {
                    None
                }
            } else {
                None
            }
        }) {
            Ok(Expr::from_place(place, self.2))
        } else {
            Err(failure::format_err!("Unknown variable {}", var))
        }
    }

    fn fold_const(&mut self, _const: &'e Const) -> Result<Expr<'tcx>, failure::Error> {
        Ok(Expr::Const(_const.clone()))
    }

    fn fold_unary_op(&mut self, op: UnaryOp, expr: &'e RestrictionExpr) -> Result<Expr<'tcx>, failure::Error> {
        Ok(Expr::UnaryOp(op, box expr.fold(self)?))
    }

    fn fold_binary_op(&mut self, op: BinOp, lhs: &'e RestrictionExpr, rhs: &'e RestrictionExpr) -> Result<Expr<'tcx>, failure::Error> {
        Ok(Expr::BinaryOp(op, box lhs.fold(self)?, box rhs.fold(self)?))
    }
}