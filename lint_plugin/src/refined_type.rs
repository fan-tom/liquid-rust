use std::{
    borrow::Borrow,
    iter::once
};

use derive_more::*;
use failure::err_msg;
use itertools::Itertools;
use rustc::ty::TyKind;

use crate::{
    expr::Expr,
    utils::IntoEither
};

#[derive(Clone, Debug, Eq, PartialEq, Hash, Display)]
pub enum Predicate<'tcx> {
    #[display(fmt = "{}", _0)]
    Basic(Expr<'tcx>),
    #[display(fmt = "not ({})", _0)]
    Not(Box<Predicate<'tcx>>),
    // vector of conjoined boolean expressions
    // /\ expr(v, locals)
    #[display(
    fmt = "({})",
    r#"_0.iter()
            .map(std::string::ToString::to_string)
            .join(r" /\ ")"#
    )]
    Conj(Vec<Predicate<'tcx>>),
}

//#[derive(Clone, Debug, Eq, PartialEq)]
//pub struct PredicateConjunction<'tcx> {
//    negated: bool,
//    // vector of conjoined boolean expressions
//    // /\ expr(v, locals)
//    parts: Vec<PredicateConjunctionPart<'tcx>>,
//}

mod folder {
    use crate::folder::{Foldable, Folder};
    use super::*;

    impl<'tcx> Foldable<Expr<'tcx>> for Predicate<'tcx> {
        fn accept(self, v: &mut impl Folder<Expr<'tcx>>) -> Predicate<'tcx> {
            match self {
                Predicate::Basic(expr) => Predicate::Basic(expr.accept(v)),
                Predicate::Not(box pred) => Predicate::Not(box pred.accept(v)),
                Predicate::Conj(preds) => Predicate::Conj(preds
                    .into_iter()
                    .map(|p| p.accept(v))
                    .collect()
                ),
            }
        }
    }
}
//impl fmt::Display for PredicateConjunction<'_> {
//    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
//        let parts = self.parts
//            .iter()
//            .map(std::string::ToString::to_string)
//            .join(r" /\ ");
//        let res = if self.negated {
//            format!("not ({})", parts)
//        } else {
//            parts
//        };
//        write!(f, "{}", res)
//    }
//}

impl<'tcx> Predicate<'tcx> {
    /// a /\ b /\ c ...
    pub fn from_exprs(exprs: Vec<Expr<'tcx>>) -> Self {
        Predicate::Conj(exprs.into_iter().filter_map(|e| if e == Expr::r#true() {
            None
        } else {
            Some(Predicate::Basic(e))
        }
        ).collect())
    }

    fn from_preds(preds: Vec<Predicate<'tcx>>) -> Self {
        let mut preds = preds
            .into_iter()
            .filter(|p| !(p == &Predicate::Basic(Expr::r#true())))
            .unique()
            .collect::<Vec<_>>();
        if preds.is_empty() {
            Predicate::Basic(Expr::r#true())
        } else if preds.len() == 1 {
            preds.remove(0)
        } else {
            Predicate::Conj(preds)
        }
    }

    pub fn from_expr(e: Expr<'tcx>) -> Self {
        Predicate::Basic(e)
    }

    /// emit `true` predicate
    pub fn r#true() -> Self {
        Self::from_expr(Expr::r#true())
    }

    pub fn negated(self) -> Self {
        match self {
            Predicate::Not(box p) => p,
            _ => {
                if self == Self::r#true() {
                    // TODO: Is it right to consider true predicate as unknown, so `not true` becomes `true` again
                    self
                } else {
                    Predicate::Not(box self)
                }
            }
        }
    }

    pub fn parts(self) -> impl Iterator<Item=Predicate<'tcx>> {
        if let Predicate::Conj(parts) = self {
            parts.into_iter().into_left()
        } else {
            once(self).into_right()
        }
    }

    pub fn extend(&mut self, add: Self) {
        take_mut::take(self, |slf|
            Predicate::from_preds(once(slf).chain(add.parts()).collect())
        );
//        self.parts.append(&mut add.parts)
    }
}

impl<'tcx> From<Expr<'tcx>> for Predicate<'tcx> {
    fn from(expr: Expr<'tcx>) -> Self {
        Predicate::from_expr(expr)
    }
}

/// The main type that represents refinement,
/// inferred from code or specified by programmer
/// {v: <base_type> | <predicate>}
/// Note that <predicate> may contain negated arrays of conjoined predicates
/// when they represent refinements from different predecessors
#[derive(Clone, Debug, Eq, PartialEq, Hash, Display)]
#[display(fmt = "{{ v: {:?} | {} }}", base_type, predicate)]
pub struct Refinement<'tcx> {
    base_type: TyKind<'tcx>,
    predicate: Predicate<'tcx>,
}

impl<'tcx> Refinement<'tcx> {
    pub fn new(base_type: TyKind<'tcx>, predicate: Predicate<'tcx>) -> Self {
        Self { base_type, predicate }
    }
    /// {v: <base_type> | true}
    pub fn unknown(base_type: TyKind<'tcx>) -> Self {
        Self {
            base_type,
            predicate: Predicate::r#true(),
        }
    }

    pub fn base_type(&self) -> &TyKind {
        &self.base_type
    }

    pub fn predicate_mut(&mut self) -> &mut Predicate<'tcx> {
        &mut self.predicate
    }

    pub fn predicate(&self) -> &Predicate<'tcx> {
        &self.predicate
    }

    pub fn adjust(&mut self, adj: Self) -> Result<(), failure::Error> {
        // turn iterator of refs pointing to refs to iterator of refs pointing to objects
        if let Some(_) = Self::common_base_type([&adj, self].into_iter().copied()) {
            self.predicate.extend(adj.predicate);
            Ok(())
        } else {
            Err(failure::format_err!("Incompatible basic types: {:?} and {:?}", adj.base_type, self.base_type))
        }
    }

    /// returns common base type of several refinements to merge them
    fn common_base_type<'s>(refs: impl IntoIterator<Item=&'s Self>) -> Option<TyKind<'tcx>>
        where 'tcx: 's
    {
        // subtyping?
        let mut bts = refs.into_iter().map(|r| &r.borrow().base_type).dedup();
        let base_type = bts.next();
        // if there is only one type after dedup
        if bts.next().is_none() {
            base_type.cloned()
        } else {
            None
        }
    }
    /// used to construct refinement from alternative
    /// predecessors' refinements
    pub fn from_alternatives(alts: Vec<Self>) -> Result<Self, failure::Error> {
        if let Some(base_type) = Self::common_base_type(&alts) {
            // a \/ b = -(-a /\ -b), De Morgan law
            let preds = alts
                .into_iter()
                // a \/ a == a
                .unique()
                .map(|r| r.predicate)
                .map(Predicate::negated)
                .collect();
            let pred = Predicate::from_preds(preds);
            Ok(Self::new(base_type, pred.negated()))
        } else {
            Err(err_msg("Incompatible basic types"))
        }
    }

//    pub fn from_restriction_expr(tcx: TyCtxt, expr: RestrictionExpr) -> Result<Self, failure::Error> {
//        expr.accept(|e| {
//            match e {
//
//            }
//        });
//        unimplemented!()
//    }
}

impl<'tcx> Into<Predicate<'tcx>> for Refinement<'tcx> {
    fn into(self) -> Predicate<'tcx> {
        self.predicate
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_from_unknown_alternatives() -> Result<(), failure::Error> {
        let ty = TyKind::Bool;
        let alts = vec![Refinement::unknown(ty.clone()), Refinement::unknown(ty.clone())];
        let res = Refinement::from_alternatives(alts)?;
        let expected = Refinement {
            base_type: TyKind::Bool,
            predicate: Predicate::Basic(Expr::r#true())
        };
        assert_eq!(res, expected);
        Ok(())
    }
}