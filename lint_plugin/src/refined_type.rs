use failure::err_msg;
use rustc::ty::TyKind;

use crate::expr::Expr;
use itertools::Itertools;
use std::borrow::Borrow;

#[derive(Clone, Debug)]
pub enum PredicateConjunctionPart {
    Basic(Expr),
    Conj(PredicateConjunction),
}

#[derive(Clone, Debug)]
pub struct PredicateConjunction {
    negated: bool,
    // vector of conjoined boolean expressions
    // /\ expr(v, locals)
    parts: Vec<PredicateConjunctionPart>,
}

impl PredicateConjunction {
    pub fn from_exprs(exprs: Vec<Expr>) -> Self {
        Self {
            negated: false,
            parts: exprs.into_iter().map(PredicateConjunctionPart::Basic).collect(),
        }
    }

    pub fn from_preds(preds: Vec<PredicateConjunction>) -> Self {
        Self {
            negated: false,
            parts: preds.into_iter().map(PredicateConjunctionPart::Conj).collect(),
        }
    }

    pub fn from_expr(e: Expr) -> Self {
        Self::from_exprs(vec![e])
    }

    /// emit `true` predicate
    pub fn r#true() -> Self {
        Self::from_expr(Expr::r#true())
    }

    pub fn negated(&mut self) -> &mut Self {
        self.negated = !self.negated;
        self
    }
//    pub fn parts(&self) -> &[Expr] {
//        &self.parts
//    }

    pub fn extend(&mut self, mut add: Self) {
        self.parts.append(&mut add.parts)
    }
}

/// The main type that represents refinement,
/// inferred from code or specified by programmer
/// {v: <base_type> | <predicate>}
/// Note that <predicate> may contain negated arrays of conjoined predicates
/// when they represent refinements from different predecessors
#[derive(Clone, Debug)]
pub struct Refinement<'tcx> {
    base_type: TyKind<'tcx>,
    predicate: PredicateConjunction,
}

impl<'tcx> Refinement<'tcx> {
    pub fn new(base_type: TyKind<'tcx>, predicate: PredicateConjunction) -> Self {
        Self { base_type, predicate }
    }
    /// {v: <base_type> | true}
    pub fn unknown(base_type: TyKind<'tcx>) -> Self {
        Self {
            base_type,
            predicate: PredicateConjunction::r#true(),
        }
    }

    pub fn base_type(&self) -> &TyKind {
        &self.base_type
    }

    pub fn predicate(&self) -> &PredicateConjunction {
        &self.predicate
    }

    pub fn adjust(&mut self, adj: Self) -> Result<(), failure::Error> {
        // turn iterator of refs pointing to refs to iterator of refs pointing to objects
        if let Some(_) = Self::common_base_type([&adj, self].into_iter().copied()) {
            self.predicate.extend(adj.predicate);
            Ok(())
        } else {
            Err(err_msg("Incompatible basic types"))
        }
    }

    /// returns common base type of several refinements to merge them
    fn common_base_type<'s>(refs: impl IntoIterator<Item=&'s Self>) -> Option<TyKind<'tcx>>
    where 'tcx: 's
    {
        // subtyping?
        let mut bts = refs.into_iter().map(|r| &r.borrow().base_type).dedup();
        let base_type = bts.next();
        if bts.next().is_none() {
            base_type.cloned()
        } else {
            None
        }
    }
    /// used to construct refinement from alternative
    /// predecessors refinements
    pub fn from_alternatives(alts: Vec<Self>) -> Result<Self, failure::Error> {
        if let Some(base_type) = Self::common_base_type(&alts) {
            // a \/ b = -(-a /\ -b), De Morgan law
            let preds = alts
                .into_iter()
                .map(|r| r.predicate)
                .map(|mut r| {r.negated(); r})
                .collect();
            let mut pred = PredicateConjunction::from_preds(preds);
            pred.negated();
            Ok(Self::new(base_type, pred))
        } else {
            Err(err_msg("Incompatible basic types"))
        }
    }
}