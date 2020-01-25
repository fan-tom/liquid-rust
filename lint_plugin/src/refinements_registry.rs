use rustc::hir::def_id::DefId;
use rustc::ty::subst::{SubstsRef, GenericArg};
use std::collections::HashMap;
use crate::restriction_expr::{Expr as RestrictionExpr, Const};
use std::collections::hash_map::{DefaultHasher, Entry};
use rustc::ty::{List, TyCtxt, Instance};
use std::hash::{Hash, Hasher};
use failure::Error;
use crate::restriction_extractor::extract_restrictions;
use std::cell::RefCell;

pub type SubstHash = u64;

pub type RestrictionMap = HashMap<String, RestrictionExpr>;

/// Type, that represents function preconditions as HashMap from arguments to restrictions and restriction for return value
#[derive(Debug)]
pub struct FunctionRestrictions(RestrictionMap, RestrictionExpr);

impl FunctionRestrictions {
    pub fn new(restrictions: RestrictionMap, ret: Option<RestrictionExpr>) -> Self {
        Self(restrictions, ret.unwrap_or(RestrictionExpr::Const(Const::Bool(true))))
    }

    pub fn pre(&self) -> &RestrictionMap {
        &self.0
    }

    pub fn post(&self) -> &RestrictionExpr {
        &self.1
    }
}

pub trait RestrictionRegistry {
    fn add(&mut self, def_id: DefId, refinement: FunctionRestrictions) -> Option<FunctionRestrictions>;
    fn add_generic(&mut self, def_id: DefId, substs: SubstsRef, refinement: FunctionRestrictions) -> Option<FunctionRestrictions>;
    fn get_or_extract_restrictions(&mut self, fun_id: DefId, tcx: TyCtxt) -> Result<&FunctionRestrictions, Error>;
    fn get_or_extract_restrictions_generic(&mut self, fun_id: DefId, substs: SubstsRef, tcx: TyCtxt) -> Result<&FunctionRestrictions, Error>;
}

impl<T: RestrictionRegistry> RestrictionRegistry for &mut T {
    fn add(&mut self, def_id: DefId, refinement: FunctionRestrictions) -> Option<FunctionRestrictions> {
        (**self).add(def_id, refinement)
    }

    fn add_generic(&mut self, def_id: DefId, substs: SubstsRef, refinement: FunctionRestrictions) -> Option<FunctionRestrictions> {
        (**self).add_generic(def_id, substs, refinement)
    }

    fn get_or_extract_restrictions(&mut self, fun_id: DefId, tcx: TyCtxt) -> Result<&FunctionRestrictions, Error> {
        (**self).get_or_extract_restrictions(fun_id,tcx)
    }

    fn get_or_extract_restrictions_generic(&mut self, fun_id: DefId, substs: SubstsRef, tcx: TyCtxt) -> Result<&FunctionRestrictions, Error> {
        (**self).get_or_extract_restrictions_generic(fun_id, substs, tcx)
    }
}

#[derive(Default)]
pub struct Restricter {
    restrictions: HashMap<(DefId, Option<SubstHash>), FunctionRestrictions>,
}

impl Restricter {
    pub fn new() -> Self {
        Self {
            restrictions: Default::default()
        }
    }
}

impl RestrictionRegistry for Restricter {
    fn add(&mut self, def_id: DefId, refinement: FunctionRestrictions) -> Option<FunctionRestrictions> {
        self.restrictions.insert((def_id, None), refinement)
    }

    fn add_generic(&mut self, def_id: DefId, substs: SubstsRef, refinement: FunctionRestrictions) -> Option<FunctionRestrictions> {
        let mut hasher = DefaultHasher::default();
        substs.hash(&mut hasher);
        let hash = hasher.finish();
        self.restrictions.insert((def_id, Some(hash)), refinement)
    }

    fn get_or_extract_restrictions(&mut self, fun_id: DefId, tcx: TyCtxt) -> Result<&FunctionRestrictions, Error> {
//        unimplemented!();
        let entry = self.restrictions.entry((fun_id, None));
        if let Entry::Occupied(res) = entry {
            Ok(res.into_mut())
        } else {
            let (restrictions, mir) = extract_restrictions(tcx, fun_id);
            mir?;
            Ok(entry.insert(restrictions).into_mut())
        }
    }

    fn get_or_extract_restrictions_generic(&mut self, fun_id: DefId, substs: SubstsRef, tcx: TyCtxt) -> Result<&FunctionRestrictions, Error> {
        unimplemented!()
    }
}
