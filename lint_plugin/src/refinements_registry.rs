use rustc::hir::def_id::DefId;
use rustc::ty::subst::{SubstsRef, GenericArg};
use std::collections::HashMap;
use crate::restriction_expr::{Expr as RestrictionExpr, Const};
use std::collections::hash_map::DefaultHasher;
use rustc::ty::{List, TyCtxt, Instance};
use std::hash::{Hash, Hasher};
use failure::Error;

pub type SubstHash = u64;

pub type RestrictionMap = HashMap<String, RestrictionExpr>;

/// Type, that represents function preconditions as HashMap from arguments to restrictions and restriction for return value
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
    fn function_refinement(&self, fun_id: DefId) -> Result<&FunctionRestrictions, Error>;
    fn function_refinement_generic(&self, fun_id: DefId, substs: SubstsRef) -> Result<&FunctionRestrictions, Error>;
}

impl<T: RestrictionRegistry> RestrictionRegistry for &mut T {
    fn add(&mut self, def_id: DefId, refinement: FunctionRestrictions) -> Option<FunctionRestrictions> {
        (**self).add(def_id, refinement)
    }

    fn add_generic(&mut self, def_id: DefId, substs: SubstsRef, refinement: FunctionRestrictions) -> Option<FunctionRestrictions> {
        (**self).add_generic(def_id, substs, refinement)
    }

    fn function_refinement(&self, fun_id: DefId) -> Result<&FunctionRestrictions, Error> {
        (**self).function_refinement(fun_id)
    }

    fn function_refinement_generic(&self, fun_id: DefId, substs: SubstsRef) -> Result<&FunctionRestrictions, Error> {
        (**self).function_refinement_generic(fun_id, substs)
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

    fn function_refinement(&self, fun_id: DefId) -> Result<&FunctionRestrictions, Error> {
//        unimplemented!();
//        self.restrictions.entry((fun_id, None)).or_insert_with(|| {
//            let mir = tcx.instance_mir(Instance::mono(tcx, fun_id).def);
//
//        })
        self.restrictions.get(&(fun_id, None)).ok_or(failure::err_msg("On demand function refining not implemented"))
    }

    fn function_refinement_generic(&self, fun_id: DefId, substs: SubstsRef) -> Result<&FunctionRestrictions, Error> {
        unimplemented!()
    }
}
