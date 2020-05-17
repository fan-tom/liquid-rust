use rustproof_libsmt::backends::smtlib2::SMTLib2;
use rustproof_libsmt::backends::backend::{Logic, SMTBackend};
use std::collections::HashMap;
use crate::refinable_entity::RefinableEntity;
use std::ops::DerefMut;
use failure::_core::ops::Deref;

pub type SMTIdx<L> = <SMTLib2<L> as SMTBackend>::Idx;
pub type Decls<'tcx, L> = HashMap<RefinableEntity<'tcx>, SMTIdx<L>>;

pub trait SmtConverterCtx<'tcx, L: Logic>: DerefMut<Target = SMTLib2<L>> {
    fn get_name(&self, var: &RefinableEntity<'tcx>) -> Option<SMTIdx<L>>;
    fn add_name(&mut self, var: RefinableEntity<'tcx>, idx: SMTIdx<L>);
}

#[derive(Debug)]
pub struct DefaultSmtConverterCtx<'tcx, L: Logic> {
    pub solver: SMTLib2<L>,
    pub names: Decls<'tcx, L>
}

impl<L: Logic> Deref for DefaultSmtConverterCtx<'_, L> {
    type Target = SMTLib2<L>;
    fn deref(&self) -> &Self::Target {
        &self.solver
    }
}

impl<L: Logic> DerefMut for DefaultSmtConverterCtx<'_, L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.solver
    }
}

impl<'tcx, L: Logic> SmtConverterCtx<'tcx, L> for DefaultSmtConverterCtx<'tcx, L> {
    fn get_name(&self, var: &RefinableEntity<'tcx>) -> Option<SMTIdx<L>> {
        self.names.get(var).copied()
    }

    fn add_name(&mut self, var: RefinableEntity<'tcx>, idx: SMTIdx<L>) {
        self.names.insert(var, idx);
    }
}

pub trait ToSmt<'tcx, L: Logic, C: SmtConverterCtx<'tcx, L> = DefaultSmtConverterCtx<'tcx, L>> {
    type Output = SMTIdx<L>;
    // TODO: think about return Result with error from assoc type, Never in some cases
    fn to_smt(&self, ctx: &mut C) -> Option<Self::Output>;
}