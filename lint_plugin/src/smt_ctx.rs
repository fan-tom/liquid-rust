use crate::to_smt::{SmtConverterCtx, SMTIdx, Decls, DefaultSmtConverterCtx};
use crate::refinable_entity::RefinableEntity;
use crate::typable::{Typer, Ty, DefaultTyper};
use rustc::ty::TyCtxt;
use rustproof_libsmt::backends::smtlib2::SMTLib2;
use rustc::mir::Body;
use rustproof_libsmt::backends::backend::Logic;
use std::ops::{Deref, DerefMut};
use std::marker::PhantomData;
use std::collections::HashMap;
use rustc::hir::def_id::DefId;

#[derive(Debug)]
pub struct SmtCtx<L, T, S> {
    phantom: PhantomData<L>,
    typer: T,
    smt_converter: S
}

impl<L: Logic> SmtCtx<L, (), ()> {
    pub fn new_default<'b, 'mir, 'tcx>(bodies: &'b HashMap<DefId, &'mir Body<'tcx>>, tcx: TyCtxt<'tcx>, solver: SMTLib2<L>, names: Decls<'tcx, L>, v_ty: Option<Ty>) -> SmtCtx<L, DefaultTyper<'b, 'mir, 'tcx>, DefaultSmtConverterCtx<'tcx, L>> {
        SmtCtx {
            typer: DefaultTyper {
                bodies,
                tcx,
                v_ty,
            },
            smt_converter: DefaultSmtConverterCtx {
                solver,
                names,
            },
            phantom: Default::default()
        }
    }
}

impl<L: Logic, T, S> SmtCtx<L, T, S> {
    pub fn new(typer: T, smt_converter: S) -> Self {
        Self {
            typer,
            smt_converter,
            phantom: Default::default()
        }
    }

}

impl<'tcx, L: Logic, T, S: SmtConverterCtx<'tcx, L>> Deref for SmtCtx<L, T, S> {
    type Target = SMTLib2<L>;

    fn deref(&self) -> &Self::Target {
        self.smt_converter.deref()
    }
}

impl<'tcx, L: Logic, T, S: SmtConverterCtx<'tcx, L>> DerefMut for SmtCtx<L, T, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.smt_converter.deref_mut()
    }
}

impl<'tcx, T, L: Logic, S: SmtConverterCtx<'tcx, L>> SmtConverterCtx<'tcx, L> for SmtCtx<L, T, S> {
    fn get_name(&self, var: &RefinableEntity<'tcx>) -> Option<SMTIdx<L>> {
        self.smt_converter.get_name(var)
    }

    fn add_name(&mut self, var: RefinableEntity<'tcx>, idx: SMTIdx<L>) {
        self.smt_converter.add_name(var, idx);
    }
}

impl<'tcx, L, S, T: Typer<'tcx>> Typer<'tcx> for SmtCtx<L, T, S> {
    fn ty(&self, v: &RefinableEntity<'tcx>) -> Ty {
        self.typer.ty(v)
    }

    fn v_ty(&self) -> Option<Ty> {
        self.typer.v_ty()
    }
}