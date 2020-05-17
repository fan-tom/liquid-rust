use rustc::mir::Body;
use crate::refinable_entity::RefinableEntity;
use rustc::ty::{TyCtxt, TyKind};
use std::convert::{TryFrom, TryInto};
use std::collections::HashMap;
use rustc::hir::def_id::DefId;

#[derive(Copy, Clone, Debug)]
pub enum Ty {
    UInt(usize),
    Int(usize),
    Bool,
}

impl Ty {
   pub fn bit_width(&self) -> Option<usize> {
       match self {
           Ty::UInt(size) | Ty::Int(size) => Some(*size),
           Ty::Bool => None,
       }
   }
}

impl<'tcx, 't> TryFrom<&'t TyKind<'tcx>> for Ty {
    type Error = &'t TyKind<'tcx>;

    fn try_from(kind: &'t TyKind<'tcx>) -> Result<Self, Self::Error> {
        Ok(match kind {
            TyKind::Bool => Ty::Bool,
            TyKind::Int(ty) => Ty::Int(ty.bit_width().expect("Isize not supported")),
            TyKind::Uint(ty) => Ty::UInt(ty.bit_width().expect("Usize not supported")),
            _ => return Err(kind)
        })
    }
}

pub trait Typer<'tcx> {
    fn ty(&self, v: &RefinableEntity<'tcx>) -> Ty;
    fn v_ty(&self) -> Option<Ty>;
}

pub struct DefaultTyper<'b, 'mir, 'tcx> {
    pub bodies: &'b HashMap<DefId, &'mir Body<'tcx>>,
    pub tcx: TyCtxt<'tcx>,
    pub v_ty: Option<Ty>,
}

impl<'b, 'mir, 'tcx> Typer<'tcx> for DefaultTyper<'b, 'mir, 'tcx> {
    fn ty(&self, v: &RefinableEntity<'tcx>) -> Ty {
        let body = self.bodies.get(&v.fun_id()).expect(&format!("No body for fun_id {:?}", v.fun_id()));
        (&v.place().ty(*body, self.tcx).ty.kind).try_into().unwrap_or_else(|k| panic!("TyKind {:?} has no corresponding type", k))
    }

    fn v_ty(&self) -> Option<Ty> {
        self.v_ty
    }
}

pub trait Typable<'tcx, T: Typer<'tcx>> {
    fn ty(&self, typer: &T) -> Option<Ty>;
}