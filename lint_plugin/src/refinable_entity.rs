use derive_more::Display;
use rustc::mir::{Local, Place, PlaceBase, Body};
use rustc::hir::def_id::DefId;
use crate::typable::{Typable, Ty, Typer};

#[derive(Clone, PartialEq, Eq, Hash, Debug, Display)]
#[display(fmt = "<{:?}: {:?}>", fun_id, place)]
pub struct RefinableEntity<'tcx> {
    fun_id: DefId,
    place: Place<'tcx>,
}

impl<'tcx> RefinableEntity<'tcx> {
    /// Body must refer to self.fun_id
    pub fn name(&self, body: &Body) -> Option<String> {
        if let Some(local)= self.place.as_local() {
            body.local_decls[local].name.map(|n| (*n.as_str()).to_owned())
        } else {
            None
        }
    }

    pub fn fun_id(&self) -> DefId {
        self.fun_id
    }

    pub fn from_place(place: Place<'tcx>, fun_id: DefId) -> Self {
        Self {
            fun_id,
            place,
        }
    }

    pub fn from_local(local: Local, fun_id: DefId) -> Self {
        Self {
            fun_id,
            place: local.into(),
        }
    }

    pub fn place(&self) -> &Place<'tcx> {
        &self.place
    }
}

impl<'tcx, T: Typer<'tcx>> Typable<'tcx, T> for RefinableEntity<'tcx> {
    fn ty(&self, typer: &T) -> Option<Ty> {
        typer.ty(self).into()
    }
}

impl<'tcx> Into<Place<'tcx>> for RefinableEntity<'tcx> {
    fn into(self) -> Place<'tcx> {
        self.place
    }
}

//impl<'tcx> From<&Place<'tcx>> for RefinableEntity {
//    fn from(p: &Place<'tcx>) -> Self {
//        match p.base {
//            PlaceBase::Local(ref l) => RefinableEntity::Local(*l),
//            _ => unimplemented!("RefinableEntity from Static")
//        }
//    }
//}
//
//impl From<Local> for RefinableEntity {
//    fn from(l: Local) -> Self {
//        RefinableEntity::Local(l)
//    }
//}
//
