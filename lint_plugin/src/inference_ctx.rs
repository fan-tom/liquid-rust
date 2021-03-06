use std::{
    collections::HashMap,
    fmt
};
use crate::{
    refinable_entity::RefinableEntity,
    refined_type::{Refinement, Predicate}
};
use itertools::Itertools;

pub type RefinementMap<'tcx> = HashMap<RefinableEntity<'tcx>, Refinement<'tcx>>;
/// Holds inferred types of local variables;
#[derive(Clone, Debug, Default)]
pub struct InferenceCtx<'tcx> {
    // need some type here to represent qualifiable entities, such as function args,
    // function return, locals, temps, struct fields and slice elems.
    // seems that Place is power enough for that purpose
    refinements: RefinementMap<'tcx>,
}

impl fmt::Display for InferenceCtx<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let res = self.refinements
            .iter()
            .map(|(k, v)| format!("{}: {}", k, v))
            .join("\n");
        write!(f, "{}", res)
    }
}

impl<'tcx> InferenceCtx<'tcx> {
    pub fn new(refinements: RefinementMap<'tcx>) -> Self {
        Self { refinements }
    }

    pub fn get_refinement(&self, p: &RefinableEntity<'tcx>) -> Refinement<'tcx> {
        self.refinements[p].clone()
    }

    pub fn refine(&mut self, var: RefinableEntity<'tcx>, lqt: Refinement<'tcx>) {
        // we need to assign more specific type to var, provided by lqt
        // and also check that it is compatible with existing one
        // conjoin predicates
        println!("Refining {} with {}", var, lqt);
        if lqt.to_string() == "{ v: Bool | not (v = 0) }" {
            panic!("Found!!!")
        }
        if let Some(existing_refinement) = self.refinements.get_mut(&var) {
            existing_refinement.adjust(lqt).expect(&format!("var: {:?}, self: {:#?}", &var, self));
        } else {
            self.refinements.insert(var, lqt);
        }
    }

    pub fn merge(&mut self, other: Self) {
        for (place, refinement) in other.refinements.into_iter() {
            self.refine(place, refinement)
        }
    }

    fn updated(&self, var: RefinableEntity<'tcx>, lqt: Refinement<'tcx>) -> Self {
        let mut res = self.clone();
        res.refine(var, lqt);
        res
    }

    pub fn refinements_mut(&mut self) -> &mut RefinementMap<'tcx> {
        &mut self.refinements
    }

    pub fn into_inner(self) -> RefinementMap<'tcx> {
        self.refinements
    }

    pub fn predicates(&self) -> impl Iterator<Item=&Predicate<'tcx>> {
        self.refinements.values().map(|r| r.predicate())
    }
}

impl<'tcx> From<RefinementMap<'tcx>> for InferenceCtx<'tcx> {
    fn from(refinements: RefinementMap<'tcx>) -> Self {
        Self::new(refinements)
    }
}
