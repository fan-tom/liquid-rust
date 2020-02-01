use rustc::{
    mir::Body,
    hir::def_id::DefId,
};
use std::collections::HashMap;
use crate::refinable_entity::RefinableEntity;

pub struct NameRegistry<'tcx, 'b> {
    bodies: &'b HashMap<DefId, &'tcx Body<'tcx>>,
    pub names: HashMap<RefinableEntity<'tcx>, String>,
    counter: usize,
}

impl<'tcx, 'b> NameRegistry<'tcx, 'b> {
    pub fn new(bodies: &'b HashMap<DefId, &'tcx Body<'tcx>>) -> Self {
        Self {
            bodies,
            counter: 0,
            names: HashMap::new(),
        }
    }

    pub fn get(&mut self, var: RefinableEntity<'tcx>) -> &str {
        if !self.names.contains_key(&var) {
            let bodies = &self.bodies;
            let counter = &mut self.counter;
            let name = if let Some(name) = var
                .name(bodies
                    .get(&var.fun_id())
                    .expect(&format!("Unknown function id: {:?}", var.fun_id()))
                ) {
                if !self.names.values().any(|n| n == &name) {
                    name
                } else {
                    *counter += 1;
                    format!("{}_{}", name, counter)
                }
            } else {
                *counter += 1;
                format!("VAR_{}", counter)
            };
            println!("Assigned name {} to var {:?}", name, var);
            self.names.insert(var.clone(), name);
        }
        // ugly code because borrowck doesn't allow to read hashmap when
        // we created entry by key, even if that entry is not occupied
        self.names.get(&var).unwrap()
    }

    pub fn get_existing(&mut self, var: &RefinableEntity<'tcx>) -> Option<&str> {
        self.names.get(var).map(|v| v.as_str())
    }
}
