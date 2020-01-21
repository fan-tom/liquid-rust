use rustc::mir::{Body, Local};
use std::collections::HashMap;
use crate::refinable_entity::RefinableEntity;
use rustc_data_structures::sync::HashMapExt;
use rustc::hir::def_id::DefId;

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
        let bodies = &self.bodies;
        let counter = &mut self.counter;
        self.names.entry(var.clone()).or_insert_with(|| {
            let name = if let Some(name) = var
                .name(bodies
                    .get(&var.fun_id())
                    .expect(&format!("Unknown function id: {:?}", var.fun_id()))
                ) {
                name
            } else {
                *counter += 1;
                format!("VAR_{}", counter)
            };
            println!("Assigned name {} to var {:?}", name, var);
            name
        })
    }

    pub fn get_existing(&mut self, var: &RefinableEntity<'tcx>) -> Option<&str> {
        self.names.get(var).map(|v| v.as_str())
    }
}