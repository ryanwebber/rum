use crate::interpreter::{Error, Module, NativeCall, Value};

pub struct Collections;

impl Module for Collections {
    fn register_builtins(&self, backend: &mut crate::interpreter::Backend) {
        // TODO
    }

    fn prelude() -> &'static str {
        include_str!("collections.rum")
    }
}
