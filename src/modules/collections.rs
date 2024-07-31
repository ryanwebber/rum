use crate::interpreter::Module;

pub struct Collections;

impl Module for Collections {
    fn register_builtins(&self, _: &mut crate::interpreter::Backend) {
        // TODO
    }

    fn prelude() -> &'static str {
        include_str!("collections.rum")
    }
}
