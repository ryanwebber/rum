use crate::interpreter::{Error, Module, NativeCall, Value};

pub struct Reflection;

impl Module for Reflection {
    fn register_builtins(&self, backend: &mut crate::interpreter::Backend) {
        backend.register(
            "reflection.symbol-to-string",
            NativeCall::Function(|_, state, args| match args {
                [Value::Symbol(symbol)] => {
                    let str = state.get_string(symbol).ok_or(Error::no_such_string())?;
                    Ok(Value::String(str.to_string()))
                }
                _ => Err(Error::invalid_bridge_call(
                    "reflection.symbol->string",
                    &format!("Expected a symbol, but got: {:?}", args),
                )),
            }),
        );
    }

    fn prelude() -> &'static str {
        include_str!("reflection.rum")
    }
}
