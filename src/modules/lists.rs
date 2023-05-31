use crate::interpreter::{Backend, Error, Module, PrintableValue, Value};

pub struct Lists;

impl Module for Lists {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.insert("__list$first", |_, state, args| match args {
            [value] => match value {
                Value::List(list) => match list.first() {
                    Some(value) => Ok(value.clone()),
                    None => Err(Error::invalid_native_call("first", "Expected non-empty list")),
                },
                _ => Err(Error::invalid_native_call(
                    "first",
                    &format!("Expected list, but got: {}", PrintableValue(state, value)),
                )),
            },
            _ => Err(Error::invalid_native_call(
                "first",
                &format!(
                    "Expected exactly one argument, but got: {}",
                    PrintableValue(state, &Value::List(args.to_vec()))
                ),
            )),
        });
    }

    fn prelude() -> &'static str {
        include_str!("lists.rum")
    }
}

#[cfg(test)]
mod tests {

    use crate::interpreter;

    #[test]
    fn test_first() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.evaluate_expr("(first '(1 2 3))"),
            Ok(interpreter::Value::Number(1))
        );
    }
}
