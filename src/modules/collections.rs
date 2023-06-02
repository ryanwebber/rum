use crate::interpreter::{Backend, Error, Module, NativeCallType, PrintableValue, Value};

pub struct Collections;

impl Module for Collections {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.register(
            "__collections$first",
            NativeCallType::Default,
            |_, state, args| match args {
                [value] => match value {
                    Value::List(list) => match list.first() {
                        Some(value) => Ok(value.clone()),
                        None => Err(Error::invalid_bridge_call("first", "Expected non-empty list")),
                    },
                    _ => Err(Error::invalid_bridge_call(
                        "first",
                        &format!("Expected list, but got: {}", PrintableValue(state, value)),
                    )),
                },
                _ => Err(Error::invalid_bridge_call(
                    "first",
                    &format!(
                        "Expected exactly one argument, but got: {}",
                        PrintableValue(state, &Value::List(args.to_vec()))
                    ),
                )),
            },
        );

        backend.register(
            "__collections$set",
            NativeCallType::Default,
            |_, state, args| match args {
                [Value::Table(table), key, value] => {
                    table.borrow_mut().insert(key.clone(), value.clone());
                    return Ok(Value::empty());
                }
                _ => Err(Error::invalid_bridge_call(
                    "set",
                    &format!(
                        "Expected table, key, and value, but got: {}",
                        PrintableValue(state, &Value::List(args.to_vec()))
                    ),
                )),
            },
        );
    }

    fn prelude() -> &'static str {
        include_str!("collections.rum")
    }
}

#[cfg(test)]
mod tests {

    use crate::interpreter::{Runtime, Value};

    #[test]
    fn test_first() {
        let mut runtime = Runtime::new();
        assert_eq!(runtime.evaluate_expr("(first '(1 2 3))"), Ok(Value::Number(1)));
    }

    #[test]
    fn test_set() {
        let mut runtime = Runtime::new();
        assert!(runtime.evaluate_expr("(set #Env 'a 1)").is_ok());
        assert_eq!(runtime.evaluate_expr("a"), Ok(Value::Number(1)));
    }
}
