use crate::interpreter::{Error, Module, NativeCall, Value};

pub struct Collections;

impl Module for Collections {
    fn register_builtins(&self, backend: &mut crate::interpreter::Backend) {
        backend.register(
            "collections.map",
            NativeCall::Function(|interpreter, state, args| match args {
                [Value::Vector(values), lambda] => {
                    let new_list = values
                        .borrow()
                        .clone()
                        .into_iter()
                        .map(|item| interpreter.call_as_function(state, lambda, &[item]))
                        .collect::<Result<Vec<Value>, Error>>()?;

                    Ok(Value::vector(new_list))
                }
                _ => Err(Error::invalid_bridge_call(
                    "collections.map",
                    &format!("Expected a list and a function, but got: {:?}", args),
                )),
            }),
        );

        backend.register(
            "collections.reduce",
            NativeCall::Function(|interpreter, state, args| match args {
                [Value::Vector(values), initial, lambda] => {
                    let mut acc = initial.clone();
                    for item in values.borrow().iter() {
                        acc = interpreter.call_as_function(state, lambda, &[acc, item.clone()])?;
                    }
                    Ok(acc)
                }
                _ => Err(Error::invalid_bridge_call(
                    "collections.reduce",
                    &format!("Expected a list, an initial value, and a function, but got: {:?}", args),
                )),
            }),
        );
    }

    fn prelude() -> &'static str {
        include_str!("collections.rum")
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter;
    use crate::interpreter::Value;

    #[test]
    fn test_map() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr("(map [1 2 3] (lambda! (x) (+ x 1)))"),
            Ok(Value::vector(vec![
                Value::Number(2),
                Value::Number(3),
                Value::Number(4)
            ]))
        );
    }

    #[test]
    fn test_reduce() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr("(reduce [1 2 3] 0 +)"),
            Ok(Value::Number(6))
        );
    }
}
