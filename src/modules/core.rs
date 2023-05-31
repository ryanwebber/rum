use crate::interpreter::{Backend, Error, Function, Identifier, Module, PrintableValue, Value};

pub struct Core;

impl Module for Core {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.insert("__core$quote", |_, _, args| {
            if args.len() != 1 {
                return Err(Error::invalid_native_call("quote", "Expected exactly one argument"));
            }

            Ok(args[0].clone())
        });

        backend.insert("__core$def_fn", |interpreter, state, args| {
            let evaluated_args = args
                .iter()
                .map(|arg| interpreter.evaluate(state, arg))
                .collect::<Result<Vec<Value>, Error>>()?;

            match &evaluated_args[..] {
                [Value::Identifier(id), Value::List(args), body] => {
                    let parameters = args
                        .iter()
                        .map(|arg| match arg {
                            Value::Identifier(id) => Ok(*id),
                            _ => Err(Error::invalid_native_call(
                                "def-fn!",
                                &format!("Expected identifier, but got: {}", PrintableValue(state, arg)),
                            )),
                        })
                        .collect::<Result<Vec<Identifier>, Error>>()?;

                    let fname = state.strings.resolve(id.0).unwrap();

                    state.globals().borrow_mut().insert(
                        Value::Identifier(*id),
                        Value::Function(Function {
                            body: Box::new(body.clone()),
                            parameters,
                            is_macro: fname.ends_with('!'),
                        }),
                    );

                    Ok(Value::empty())
                }
                _ => Err(Error::invalid_native_call(
                    "def-fn!",
                    &format!(
                        "Expected identifier, argument list, and body, but got: {}",
                        PrintableValue(state, &Value::List(args.to_vec()))
                    ),
                )),
            }
        });

        backend.insert("__core$evaluate", |interpreter, state, args| match args {
            [value] => {
                let value = interpreter.evaluate(state, value)?;
                let value = interpreter.evaluate(state, &value)?;
                return Ok(value);
            }
            _ => Err(Error::invalid_native_call(
                "evaluate",
                &format!(
                    "Expected exactly one argument, but got: {}",
                    PrintableValue(state, &Value::List(args.to_vec()))
                ),
            )),
        });
    }

    fn prelude() -> &'static str {
        include_str!("core.rum")
    }
}

#[cfg(test)]
mod tests {

    use crate::interpreter;
    use crate::interpreter::Value;

    #[test]
    fn test_add() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(runtime.evaluate_expr("(+ 4 5)"), Ok(interpreter::Value::Number(9)));
    }

    #[test]
    fn test_quote() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(runtime.evaluate_expr("(#Call :__core$quote 1)"), Ok(Value::Number(1)));
        assert_eq!(runtime.evaluate_expr("'(1)"), Ok(Value::List(vec![Value::Number(1)])));
    }

    #[test]
    fn test_def_fn() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(runtime.evaluate_expr("(def-fn! dbl (a) (+ a a))"), Ok(Value::empty()));
        assert_eq!(runtime.evaluate_expr("(dbl 5)"), Ok(Value::Number(10)));
    }

    #[test]
    fn test_eval() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(runtime.evaluate_expr("(eval '(+ 1 2))"), Ok(Value::Number(3)));
    }
}
