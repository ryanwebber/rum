use crate::interpreter::{Backend, Error, Function, Identifier, Module, NativeCallType, PrintableValue, Value};

pub struct Core;

impl Module for Core {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.register("__core$quote", NativeCallType::Macro, |_, state, args| match args {
            [value] => Ok(value.clone()),
            _ => Err(Error::invalid_bridge_call(
                "quote",
                &format!(
                    "Expected exactly one argument, but got: {}",
                    PrintableValue(state, &Value::List(args.to_vec()))
                ),
            )),
        });

        backend.register("__core$def_fn", NativeCallType::Default, |_, state, args| match args {
            [Value::Identifier(id), Value::List(args), body] => {
                let parameters = args
                    .iter()
                    .map(|arg| match arg {
                        Value::Identifier(id) => Ok(*id),
                        _ => Err(Error::invalid_bridge_call(
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
            _ => Err(Error::invalid_bridge_call(
                "def-fn!",
                &format!(
                    "Expected identifier, argument list, and body, but got: {}",
                    PrintableValue(state, &Value::List(args.to_vec()))
                ),
            )),
        });

        backend.register(
            "__core$apply",
            NativeCallType::Default,
            |interpreter, state, args| match args {
                [callee, Value::List(args)] => interpreter.try_call(state, &callee, args),
                _ => Err(Error::invalid_bridge_call(
                    "apply",
                    &format!(
                        "Expected function and argument list, but got: {}",
                        PrintableValue(state, &Value::Vector(args.to_vec()))
                    ),
                )),
            },
        );

        backend.register(
            "__core$evaluate",
            NativeCallType::Default,
            |interpreter, state, args| match args {
                [value] => interpreter.evaluate(state, &value),
                _ => Err(Error::invalid_bridge_call(
                    "evaluate",
                    &format!(
                        "Expected exactly one argument, but got: {}",
                        PrintableValue(state, &Value::List(args.to_vec()))
                    ),
                )),
            },
        );

        backend.register(
            "__core$with",
            NativeCallType::Default,
            |interpreter, state, args| match args {
                [Value::List(bindings), body] => {
                    let (parameters, args): (Vec<Identifier>, Vec<Value>) = bindings
                        .into_iter()
                        .map(|value| match value {
                            Value::List(list) => match &list[..] {
                                [Value::Identifier(id), value] => Ok((*id, interpreter.evaluate(state, &value)?)),
                                _ => Err(Error::invalid_bridge_call(
                                    "with!",
                                    &format!("Expected binding pair, but got: {}", PrintableValue(state, value)),
                                )),
                            },
                            _ => Err(Error::invalid_bridge_call(
                                "with!",
                                &format!("Expected binding pair, but got: {}", PrintableValue(state, value)),
                            )),
                        })
                        .collect::<Result<Vec<(Identifier, Value)>, Error>>()?
                        .into_iter()
                        .unzip();

                    let function = Function {
                        body: Box::new(body.clone()),
                        parameters,
                        is_macro: false,
                    };

                    let mut new_state = state.closing(&function, args);
                    interpreter.evaluate(&mut new_state, &function.body)
                }
                _ => Err(Error::invalid_bridge_call(
                    "with!",
                    &format!(
                        "Expected two arguments, but got: {}",
                        PrintableValue(state, &Value::List(args.to_vec()))
                    ),
                )),
            },
        );

        backend.register("__core$do", NativeCallType::Default, |_, state, args| match args {
            [Value::List(args)] => Ok(args.last().map_or(Value::empty(), |v| v.clone())),
            _ => Err(Error::invalid_bridge_call(
                "do",
                &format!(
                    "Expected list, but got: {}",
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
    fn test_apply() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(runtime.evaluate_expr("(apply + '(1 2))"), Ok(Value::Number(3)));
    }

    #[test]
    fn test_quote() {
        let mut runtime = interpreter::Runtime::new();
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

    #[test]
    fn test_with() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.evaluate_expr("(with! { x => 2 y => 3 } (+ x (+ x y)))"),
            Ok(Value::Number(7))
        );
    }

    #[test]
    fn test_do() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(runtime.evaluate_expr("(do 1 2 3 4 5)"), Ok(Value::Number(5)));
    }
}
