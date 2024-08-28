use crate::{
    ast::Expr,
    interpreter::{Backend, Error, Module, NativeCall, State, Table, Value},
    parser,
};

pub struct Core;

fn parse_lambda(call: &'static str, state: &mut State, args: &[Expr], is_macro: bool) -> Result<Table, Error> {
    match args {
        [Expr::List(parameters), body] => {
            let parameter_names: Vec<String> = parameters
                .iter()
                .map(|expr| match expr {
                    Expr::Identifier(id) => Ok(id.clone()),
                    _ => Err(Error::invalid_bridge_call(
                        "core.def-macro",
                        &format!("Expected parameter name to be an identifier, but got: {:?}", expr),
                    )),
                })
                .collect::<Result<_, _>>()?;

            let table = Table::callable(state, parameter_names.into_iter(), body.clone(), is_macro);

            Ok(table)
        }
        _ => Err(Error::invalid_bridge_call(
            call,
            &format!("Invalid function definition, got: {:?}", args),
        )),
    }
}

impl Module for Core {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.register(
            "core.def-macro",
            NativeCall::Macro(|_, state, args| match args.split_first() {
                Some((Expr::Identifier(id), rest)) => {
                    let table = parse_lambda("core.def-macro", state, rest, true)?;
                    let value = Value::table(table);
                    let symbol = state.get_symbol(id);
                    state.global_scope_mut().set_local(symbol, value.clone());
                    Ok(value)
                }
                _ => Err(Error::invalid_bridge_call(
                    "core.def-macro",
                    &format!("Expected (id [args...] body), but got: {:?}", args),
                )),
            }),
        );

        backend.register(
            "core.def-fn",
            NativeCall::Macro(|_, state, args| match args.split_first() {
                Some((Expr::Identifier(id), rest)) => {
                    let table = parse_lambda("core.def-fn", state, rest, false)?;
                    let value = Value::table(table);
                    let symbol = state.get_symbol(id);
                    state.global_scope_mut().set_local(symbol, value.clone());
                    Ok(value)
                }
                _ => Err(Error::invalid_bridge_call(
                    "core.def-fn",
                    &format!("Expected (id [args...] body), but got: {:?}", args),
                )),
            }),
        );

        backend.register(
            "core.lambda",
            NativeCall::Macro(|_, state, args| {
                let table = parse_lambda("core.lambda", state, args, false)?;
                Ok(Value::table(table))
            }),
        );

        backend.register(
            "core.call",
            NativeCall::Function(|interpreter, state, args| match args {
                [callee, Value::Vector(args)] => interpreter.call_as_function(state, &callee, &args.borrow().clone()),
                _ => Err(Error::invalid_bridge_call("core.call", "Expected (callee [args...])")),
            }),
        );

        backend.register(
            "core.get",
            NativeCall::Function(|_, _, args| match args {
                [Value::Table(table), key] => Ok(table.borrow().get(key).cloned().unwrap_or_else(|| Value::empty())),
                [Value::Vector(vec), Value::Number(index)] => {
                    let index = *index as usize;
                    let vec = vec.borrow();
                    if index < vec.len() {
                        Ok(vec[index].clone())
                    } else {
                        Ok(Value::empty())
                    }
                }
                _ => Err(Error::invalid_bridge_call(
                    "core.get",
                    &format!("Expected (table|vec key), but got: {:?}", args),
                )),
            }),
        );

        backend.register(
            "core.set",
            NativeCall::Function(|_, _, args| match args {
                [Value::Table(table), key, value] => {
                    table.borrow_mut().insert(key.clone(), value.clone());
                    Ok(Value::Table(table.clone()))
                }
                [Value::Vector(vec), Value::Number(index), value] => {
                    {
                        let mut vec = vec.borrow_mut();
                        let index = *index as usize;
                        if index < vec.len() {
                            vec[index] = value.clone();
                        } else {
                            vec.push(value.clone());
                        }
                    }

                    Ok(Value::Vector(vec.clone()))
                }
                _ => Err(Error::invalid_bridge_call(
                    "core.set",
                    &format!("Expected (table|vec key value), but got: {:?}", args),
                )),
            }),
        );

        backend.register(
            "core.first",
            NativeCall::Function(|_, _, args| match args {
                [Value::Vector(vec)] => Ok(vec.borrow().first().cloned().unwrap_or_else(|| Value::empty())),
                _ => Err(Error::invalid_bridge_call("core.last", "Expected (vec), but got: {:?}")),
            }),
        );

        backend.register(
            "core.last",
            NativeCall::Function(|_, _, args| match args {
                [Value::Vector(vec)] => Ok(vec.borrow().last().cloned().unwrap_or_else(|| Value::empty())),
                _ => Err(Error::invalid_bridge_call("core.last", "Expected (vec), but got: {:?}")),
            }),
        );

        backend.register(
            "core.append",
            NativeCall::Function(|_, _, args| match args {
                [Value::Vector(vec), value] => {
                    vec.borrow_mut().push(value.clone());
                    Ok(Value::Vector(vec.clone()))
                }
                _ => Err(Error::invalid_bridge_call(
                    "core.push",
                    "Expected (vec value), but got: {:?}",
                )),
            }),
        );

        backend.register(
            "core.match",
            NativeCall::Macro(|interpreter, state, args| match args {
                [lhs, Expr::Map(patterns)] => {
                    let lhs = interpreter.evaluate(state, lhs.clone())?;
                    for (pattern, body) in patterns.iter() {
                        match pattern {
                            Expr::Number(..) | Expr::String(..) | Expr::Symbol(..) => {
                                if lhs == interpreter.evaluate(state, pattern.clone())? {
                                    return interpreter.evaluate(state, body.clone());
                                }
                            }
                            Expr::Identifier(..) => {
                                let pattern = interpreter.evaluate(state, pattern.clone())?;
                                if lhs == pattern {
                                    return interpreter.evaluate(state, body.clone());
                                }
                            }
                            _ => todo!(),
                        }
                    }

                    Err(Error::no_matching_pattern(lhs.display(state), &patterns))
                }
                _ => Err(Error::invalid_bridge_call(
                    "core.match",
                    &format!("Expected (expr table), but got: {:?}", args),
                )),
            }),
        );

        backend.register(
            "core.let",
            NativeCall::Macro(|interpreter, state, args| match args {
                [Expr::Map(assignments), lhs] => {
                    for (lhs, expr) in assignments.iter() {
                        if let Expr::Identifier(id) = lhs {
                            let value = interpreter.evaluate(state, expr.clone())?;
                            let symbol = state.get_symbol(id);
                            state.current_scope_mut().set_local(symbol, value);
                        }
                    }

                    // TODO: Should we pop these bindings?
                    interpreter.evaluate(state, lhs.clone())
                }
                _ => Err(Error::invalid_bridge_call(
                    "core.match",
                    &format!("Expected (expr table), but got: {:?}", args),
                )),
            }),
        );

        backend.register(
            "core.eval",
            NativeCall::Function(|interpreter, state, args| match args {
                [Value::String(code)] => {
                    // TODO: Get this from the runtime?
                    let parser = parser::ExprsParser::new();
                    let exprs = parser.parse(code).map_err(|e| Error::invalid_parse(&e))?;
                    exprs
                        .into_iter()
                        .try_fold(Value::empty(), |_, expr| interpreter.evaluate(state, expr))
                }
                _ => Err(Error::invalid_bridge_call(
                    "core.match",
                    &format!("Expected (expr table), but got: {:?}", args),
                )),
            }),
        );

        backend.register(
            "core.equal",
            NativeCall::Function(|_, _, args| {
                let all_equal = args.windows(2).all(|pair| pair[0] == pair[1]);
                Ok(Value::Bool(all_equal))
            }),
        );

        backend.register(
            "core.and",
            NativeCall::Function(|_, _, args| {
                let all_true = args.iter().all(|arg| match arg {
                    Value::Bool(true) => true,
                    _ => false,
                });
                Ok(Value::Bool(all_true))
            }),
        );

        backend.register(
            "core.or",
            NativeCall::Function(|_, _, args| {
                let any_true = args.iter().any(|arg| match arg {
                    Value::Bool(true) => true,
                    _ => false,
                });
                Ok(Value::Bool(any_true))
            }),
        );
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
    fn test_identity() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_exprs(indoc::indoc! {"
                (def-fn! identity (x) x)
                (identity 42)
            "}),
            Ok(Some(Value::Number(42)))
        );
    }

    #[test]
    fn test_call() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {"
                (call + [1 2])
            "}),
            Ok(Value::Number(3))
        );
    }

    #[test]
    fn test_eval() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {r#"
                (eval "(+ 1 2)")
            "#}),
            Ok(Value::Number(3))
        );
    }

    #[test]
    fn test_eval_scope() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {r#"
                (let!
                    { x => 2 }
                     (eval "(+ x 1)"))
            "#}),
            Ok(Value::Number(3))
        );
    }

    #[test]
    fn test_lambda() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {"
                (call (lambda! (a) (+ a a)) [2])
            "}),
            Ok(Value::Number(4))
        );
    }

    #[test]
    fn test_set_vec() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {r#"
                (let! { a => [0] }
                    (do
                        (set a 0 1)
                        (get a 0)))
            "#}),
            Ok(Value::Number(1))
        );
    }

    #[test]
    fn test_last() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {"
                (last [1 2 3])
            "}),
            Ok(Value::Number(3))
        );
    }

    #[test]
    fn test_match() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {r#"
                (match! 2 {
                    1 => undefined-identifier
                    2 => "two"
                })
            "#}),
            Ok(Value::String(String::from("two")))
        );
    }

    #[test]
    fn test_let() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {r#"
                (let! { x => 2 } x)
            "#}),
            Ok(Value::Number(2))
        );
    }

    #[test]
    fn test_do() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {r#"
                (do 1 2 3 4)
            "#}),
            Ok(Value::Number(4))
        );
    }

    #[test]
    fn test_equal() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {r#"
                (equal? [1 2] [1 2] [1 2])
            "#}),
            Ok(Value::Bool(true))
        );

        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {r#"
                (equal? '(1 2) '(1 2))
            "#}),
            Ok(Value::Bool(true))
        );
    }

    #[test]
    fn test_and() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {r#"
                (and? #true #true #true)
            "#}),
            Ok(Value::Bool(true))
        );

        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {r#"
                (and? #true #true #false)
            "#}),
            Ok(Value::Bool(false))
        );
    }

    #[test]
    fn test_or() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {r#"
                (or? #false #false #true)
            "#}),
            Ok(Value::Bool(true))
        );

        assert_eq!(
            runtime.parse_and_evaluate_expr(indoc::indoc! {r#"
                (or? #false #false #false)
            "#}),
            Ok(Value::Bool(false))
        );
    }
}
