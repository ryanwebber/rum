use crate::{
    ast::Expr,
    interpreter::{Backend, Error, Interpreter, Module, NativeCall, State, StaticSymbol, Symbol, Table, Value},
};

pub struct Core;

fn def_fn_impl(
    interpreter: &Interpreter,
    state: &mut State,
    args: &[Expr],
    kind: Option<StaticSymbol>,
) -> Result<Value, Error> {
    match args {
        [Expr::List(nodes)] => {
            let arg_exprs: Vec<Expr> = nodes
                .iter()
                .map(|expr| interpreter.evaluate(state, expr.clone()))
                .map(|value| match value {
                    Err(e) => Err(e),
                    Ok(Value::Expr(expr)) => Ok(expr),
                    Ok(value) => Err(Error::invalid_bridge_call(
                        "core.def-fn",
                        &format!("Expected an expression, but got: {:?}", value),
                    )),
                })
                .collect::<Result<_, _>>()?;

            match &arg_exprs[..] {
                [Expr::Identifier(fname), Expr::List(parameters), body] => {
                    let mut table = Table::new();
                    table.insert(
                        Value::Symbol(Symbol::Static(StaticSymbol::FN_NAME)),
                        state.create_string(fname),
                    );
                    table.insert(
                        Value::Symbol(Symbol::Static(StaticSymbol::FN_BODY)),
                        state.create_expr(body.clone()),
                    );
                    table.insert(
                        Value::Symbol(Symbol::Static(StaticSymbol::FN_PARAMETERS)),
                        state.create_expr(Expr::List(parameters.clone())),
                    );

                    if let Some(kind) = kind {
                        table.insert(
                            Value::Symbol(Symbol::Static(StaticSymbol::FN_TYPE)),
                            Value::Symbol(Symbol::Static(kind)),
                        );
                    }

                    let table = state.create_table(table);
                    let identifier = Symbol::resolve(&fname, state);
                    state.global_scope_mut().set_local(identifier, table.clone());

                    Ok(table)
                }
                _ => Err(Error::invalid_bridge_call(
                    "core.def-fn",
                    &format!("Expected (<ID> <LIST> <EXPR>), but got: {:?}", nodes),
                )),
            }
        }
        _ => Err(Error::invalid_bridge_call(
            "core.def-fn",
            &format!("Malformed core.def-fn bridge call args, got: {:?}", args),
        )),
    }
}

impl Module for Core {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.register(
            "core.def-macro",
            NativeCall::Macro(|interpreter, state, args| {
                def_fn_impl(interpreter, state, args, Some(StaticSymbol::MACRO))
            }),
        );

        backend.register(
            "core.def-fn",
            NativeCall::Macro(|interpreter, state, args| def_fn_impl(interpreter, state, args, None)),
        );

        backend.register(
            "core.call",
            NativeCall::Function(|interpreter, state, args| match args {
                [callee, Value::Vector(args)] => interpreter.call_as_function(state, &callee, &args),
                _ => Err(Error::invalid_bridge_call("core.call", "Expected (callee [args...])")),
            }),
        );

        backend.register(
            "core.get",
            NativeCall::Function(|_, _, args| match args {
                [Value::Table(table), key] => Ok(table.borrow().get(key).cloned().unwrap_or_else(|| Value::empty())),
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
                    Ok(Value::empty())
                }
                _ => Err(Error::invalid_bridge_call(
                    "core.set",
                    &format!("Expected (table|vec key value), but got: {:?}", args),
                )),
            }),
        );

        backend.register(
            "core.last",
            NativeCall::Function(|_, _, args| match args {
                [Value::Vector(vec)] => Ok(vec.last().cloned().unwrap_or_else(|| Value::empty())),
                _ => Err(Error::invalid_bridge_call("core.last", "Expected (vec), but got: {:?}")),
            }),
        );

        backend.register(
            "core.match",
            NativeCall::Macro(|interpreter, state, args| match args {
                [Expr::Identifier(lhs_id), Expr::Identifier(patterns_id)] => {
                    let lhs = interpreter.evaluate(state, Expr::Identifier(lhs_id.clone()))?;
                    let patterns = interpreter.evaluate(state, Expr::Identifier(patterns_id.clone()))?;
                    match (lhs, patterns) {
                        (Value::Expr(lhs), Value::Expr(Expr::Map(patterns))) => {
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
                    }
                }
                _ => unreachable!("core.match: Expected (lhs patterns)"),
            }),
        );

        backend.register(
            "core.let",
            NativeCall::Macro(|interpreter, state, args| match args {
                [Expr::Identifier(assignments_id), Expr::Identifier(expr_id)] => {
                    let assignments = interpreter.evaluate(state, Expr::Identifier(assignments_id.clone()))?;
                    let expr = interpreter.evaluate(state, Expr::Identifier(expr_id.clone()))?;
                    match (assignments, expr) {
                        (Value::Expr(Expr::Map(assignments)), Value::Expr(lhs)) => {
                            for (lhs, expr) in assignments.iter() {
                                if let Expr::Identifier(id) = lhs {
                                    let value = interpreter.evaluate(state, expr.clone())?;
                                    let symbol = Symbol::resolve(id, state);
                                    state.current_scope_mut().set_local(symbol, value);
                                }
                            }

                            // TODO: Should we pop these bindings?
                            interpreter.evaluate(state, lhs)
                        }
                        _ => Err(Error::invalid_bridge_call(
                            "core.match",
                            &format!("Expected (expr table), but got: {:?}", args),
                        )),
                    }
                }
                _ => unreachable!("core.match: Expected (lhs patterns)"),
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
}
