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
    fn test_symbol_to_string() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr("(symbol->string :hello)"),
            Ok(Value::String(":hello".to_string()))
        );
    }
}
