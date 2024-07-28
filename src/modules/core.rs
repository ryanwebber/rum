use crate::{
    ast::Expr,
    interpreter::{Backend, Error, Module, PrintableValue, Value},
};

pub struct Core;

impl Module for Core {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.register("core.def-fn", |interpreter, state, args| match args {
            [Value::Expr(Expr::List(nodes))] => match &nodes[..] {
                [Expr::Identifier(name), Expr::List(parameters), body] => {
                    todo!("def-fn! {} {:?}", name, parameters)
                }
                _ => Err(Error::invalid_bridge_call(
                    "core.def-fn",
                    &format!("Expected (<ID> <LIST> <EXPR>), but got: {:?}", nodes),
                )),
            },
            _ => Err(Error::invalid_bridge_call(
                "core.def-fn",
                &format!("core.def-fn bridge arguments should be quoted"),
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

    // #[test]
    // fn test_apply() {
    //     let mut runtime = interpreter::Runtime::new();
    //     assert_eq!(runtime.evaluate_expr("(apply + '(1 2))"), Ok(Value::Number(3)));
    // }
}
