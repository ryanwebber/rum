use crate::interpreter::{Error, Module, NativeCall, Value};

pub struct Math;

impl Math {
    fn apply_binary_op(
        identity: Value,
        args: &[Value],
        op: impl Fn(Value, Value) -> Result<Value, Error>,
    ) -> Result<Value, Error> {
        args.iter()
            .fold(Ok(identity), |acc, arg| acc.and_then(|acc| op(acc, arg.clone())))
    }
}

impl Module for Math {
    fn register_builtins(&self, backend: &mut crate::interpreter::Backend) {
        backend.register(
            "math.addition",
            NativeCall::Function(|_, state, args| {
                Math::apply_binary_op(Value::Number(0), args, |acc, arg| match (acc, arg) {
                    (Value::Number(acc), Value::Number(arg)) => Ok(Value::Number(acc + arg)),
                    (acc, arg) => Err(Error::unsupported_operation(&format!(
                        "Cannot add types {} and {}",
                        acc.display(state),
                        arg.display(state)
                    ))),
                })
            }),
        );

        backend.register(
            "math.subtraction",
            NativeCall::Function(|_, state, args| {
                Math::apply_binary_op(Value::Number(0), args, |acc, arg| match (acc, arg) {
                    (Value::Number(acc), Value::Number(arg)) => Ok(Value::Number(acc - arg)),
                    (acc, arg) => Err(Error::unsupported_operation(&format!(
                        "Cannot subtract types {} and {}",
                        acc.display(state),
                        arg.display(state)
                    ))),
                })
            }),
        );
    }

    fn prelude() -> &'static str {
        include_str!("math.rum")
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter;
    use crate::interpreter::Value;

    #[test]
    fn test_addition() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(runtime.parse_and_evaluate_expr("(+ 1 2 3)"), Ok(Value::Number(6)));
    }
}
