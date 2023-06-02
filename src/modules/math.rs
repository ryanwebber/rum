use crate::{
    interpreter::{Backend, Error, Module, NativeCallType, PrintableValue, State, Value},
    types,
};

pub struct Math;

impl Math {
    fn as_numbers(state: &mut State, args: &[Value]) -> Result<Vec<types::Numeric>, Error> {
        args.iter()
            .map(|arg| match arg {
                Value::Number(n) => Ok(*n),
                _ => Err(Error::invalid_bridge_call(
                    "+",
                    &format!("Expected number (got {})", PrintableValue(state, arg)),
                )),
            })
            .collect::<Result<Vec<types::Numeric>, Error>>()
    }
}

impl Module for Math {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.register("__math$add", NativeCallType::Default, |_, state, args| {
            let evaluated_args = Self::as_numbers(state, args)?;
            match evaluated_args.into_iter().reduce(|acc, item| acc + item) {
                Some(n) => Ok(Value::Number(n)),
                None => Err(Error::invalid_bridge_call("+", "Expected at least one argument")),
            }
        });

        backend.register("__math$sub", NativeCallType::Default, |_, state, args| {
            let evaluated_args = Self::as_numbers(state, args)?;
            match evaluated_args.into_iter().reduce(|acc, item| acc - item) {
                Some(n) => Ok(Value::Number(n)),
                None => Err(Error::invalid_bridge_call("-", "Expected at least one argument")),
            }
        });

        backend.register("__math$mul", NativeCallType::Default, |_, state, args| {
            let evaluated_args = Self::as_numbers(state, args)?;
            match evaluated_args.into_iter().reduce(|acc, item| acc * item) {
                Some(n) => Ok(Value::Number(n)),
                None => Err(Error::invalid_bridge_call("*", "Expected at least one argument")),
            }
        });
    }

    fn prelude() -> &'static str {
        include_str!("math.rum")
    }
}

#[cfg(test)]
mod tests {

    use crate::interpreter;

    #[test]
    fn test_add() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(runtime.evaluate_expr("(+ 1 2 3)"), Ok(interpreter::Value::Number(6)));
    }

    #[test]
    fn test_sub() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(runtime.evaluate_expr("(- 9 5)"), Ok(interpreter::Value::Number(4)));
    }

    #[test]
    fn test_mul() {
        let mut runtime = interpreter::Runtime::new();
        assert_eq!(runtime.evaluate_expr("(* 4 5)"), Ok(interpreter::Value::Number(20)));
    }
}
