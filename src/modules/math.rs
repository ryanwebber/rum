use crate::{
    interpreter::{Backend, Error, Interpreter, Module, PrintableValue, State, Value},
    types,
};

pub struct Math;

impl Math {
    fn eval_as_numbers(
        interpreter: &Interpreter,
        state: &mut State,
        args: &[Value],
    ) -> Result<Vec<types::Numeric>, Error> {
        args.iter()
            .map(|arg| match interpreter.evaluate(state, arg)? {
                Value::Number(n) => Ok(n),
                _ => Err(Error::invalid_native_call(
                    "+",
                    &format!("Expected number (got {})", PrintableValue(state, arg)),
                )),
            })
            .collect::<Result<Vec<types::Numeric>, Error>>()
    }
}

impl Module for Math {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.insert("__math$add", |interpreter, state, args| {
            let evaluated_args = Self::eval_as_numbers(interpreter, state, args)?;
            match evaluated_args.into_iter().reduce(|acc, item| acc + item) {
                Some(n) => Ok(Value::Number(n)),
                None => Err(Error::invalid_native_call("+", "Expected at least one argument")),
            }
        });

        backend.insert("__math$sub", |interpreter, state, args| {
            let evaluated_args = Self::eval_as_numbers(interpreter, state, args)?;
            match evaluated_args.into_iter().reduce(|acc, item| acc - item) {
                Some(n) => Ok(Value::Number(n)),
                None => Err(Error::invalid_native_call("-", "Expected at least one argument")),
            }
        });

        backend.insert("__math$mul", |interpreter, state, args| {
            let evaluated_args = Self::eval_as_numbers(interpreter, state, args)?;
            match evaluated_args.into_iter().reduce(|acc, item| acc * item) {
                Some(n) => Ok(Value::Number(n)),
                None => Err(Error::invalid_native_call("*", "Expected at least one argument")),
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
        assert_eq!(runtime.evaluate_expr("(+ 4 5)"), Ok(interpreter::Value::Number(9)));
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