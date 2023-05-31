use crate::interpreter::{Backend, Error, Module, PrintableValue, Value};

pub struct Math;

impl Module for Math {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.insert("__math$add", |interpreter, state, args| {
            let mut sum = 0;
            for arg in args {
                match interpreter.evaluate(state, arg) {
                    Ok(Value::Number(n)) => sum += n,
                    Ok(_) => {
                        return Err(Error::invalid_native_call(
                            "+",
                            &format!("Expected number (got {})", PrintableValue(state, arg)),
                        ))
                    }
                    Err(err) => return Err(err),
                }
            }
            Ok(Value::Number(sum))
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
}
