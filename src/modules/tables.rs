use crate::interpreter::{Backend, Error, Module, PrintableValue, Value};

pub struct Tables;

impl Module for Tables {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.insert("__core$set", |_, state, args| match args {
            [Value::Table(table), key, value] => {
                table.borrow_mut().insert(key.clone(), value.clone());
                return Ok(Value::empty());
            }
            _ => Err(Error::invalid_native_call(
                "set",
                &format!(
                    "Expected table, key, and value, but got: {}",
                    PrintableValue(state, &Value::List(args.to_vec()))
                ),
            )),
        });
    }

    fn prelude() -> &'static str {
        include_str!("tables.rum")
    }
}

#[cfg(test)]
mod tests {

    use crate::interpreter::{self, Value};

    #[test]
    fn test_set() {
        let mut runtime = interpreter::Runtime::new();
        assert!(runtime.evaluate_expr("(set #Env 'a 1)").is_ok());
        assert_eq!(runtime.evaluate_expr("a"), Ok(Value::Number(1)));
    }
}
