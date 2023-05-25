use std::collections::BTreeMap;

use crate::{ast, parser, types};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Value {
    Boolean(bool),
    Extern(Extern),
    List(Vec<Value>),
    Numbers(types::Numeric),
    Strings(String),
    Symbol(Symbol),
    Unbound,
    Vector(Vec<Value>),
    Table(Table),
}

impl Value {
    fn empty() -> Value {
        Value::List(vec![])
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Table {
    contents: BTreeMap<Value, Value>,
    metatable: Option<Box<Table>>,
}

impl Table {
    fn new() -> Self {
        Table {
            contents: BTreeMap::new(),
            metatable: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Symbol {
    id: types::Id,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Extern {
    id: types::Id,
}

struct Interpreter {
    global: Table,
}

impl Interpreter {
    fn new() -> Self {
        Interpreter { global: Table::new() }
    }

    fn evaluate(&mut self, expr: &ast::Expr) -> Result<Value, ()> {
        Err(())
    }
}

#[cfg(test)]
mod test {

    use super::*;

    fn evaluate(input: &str) -> Value {
        let parser = parser::ExprParser::new();
        let expr = match parser.parse(input) {
            Ok(expr) => expr,
            Err(err) => panic!("Error parsing expression: {:?}", err),
        };

        let mut interpreter = Interpreter::new();
        match interpreter.evaluate(&expr) {
            Ok(value) => value,
            Err(err) => panic!("Error evaluating expression: {:?}", err),
        }
    }

    #[test]
    fn test_evaluate() {
        assert!(evaluate("()") == Value::empty());
    }
}
