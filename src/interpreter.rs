use std::collections::BTreeMap;

use crate::{ast, interner, types};

type StringInterner = interner::StringInterner<types::Id>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Value {
    Boolean(bool),
    Identifier(types::Id),
    List(Vec<Value>),
    Number(types::Numeric),
    String(String),
    Symbol(types::Id),
    Table(Table),
    Unbound,
    Value(types::Id),
    Vector(Vec<Value>),
}

impl Value {
    fn empty() -> Value {
        Value::List(vec![])
    }
}

struct State {
    string_interner: StringInterner,
}

impl State {
    fn new() -> Self {
        State {
            string_interner: StringInterner::new(),
        }
    }
}

trait MetaProtocol {
    fn to_value(&self, string_interner: &mut StringInterner) -> Value;
}

impl<'a> MetaProtocol for ast::Expr<'a> {
    fn to_value(&self, string_interner: &mut StringInterner) -> Value {
        match self {
            ast::Expr::String(s) => Value::String(s.to_string()),
            ast::Expr::Number(n) => Value::Number(*n),
            ast::Expr::Path(p) => Value::List(p.iter().map(|s| Value::String(s.to_string())).collect()),
            ast::Expr::Vector(v) => Value::Vector(v.iter().map(|e| e.to_value(string_interner)).collect()),
            ast::Expr::List(items) => Value::List(items.iter().map(|e| e.to_value(string_interner)).collect()),
            ast::Expr::Map(m) => {
                let m: Vec<Value> = m
                    .iter()
                    .map(|(k, v)| Value::List(vec![k.to_value(string_interner), v.to_value(string_interner)]))
                    .collect();

                Value::List(m)
            }
            ast::Expr::Identifier(id) => Value::Identifier(string_interner.get_or_intern(id)),
            ast::Expr::Symbol(sym) => Value::Symbol(string_interner.get_or_intern(sym)),
            ast::Expr::Value(val) => Value::Value(string_interner.get_or_intern(val)),
            ast::Expr::Placeholder(_) => todo!(), // Not sure what to do here - can we use `unbound` and metatables?
        }
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

struct Interpreter {}

impl Interpreter {
    fn new() -> Self {
        Interpreter {}
    }

    fn evaluate(&mut self, state: &mut State, value: &Value) -> Result<Value, ()> {
        match value {
            Value::Boolean(_)
            | Value::Number(_)
            | Value::String(_)
            | Value::Symbol(_)
            | Value::Table(_)
            | Value::Vector(_)
            | Value::Unbound => Ok(value.clone()),
            Value::Identifier(_id) => todo!(),
            Value::Value(val) => match state.string_interner.resolve(*val) {
                None => Err(()),
                Some("True") => Ok(Value::Boolean(true)),
                Some("False") => Ok(Value::Boolean(false)),
                Some(_) => Err(()),
            },
            Value::List(items) => match items.split_first() {
                None => Ok(Value::empty()),
                Some((_first, _rest)) => todo!(),
            },
        }
    }
}

#[cfg(test)]
mod test {

    use super::*;
    use crate::parser;

    fn parse(input: &str) -> ast::Expr {
        let parser = parser::ExprParser::new();
        match parser.parse(input) {
            Ok(expr) => expr,
            Err(err) => panic!("Error parsing expression: {:?}", err),
        }
    }

    fn evaluate(input: &str) -> Value {
        let mut state = State::new();
        let mut interpreter = Interpreter::new();
        let value = parse(input).to_value(&mut state.string_interner);
        match interpreter.evaluate(&mut state, &value) {
            Ok(value) => value,
            Err(err) => panic!("Error evaluating expression: {:?}", err),
        }
    }

    fn throws_condition(input: &str) -> () {
        let mut state = State::new();
        let mut interpreter = Interpreter::new();
        let value = parse(input).to_value(&mut state.string_interner);
        match interpreter.evaluate(&mut state, &value) {
            Ok(value) => panic!("Expected condition but got: {:?}", value),
            Err(err) => err,
        }
    }

    #[test]
    fn test_ast_meta_protocol() {
        let mut interner = StringInterner::new();
        assert_eq!(
            parse("{ 1 => 2 }").to_value(&mut interner),
            Value::List(vec![Value::List(vec![Value::Number(1), Value::Number(2)])])
        );
    }

    #[test]
    fn test_evaluate() {
        assert_eq!(evaluate("1"), Value::Number(1));
        assert_eq!(evaluate(":symbol"), Value::Symbol(0));
        assert_eq!(evaluate("\"abc\""), Value::String(String::from("abc")));
        assert_eq!(evaluate("#True"), Value::Boolean(true));

        assert_eq!(
            evaluate("[1 () [2]]"),
            Value::Vector(vec![
                Value::Number(1),
                Value::empty(),
                Value::Vector(vec![Value::Number(2)])
            ])
        );

        assert!(throws_condition("#Yo") == ());
    }
}
