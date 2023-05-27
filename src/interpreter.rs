use std::collections::BTreeMap;
use std::collections::HashMap;

use crate::{ast, interner, types};

enum ErrorType {
    InconsistentState,
    ValueNotCallable,
    UnknownPseudoValue,
}

type Error = &'static str;
type StringInterner = interner::StringInterner<types::Id>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct Symbol(types::Id);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct Identifier(types::Id);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct PseudoValue(types::Id);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Value {
    Boolean(bool),
    NativeCall,
    Identifier(Identifier),
    List(Vec<Value>),
    Number(types::Numeric),
    PseudoValue(PseudoValue),
    String(String),
    Symbol(Symbol),
    Table(Table),
    Unbound,
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
            ast::Expr::Identifier(id) => Value::Identifier(Identifier(string_interner.get_or_intern(id))),
            ast::Expr::Symbol(sym) => Value::Symbol(Symbol(string_interner.get_or_intern(sym))),
            ast::Expr::PseudoValue(val) => Value::PseudoValue(PseudoValue(string_interner.get_or_intern(val))),
            ast::Expr::Placeholder(_) => todo!(), // Not sure what to do here - can we use `unbound` and metatables?
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Table {
    contents: BTreeMap<Value, Value>,
    metatable: MetaTable,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct MetaTable {
    table: Option<Box<Table>>,
}

impl MetaTable {
    fn new() -> Self {
        MetaTable { table: None }
    }
}

impl Table {
    fn new() -> Self {
        Table {
            contents: BTreeMap::new(),
            metatable: MetaTable::new(),
        }
    }
}

type Call = fn(&Interpreter, &mut State, &[Value]) -> Result<Value, Error>;
struct Backend {
    builtins: HashMap<&'static str, Call>,
}

impl Backend {
    fn new() -> Self {
        Backend {
            builtins: HashMap::new(),
        }
    }

    fn insert(&mut self, name: &'static str, call: Call) {
        self.builtins.insert(name, call);
    }

    fn try_call(
        &self,
        interpreter: &Interpreter,
        state: &mut State,
        sym: Symbol,
        args: &[Value],
    ) -> Result<Value, Error> {
        match state.string_interner.resolve(sym.0) {
            None => Err("No such interned string"),
            Some(name) => match self.builtins.get(&name[1..]) {
                None => Err("No such builtin"),
                Some(call) => call(interpreter, state, args),
            },
        }
    }
}

trait Module {
    fn register_builtins(&self, backend: &mut Backend);
}

struct CoreModule;

impl Module for CoreModule {
    fn register_builtins(&self, _backend: &mut Backend) {}
}

struct ArithmeticModule;

impl Module for ArithmeticModule {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.insert("add", |interpreter, state, args| {
            let mut sum = 0;
            for arg in args {
                match interpreter.evaluate(state, arg) {
                    Ok(Value::Number(n)) => sum += n,
                    Ok(_) => return Err("Expected number"),
                    Err(err) => return Err(err),
                }
            }
            Ok(Value::Number(sum))
        });
    }
}

struct Interpreter {
    backend: Backend,
}

impl Interpreter {
    fn new() -> Self {
        let mut interpreter = Interpreter {
            backend: Backend::new(),
        };

        // Load the default modules we literally can't run without
        interpreter.load_module(&CoreModule);
        interpreter.load_module(&ArithmeticModule);

        interpreter
    }

    fn load_module<T: Module>(&mut self, module: &T) {
        module.register_builtins(&mut self.backend);
    }

    fn evaluate(&self, state: &mut State, value: &Value) -> Result<Value, Error> {
        match value {
            Value::Boolean(_)
            | Value::Number(_)
            | Value::String(_)
            | Value::Symbol(_)
            | Value::Table(_)
            | Value::Vector(_)
            | Value::NativeCall
            | Value::Unbound => Ok(value.clone()),
            Value::Identifier(_id) => todo!(),
            Value::PseudoValue(PseudoValue(val)) => match state.string_interner.resolve(*val) {
                None => Err("No such interned string"),
                Some("Call") => Ok(Value::NativeCall),
                Some("True") => Ok(Value::Boolean(true)),
                Some("False") => Ok(Value::Boolean(false)),
                Some(_) => Err("No such value"),
            },
            Value::List(items) => match items.split_first() {
                None => Ok(Value::empty()),
                Some((first, args)) => self.evaluate(state, first).and_then(|callee| match callee {
                    Value::NativeCall => match args {
                        [] => Err("No arguments to native call"),
                        [Value::Symbol(sym), args @ ..] => self.backend.try_call(self, state, *sym, args),
                        _ => Err("Native call expects symbol as first argument"),
                    },
                    Value::Table(_table) => todo!(),
                    _ => Err("Value is not invokable"),
                }),
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
        let interpreter = Interpreter::new();
        let value = parse(input).to_value(&mut state.string_interner);
        match interpreter.evaluate(&mut state, &value) {
            Ok(value) => value,
            Err(err) => panic!("Error evaluating expression: {:?}", err),
        }
    }

    fn throws_condition(input: &str) -> () {
        let mut state = State::new();
        let interpreter = Interpreter::new();
        let value = parse(input).to_value(&mut state.string_interner);
        match interpreter.evaluate(&mut state, &value) {
            Ok(value) => panic!("Expected condition but got: {:?}", value),
            Err(_) => (),
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
    fn test_evaluate_primitives() {
        assert_eq!(evaluate("1"), Value::Number(1));
        assert_eq!(evaluate(":symbol"), Value::Symbol(Symbol(0)));
        assert_eq!(evaluate("\"abc\""), Value::String(String::from("abc")));
        assert_eq!(evaluate("#True"), Value::Boolean(true));
        assert_eq!(evaluate("#Call"), Value::NativeCall);

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

    #[test]
    fn test_evaluate_add() {
        assert_eq!(evaluate("(#Call :add 1 (#Call :add 2 3))"), Value::Number(6));
    }
}
