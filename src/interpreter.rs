use core::hash::Hash;
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
enum Arity {
    Any,
    Exactly(usize),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct Symbol(types::Id);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct Identifier(types::Id);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct PseudoValue(types::Id);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Function {
    arity: Arity,
    body: Box<Value>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Value {
    Boolean(bool),
    Function(Function),
    Identifier(Identifier),
    List(Vec<Value>),
    NativeCall,
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
    strings: StringInterner,
    globals: Table,
}

impl State {
    fn new() -> Self {
        State {
            strings: StringInterner::new(),
            globals: Table::new(),
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct Table {
    contents: HashMap<Value, Value>,
    metatable: MetaTable,
}

impl Hash for Table {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {
        todo!("Figure out how to hash table")
    }
}

impl Table {
    fn insert(&mut self, key: Value, value: Value) -> Option<Value> {
        self.contents.insert(key, value)
    }

    fn get(&self, key: &Value) -> Option<&Value> {
        self.contents.get(key)
    }
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
            contents: HashMap::new(),
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
        match state.strings.resolve(sym.0) {
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
    fn register_builtins(&self, backend: &mut Backend) {
        backend.insert("__core$quote", |_, _, args| {
            if args.len() != 1 {
                return Err("Expected one argument to quote");
            }

            Ok(args[0].clone())
        });

        backend.insert("__core$def_fn", |_, state, args| match args {
            [Value::Identifier(id), _, body] => match state.strings.resolve(id.0) {
                None => Err("No such interned string"),
                Some(fname) => {
                    println!("Function: {}", fname);
                    let key = Value::String(fname.to_string());
                    state.globals.insert(
                        key,
                        Value::Function(Function {
                            arity: Arity::Any,
                            body: Box::new(body.clone()),
                        }),
                    );

                    Ok(Value::empty())
                }
            },
            _ => Err("Expected three arguments to def_fn"),
        });
    }
}

struct ArithmeticModule;

impl Module for ArithmeticModule {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.insert("__math$add", |interpreter, state, args| {
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
            | Value::Function(_)
            | Value::Number(_)
            | Value::String(_)
            | Value::Symbol(_)
            | Value::Table(_)
            | Value::Vector(_)
            | Value::NativeCall
            | Value::Unbound => Ok(value.clone()),
            Value::Identifier(id) => match state.strings.resolve(id.0) {
                None => Err("No such interned string"),
                Some(name) => match state.globals.get(&Value::String(name.to_string())) {
                    None => Err("No such global"),
                    Some(value) => Ok(value.clone()),
                },
            },
            Value::PseudoValue(PseudoValue(val)) => match state.strings.resolve(*val) {
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
                    Value::Function(func) => self.evaluate(state, &func.body), // TODO: Handle parameters
                    Value::Table(_table) => todo!(),
                    _ => {
                        println!("Callee: {:?}", callee);
                        Err("Value is not invokable")
                    }
                }),
            },
        }
    }
}

#[cfg(test)]
mod test {

    use super::*;
    use crate::parser;

    struct Runtime {
        state: State,
        parser: parser::ExprParser,
        interpreter: Interpreter,
    }

    impl Runtime {
        fn new() -> Self {
            Runtime {
                state: State::new(),
                parser: parser::ExprParser::new(),
                interpreter: Interpreter::new(),
            }
        }

        fn evaluate(&mut self, value: &Value) -> Result<Value, Error> {
            self.interpreter.evaluate(&mut self.state, value)
        }

        fn parse_and_evaluate(&mut self, input: &str) -> Result<Value, Error> {
            let expr = self.parser.parse(input).unwrap();
            let value = expr.to_value(&mut self.state.strings);
            self.evaluate(&value)
        }
    }

    #[test]
    fn test_ast_meta_protocol() {
        let mut interner = StringInterner::new();
        let parse = parser::ExprParser::new()
            .parse("{ 1 => 2 }")
            .unwrap()
            .to_value(&mut interner);

        assert_eq!(
            parse,
            Value::List(vec![Value::List(vec![Value::Number(1), Value::Number(2)])])
        );
    }

    #[test]
    fn test_evaluate_primitives() {
        let mut runtime = Runtime::new();
        assert_eq!(runtime.parse_and_evaluate("1"), Ok(Value::Number(1)));
        assert_eq!(
            runtime.parse_and_evaluate("\"abc\""),
            Ok(Value::String(String::from("abc")))
        );
        assert_eq!(runtime.parse_and_evaluate("#True"), Ok(Value::Boolean(true)));
        assert_eq!(runtime.parse_and_evaluate("#False"), Ok(Value::Boolean(false)));
        assert_eq!(runtime.parse_and_evaluate("#Yo"), Err("No such value"));
        assert_eq!(runtime.parse_and_evaluate("#Call"), Ok(Value::NativeCall));
        assert_eq!(
            runtime.parse_and_evaluate("[1 () [2]]"),
            Ok(Value::Vector(vec![
                Value::Number(1),
                Value::empty(),
                Value::Vector(vec![Value::Number(2)]),
            ]))
        );
        assert!({
            let result = runtime.evaluate(&Value::Function(Function {
                arity: Arity::Any,
                body: Box::new(Value::Number(1)),
            }));

            match result {
                Ok(Value::Function(_)) => true,
                _ => false,
            }
        });
    }

    #[test]
    fn test_evaluate_quote() {
        let mut runtime = Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate("(#Call :__core$quote 1)"),
            Ok(Value::Number(1))
        );
    }

    #[test]
    fn test_evaluate_add() {
        let mut runtime = Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate("(#Call :__math$add 1 2 3)"),
            Ok(Value::Number(6))
        );
    }

    #[test]
    fn test_evaluate_function_call() {
        let mut runtime = Runtime::new();

        assert_eq!(
            runtime.parse_and_evaluate("(#Call :__core$def_fn add (a b) (#Call :__math$add 2 3))"),
            Ok(Value::empty())
        );

        assert_eq!(runtime.parse_and_evaluate("(add 1 2)"), Ok(Value::Number(5)));
    }
}
