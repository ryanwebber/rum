use core::hash::Hash;
use std::{
    collections::HashMap,
    fmt::{Display, Formatter},
};

use crate::{ast, interner, parser, types};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ErrorType {
    InconsistentState,
    InvalidNativeCall,
    InvalidParse,
    UnboundIdentifier,
    UnknownNativeCall,
    UnknownPseudoValue,
    ValueNotCallable,
}

type StringInterner = interner::StringInterner<types::Id>;

#[derive(Debug)]
pub struct Error {
    error_type: ErrorType,
    message: String,
}

impl Error {
    fn invalid_native_call(call: &str) -> Error {
        Error {
            error_type: ErrorType::InvalidNativeCall,
            message: format!("Invalid native call: {}", call),
        }
    }

    fn invalid_parse<T>(error: &T) -> Error
    where
        T: std::error::Error,
    {
        Error {
            error_type: ErrorType::InvalidParse,
            message: format!("Invalid parse: {:?}", error),
        }
    }

    fn no_such_string() -> Error {
        Error {
            error_type: ErrorType::InconsistentState,
            message: String::from("No such interned string"),
        }
    }

    fn unbound_identifier(id: &str) -> Error {
        Error {
            error_type: ErrorType::UnboundIdentifier,
            message: format!("Unbound identifier: {}", id),
        }
    }

    fn unknown_native_call(name: &str) -> Error {
        Error {
            error_type: ErrorType::UnknownNativeCall,
            message: format!("Unknown native call: {}", name),
        }
    }

    fn unknown_pseudo_value(name: &str) -> Error {
        Error {
            error_type: ErrorType::UnknownPseudoValue,
            message: format!("Unknown pseudo value: {}", name),
        }
    }

    fn value_not_callable(value: &Value) -> Error {
        Error {
            error_type: ErrorType::ValueNotCallable,
            message: format!("Value is not callable: {:?}", value),
        }
    }
}

impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        self.error_type == other.error_type && self.message == other.message
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}]",
            match self.error_type {
                ErrorType::InconsistentState => "InconsistentState",
                ErrorType::InvalidNativeCall => "InvalidNativeCall",
                ErrorType::InvalidParse => "InvalidParse",
                ErrorType::UnboundIdentifier => "UnboundIdentifier",
                ErrorType::UnknownNativeCall => "UnknownNativeCall",
                ErrorType::UnknownPseudoValue => "UnknownPseudoValue",
                ErrorType::ValueNotCallable => "ValueNotCallable",
            }
        )?;

        write!(f, " {}", self.message)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum Arity {
    Any,
    Exactly(usize),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Symbol(types::Id);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Identifier(types::Id);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct PseudoValue(types::Id);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    arity: Arity,
    body: Box<Value>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
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

struct FunctionClosure {
    function: Function,
    environment: Table,
    upvalues: Vec<Value>,
}

pub struct State {
    strings: StringInterner,
    globals: Table,
}

impl State {
    pub fn new() -> Self {
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
pub struct Table {
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

pub type Call = fn(&Interpreter, &mut State, &[Value]) -> Result<Value, Error>;
pub struct Backend {
    builtins: HashMap<&'static str, Call>,
}

impl Backend {
    fn new() -> Self {
        Backend {
            builtins: HashMap::new(),
        }
    }

    pub fn insert(&mut self, name: &'static str, call: Call) {
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
            None => Err(Error::no_such_string()),
            Some(name) => match self.builtins.get(&name[1..]) {
                None => Err(Error::unknown_native_call(name)),
                Some(call) => call(interpreter, state, args),
            },
        }
    }
}

pub trait Module
where
    Self: Sized,
{
    fn register_builtins(&self, backend: &mut Backend);

    fn prelude() -> &'static str {
        ""
    }
}

struct CoreModule;

impl Module for CoreModule {
    fn register_builtins(&self, backend: &mut Backend) {
        backend.insert("__core$quote", |_, _, args| {
            if args.len() != 1 {
                return Err(Error::invalid_native_call("quote"));
            }

            Ok(args[0].clone())
        });

        backend.insert("__core$def_fn", |_, state, args| match args {
            [Value::Identifier(id), Value::List(args), body] => {
                state.globals.insert(
                    Value::Identifier(*id),
                    Value::Function(Function {
                        arity: Arity::Exactly(args.len()),
                        body: Box::new(body.clone()),
                    }),
                );

                Ok(Value::empty())
            }
            _ => Err(Error::invalid_native_call("def-fn")),
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
                    Ok(_) => return Err(Error::invalid_native_call("+")),
                    Err(err) => return Err(err),
                }
            }
            Ok(Value::Number(sum))
        });
    }

    fn prelude() -> &'static str {
        include_str!("pkg/math.rum")
    }
}

pub struct Interpreter {
    backend: Backend,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            backend: Backend::new(),
        }
    }

    pub fn evaluate(&self, state: &mut State, value: &Value) -> Result<Value, Error> {
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
            Value::Identifier(id) => match state.globals.get(value) {
                None => Err(Error::unbound_identifier(state.strings.resolve(id.0).unwrap_or("<?>"))),
                Some(value) => Ok(value.clone()),
            },
            Value::PseudoValue(PseudoValue(val)) => match state.strings.resolve(*val) {
                None => Err(Error::no_such_string()),
                Some("Call") => Ok(Value::NativeCall),
                Some("Nil") => Ok(Value::Unbound),
                Some("True") => Ok(Value::Boolean(true)),
                Some("False") => Ok(Value::Boolean(false)),
                Some(name) => Err(Error::unknown_pseudo_value(name)),
            },
            Value::List(items) => match items.split_first() {
                None => Ok(Value::empty()),
                Some((first, args)) => self.evaluate(state, first).and_then(|callee| match callee {
                    Value::NativeCall => match args {
                        [] => Err(Error::invalid_native_call("<no name>")),
                        [Value::Symbol(sym), args @ ..] => self.backend.try_call(self, state, *sym, args),
                        _ => Err(Error::invalid_native_call("<bad name>")),
                    },
                    Value::Function(func) => self.evaluate(state, &func.body), // TODO: Handle parameters
                    Value::Table(_table) => todo!(),
                    _ => Err(Error::value_not_callable(&callee)),
                }),
            },
        }
    }
}

struct Parsers {
    expr: parser::ExprParser,
    exprs: parser::ExprsParser,
}

pub struct Runtime {
    state: State,
    interpreter: Interpreter,
    parsers: Parsers,
}

impl Runtime {
    pub fn new() -> Self {
        let mut runtime = Runtime {
            state: State::new(),
            interpreter: Interpreter::new(),
            parsers: Parsers {
                expr: parser::ExprParser::new(),
                exprs: parser::ExprsParser::new(),
            },
        };

        runtime.load_module(&CoreModule).unwrap();
        runtime.load_module(&ArithmeticModule).unwrap();

        runtime
    }

    pub fn load_module<T: Module>(&mut self, module: &T) -> Result<(), Error> {
        module.register_builtins(&mut self.interpreter.backend);
        self.evaluate_exprs(T::prelude()).map(|_| ())
    }

    pub fn evaluate(&mut self, value: &Value) -> Result<Value, Error> {
        self.interpreter.evaluate(&mut self.state, value)
    }

    pub fn evaluate_expr(&mut self, input: &str) -> Result<Value, Error> {
        self.parsers
            .expr
            .parse(input)
            .map_err(|err| Error::invalid_parse(&err))
            .and_then(|expr| {
                let value = expr.to_value(&mut self.state.strings);
                self.evaluate(&value)
            })
    }

    pub fn evaluate_exprs(&mut self, input: &str) -> Result<(), Error> {
        self.parsers
            .exprs
            .parse(input)
            .map_err(|err| Error::invalid_parse(&err))
            .and_then(|exprs| {
                exprs
                    .into_iter()
                    .map(|expr| {
                        let value = expr.to_value(&mut self.state.strings);
                        self.evaluate(&value)
                    })
                    .collect::<Result<Vec<Value>, Error>>()
                    .map(|_| ())
            })
    }
}

#[cfg(test)]
mod test {

    use super::*;
    use crate::parser;

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
        assert_eq!(runtime.evaluate_expr("1"), Ok(Value::Number(1)));
        assert_eq!(runtime.evaluate_expr("\"abc\""), Ok(Value::String(String::from("abc"))));
        assert_eq!(runtime.evaluate_expr("#True"), Ok(Value::Boolean(true)));
        assert_eq!(runtime.evaluate_expr("#False"), Ok(Value::Boolean(false)));
        assert_eq!(runtime.evaluate_expr("#Yo"), Err(Error::unknown_pseudo_value("Yo")));
        assert_eq!(runtime.evaluate_expr("#Call"), Ok(Value::NativeCall));
        assert_eq!(
            runtime.evaluate_expr("[1 () [2]]"),
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
        assert_eq!(runtime.evaluate_expr("(#Call :__core$quote 1)"), Ok(Value::Number(1)));
    }

    #[test]
    fn test_evaluate_add() {
        let mut runtime = Runtime::new();
        assert_eq!(runtime.evaluate_expr("(#Call :__math$add 1 2 3)"), Ok(Value::Number(6)));
    }

    #[test]
    fn test_evaluate_function_call() {
        let mut runtime = Runtime::new();

        assert_eq!(
            runtime.evaluate_expr("(#Call :__core$def_fn add (a b) (#Call :__math$add a b))"),
            Ok(Value::empty())
        );

        assert_eq!(runtime.evaluate_expr("(add 1 (add 2 3))"), Ok(Value::Number(5)));
    }
}
