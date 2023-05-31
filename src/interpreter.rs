use core::{fmt, hash::Hash};
use std::{
    collections::HashMap,
    fmt::{Display, Formatter},
    rc::Rc,
};

use crate::{ast, gc::Gc, interner, modules, parser, types};

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
    pub fn invalid_native_call(call: &str, msg: &str) -> Error {
        Error {
            error_type: ErrorType::InvalidNativeCall,
            message: format!("Invalid native call: {} ({})", call, msg),
        }
    }

    pub fn invalid_parse<T>(error: &T) -> Error
    where
        T: std::error::Error,
    {
        Error {
            error_type: ErrorType::InvalidParse,
            message: format!("Invalid parse: {:?}", error),
        }
    }

    pub fn no_such_string() -> Error {
        Error {
            error_type: ErrorType::InconsistentState,
            message: String::from("No such interned string"),
        }
    }

    pub fn unbound_identifier(id: &str) -> Error {
        Error {
            error_type: ErrorType::UnboundIdentifier,
            message: format!("Unbound identifier: {}", id),
        }
    }

    pub fn unknown_native_call(name: &str) -> Error {
        Error {
            error_type: ErrorType::UnknownNativeCall,
            message: format!("Unknown native call: {}", name),
        }
    }

    pub fn unknown_pseudo_value(name: &str) -> Error {
        Error {
            error_type: ErrorType::UnknownPseudoValue,
            message: format!("Unknown pseudo value: {}", name),
        }
    }

    pub fn value_not_callable(value: PrintableValue<'_>) -> Error {
        Error {
            error_type: ErrorType::ValueNotCallable,
            message: format!("Value is not callable: {}", value),
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
pub struct Symbol(pub types::Id);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Identifier(pub types::Id);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct PseudoValue(pub types::Id);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    pub body: Box<Value>,
    pub parameters: Vec<Identifier>,
    pub is_macro: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NativeCallType {
    Call,
    Macro,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Boolean(bool),
    Function(Function),
    Identifier(Identifier),
    List(Vec<Value>),
    NativeCall(NativeCallType),
    Number(types::Numeric),
    PseudoValue(PseudoValue),
    String(String),
    Symbol(Symbol),
    Table(Gc<Table>),
    Unbound,
    Vector(Vec<Value>),
}

impl Value {
    pub fn empty() -> Value {
        Value::List(vec![])
    }
}

pub struct SharedIdentifiers {
    globals: Identifier,
    parent_scope: Identifier,
}

pub struct State {
    pub strings: StringInterner,
    pub identifiers: Rc<SharedIdentifiers>,
    pub environment: Gc<Table>,
}

impl State {
    pub fn new() -> Self {
        let mut strings = StringInterner::new();
        let identifiers = Rc::new(SharedIdentifiers {
            globals: Identifier(strings.get_or_intern("__globals")),
            parent_scope: Identifier(strings.get_or_intern("__parent_scope")),
        });

        let environment = Gc::new(Table::new());

        State {
            strings,
            identifiers,
            environment,
        }
    }

    pub fn resolve(&self, identifier: &Identifier) -> Option<Value> {
        self.environment
            .borrow()
            .get(&Value::Identifier(*identifier))
            .map(|v| v.clone())
            .or_else(|| {
                if let Some(parent) = self
                    .environment
                    .borrow()
                    .get(&Value::Identifier(self.identifiers.parent_scope))
                {
                    match parent {
                        Value::Table(table) => {
                            let parent_state = State {
                                strings: self.strings.clone(),
                                identifiers: self.identifiers.clone(),
                                environment: table.clone(),
                            };

                            return parent_state.resolve(identifier);
                        }
                        _ => {}
                    }
                }

                None
            })
    }

    pub fn try_resolve(&self, identifier: &Identifier) -> Result<Value, Error> {
        match self.resolve(identifier) {
            None => Err(Error::unbound_identifier(
                self.strings.resolve(identifier.0).unwrap_or("<?>"),
            )),
            Some(value) => Ok(value),
        }
    }

    pub fn globals(&self) -> Gc<Table> {
        match self
            .environment
            .borrow()
            .get(&Value::Identifier(self.identifiers.globals))
        {
            None => self.environment.clone(),
            Some(Value::Table(table)) => table.clone(),
            _ => unreachable!(),
        }
    }

    pub fn closing(&self, function: &Function, parameters: Vec<Value>) -> State {
        let mut state = State::new();
        state.strings = self.strings.clone();

        state.environment.borrow_mut().contents.insert(
            Value::Identifier(self.identifiers.parent_scope),
            Value::Table(self.environment.clone()),
        );

        state.environment.borrow_mut().contents.insert(
            Value::Identifier(self.identifiers.globals),
            Value::Table(self.globals()),
        );

        for (value, name) in parameters.into_iter().zip(function.parameters.iter()) {
            state.environment.borrow_mut().insert(Value::Identifier(*name), value);
        }

        state
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

pub struct PrintableValue<'a>(pub &'a State, pub &'a Value);

impl<'a> Display for PrintableValue<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.1 {
            Value::Identifier(id) => match self.0.strings.resolve(id.0) {
                None => write!(f, "'<???>"),
                Some(name) => write!(f, "'{}", name),
            },
            Value::Symbol(sym) => match self.0.strings.resolve(sym.0) {
                None => write!(f, ":<???>"),
                Some(name) => write!(f, ":{}", name),
            },
            Value::PseudoValue(pseudo) => match self.0.strings.resolve(pseudo.0) {
                None => write!(f, "#<???>"),
                Some(name) => write!(f, "#{}", name),
            },
            Value::Boolean(b) => write!(f, "#{}", if *b { "True" } else { "False" }),
            Value::Function(_) => write!(f, "<function>"),
            Value::List(items) => {
                write!(f, "'(")?;
                for item in items {
                    write!(f, "{} ", PrintableValue(self.0, item))?;
                }
                write!(f, ")")
            }
            Value::NativeCall(_) => write!(f, "<native-call>"),
            Value::Number(n) => write!(f, "{}", n),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Table(table) => {
                write!(f, "{{")?;
                for (key, value) in &table.borrow().contents {
                    write!(
                        f,
                        "{}: {}, ",
                        PrintableValue(self.0, &key),
                        PrintableValue(self.0, &value)
                    )?;
                }
                write!(f, "}}")
            }
            Value::Unbound => write!(f, "#Nil"),
            Value::Vector(items) => {
                write!(f, "[")?;
                for item in items {
                    write!(f, "{} ", PrintableValue(self.0, item))?;
                }
                write!(f, "]")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Table {
    contents: HashMap<Value, Value>,
    metatable: MetaTable,
}

impl Table {
    pub fn new() -> Self {
        Table {
            contents: HashMap::new(),
            metatable: MetaTable::new(),
        }
    }

    pub fn insert(&mut self, key: Value, value: Value) -> Option<Value> {
        self.contents.insert(key, value)
    }

    pub fn get(&self, key: &Value) -> Option<&Value> {
        self.contents.get(key)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct MetaTable {
    table: Option<Gc<Table>>,
}

impl MetaTable {
    fn new() -> Self {
        MetaTable { table: None }
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
        call_type: NativeCallType,
    ) -> Result<Value, Error> {
        match state.strings.resolve(sym.0) {
            None => Err(Error::no_such_string()),
            Some(name) => match self.builtins.get(&name[1..]) {
                None => Err(Error::unknown_native_call(name)),
                Some(call) => {
                    let args = match call_type {
                        NativeCallType::Macro => args.to_vec(),
                        NativeCallType::Call => args
                            .iter()
                            .map(|arg| interpreter.evaluate(state, arg))
                            .collect::<Result<Vec<Value>, Error>>()?,
                    };

                    call(interpreter, state, &args)
                }
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
            | Value::NativeCall(_)
            | Value::Unbound => Ok(value.clone()),
            Value::Identifier(id) => state.try_resolve(id).map(|v| v.clone()),
            Value::PseudoValue(PseudoValue(val)) => match state.strings.resolve(*val) {
                None => Err(Error::no_such_string()),
                Some("Call") => Ok(Value::NativeCall(NativeCallType::Call)),
                Some("CallMacro") => Ok(Value::NativeCall(NativeCallType::Macro)),
                Some("Env") => Ok(Value::Table(state.environment.clone())),
                Some("Nil") => Ok(Value::Unbound),
                Some("True") => Ok(Value::Boolean(true)),
                Some("False") => Ok(Value::Boolean(false)),
                Some(name) => Err(Error::unknown_pseudo_value(name)),
            },
            Value::List(items) => match items.split_first() {
                None => Ok(Value::empty()),
                Some((first, args)) => self.evaluate(state, first).and_then(|callee| match &callee {
                    Value::NativeCall(call_type) => match args {
                        [] => Err(Error::invalid_native_call(
                            "<no name>",
                            "Expected at least one argument",
                        )),
                        [Value::Symbol(sym), args @ ..] => self.backend.try_call(self, state, *sym, args, *call_type),
                        _ => Err(Error::invalid_native_call("<bad name>", "Expected symbol")),
                    },
                    Value::Function(func) => {
                        let evaluated_args = match func.is_macro {
                            true => args.to_vec(),
                            false => args
                                .iter()
                                .map(|arg| self.evaluate(state, arg))
                                .collect::<Result<Vec<Value>, Error>>()?,
                        };

                        let mut scope_state = state.closing(&func, evaluated_args);
                        self.evaluate(&mut scope_state, &func.body)
                    }
                    Value::Table(_table) => todo!(),
                    _ => Err(Error::value_not_callable(PrintableValue(state, &callee))),
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

        runtime.load_module(&modules::core::Core).unwrap();
        runtime.load_module(&modules::math::Math).unwrap();
        runtime.load_module(&modules::lists::Lists).unwrap();
        runtime.load_module(&modules::tables::Tables).unwrap();

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

    pub fn print_value<'a>(&'a self, value: &'a Value) -> PrintableValue<'a> {
        PrintableValue(&self.state, value)
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
        assert_eq!(
            runtime.evaluate_expr("#Call"),
            Ok(Value::NativeCall(NativeCallType::Call))
        );
        assert_eq!(
            runtime.evaluate_expr("[1 () [2]]"),
            Ok(Value::Vector(vec![
                Value::Number(1),
                Value::empty(),
                Value::Vector(vec![Value::Number(2)]),
            ]))
        );

        assert!(matches!(runtime.evaluate_expr("#Env"), Ok(Value::Table(_))));

        assert!({
            let result = runtime.evaluate(&Value::Function(Function {
                body: Box::new(Value::Number(1)),
                parameters: vec![],
                is_macro: false,
            }));

            match result {
                Ok(Value::Function(_)) => true,
                _ => false,
            }
        });
    }
}
