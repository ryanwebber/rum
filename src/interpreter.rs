use core::{fmt, hash::Hash};
use std::{
    collections::HashMap,
    fmt::{Display, Formatter},
};

use crate::{ast::Expr, gc::Gc, interner, modules, parser, types::*};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ErrorType {
    InconsistentState,
    InvalidBridgeCall,
    InvalidParse,
    UnboundIdentifier,
    UnknownNativeCall,
    UnknownPseudoValue,
    ValueNotCallable,
}

type StringInterner = interner::StringInterner<Id>;

#[derive(Debug)]
pub struct Error {
    error_type: ErrorType,
    message: String,
}

impl Error {
    pub fn invalid_bridge_call(call: &str, msg: &str) -> Error {
        Error {
            error_type: ErrorType::InvalidBridgeCall,
            message: format!("Invalid bridge call: {} ({})", call, msg),
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
                ErrorType::InvalidBridgeCall => "InvalidBridgeCall",
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Bridge,
    Expr(Expr),
    List(Vec<Value>),
    String(String),
    Symbol(Symbol),
    Table(Gc<Table>),
    Vector(Vec<Value>),
}

impl Value {
    pub fn empty() -> Self {
        Value::List(vec![])
    }

    pub fn display<'a>(&'a self, state: &'a State) -> PrintableValue<'a> {
        PrintableValue(state, self)
    }
}

pub struct PrintableValue<'a>(pub &'a State, pub &'a Value);

impl<'a> Display for PrintableValue<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.1 {
            Value::Bridge => write!(f, "<bridge>"),
            Value::Expr(expr) => write!(f, "{:?}", expr),
            Value::List(items) => {
                write!(f, "'(")?;
                for item in items {
                    write!(f, "{} ", PrintableValue(self.0, item))?;
                }
                write!(f, ")")
            }
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Symbol(sym) => match self.0.strings.resolve(sym.0) {
                None => write!(f, "<???>"),
                Some(name) => write!(f, "{}", name),
            },
            Value::Table(table) => {
                write!(f, "{{")?;
                for (key, value) in table.borrow().0.iter() {
                    write!(
                        f,
                        "{}: {}, ",
                        PrintableValue(self.0, &key),
                        PrintableValue(self.0, &value)
                    )?;
                }
                write!(f, "}}")
            }
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Symbol(pub Id);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Table(HashMap<Value, Value>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NativeFunction {
    pub sym: Symbol,
}

impl NativeFunction {
    fn call(&self, interpreter: &Interpreter, state: &mut State, args: &[Value]) -> Result<Value, Error> {
        interpreter.backend.try_native_call(interpreter, state, self.sym, args)
    }
}

pub struct State {
    strings: StringInterner,
    metatable: Gc<Table>,
}

impl State {
    pub fn new() -> Self {
        Self {
            strings: StringInterner::new(),
            metatable: Gc::new(Table(HashMap::new())),
        }
    }
}

pub type NativeFunctionImpl = fn(&Interpreter, &mut State, &[Value]) -> Result<Value, Error>;

pub struct Backend {
    builtins: HashMap<&'static str, NativeFunctionImpl>,
}

impl Backend {
    fn new() -> Self {
        Backend {
            builtins: HashMap::new(),
        }
    }

    pub fn register(&mut self, name: &'static str, implementation: NativeFunctionImpl) {
        self.builtins.insert(name, implementation);
    }

    fn try_native_call(
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
                Some(implementation) => implementation(interpreter, state, args),
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

    pub fn evaluate(&self, state: &mut State, expr: Expr) -> Result<Value, Error> {
        match expr {
            Expr::List(exprs) => {
                let values = exprs
                    .into_iter()
                    .map(|expr| self.evaluate(state, expr))
                    .collect::<Result<Vec<_>, _>>()?;

                match values.split_first() {
                    None => Ok(Value::empty()),
                    Some((first, args)) => self.try_call(state, first, args),
                }
            }
            Expr::PseudoValue(name) => match &name[..] {
                "bridge" => Ok(Value::Bridge),
                "meta" => Ok(Value::Table(state.metatable.clone())),
                _ => Err(Error::unknown_pseudo_value(&name)),
            },
            Expr::Quoted(expr) => Ok(Value::Expr(*expr)),
            Expr::String(s) => Ok(Value::String(s)),
            Expr::Symbol(sym) => {
                let sym = state.strings.get_or_intern(sym);
                Ok(Value::Symbol(Symbol(sym)))
            }
            Expr::Vector(exprs) => {
                let values = exprs
                    .into_iter()
                    .map(|expr| self.evaluate(state, expr))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(Value::Vector(values))
            }
            _ => todo!("Convert {:?} to Value", expr),
        }
    }

    pub fn try_call(&self, state: &mut State, callee: &Value, args: &[Value]) -> Result<Value, Error> {
        match callee {
            Value::Bridge => match args {
                [Value::Symbol(sym), args @ ..] => self.backend.try_native_call(self, state, *sym, args),
                _ => Err(Error::invalid_bridge_call(
                    "bridge",
                    &format!(
                        "Expected (<SYMBOL> ...), got: {}",
                        Value::List(args.to_vec()).display(state)
                    ),
                )),
            },
            Value::Table(_) => {
                //
                todo!("Call table")
            }
            _ => Err(Error::value_not_callable(callee.display(state))),
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

        runtime
    }

    pub fn load_module<T: Module>(&mut self, module: &T) -> Result<(), Error> {
        module.register_builtins(&mut self.interpreter.backend);
        self.parse_and_evaluate_exprs(T::prelude()).map(|_| ())
    }

    pub fn parse_and_evaluate_expr(&mut self, input: &str) -> Result<Value, Error> {
        self.parsers
            .expr
            .parse(input)
            .map_err(|err| Error::invalid_parse(&err))
            .and_then(|expr| self.interpreter.evaluate(&mut self.state, expr))
    }

    pub fn parse_and_evaluate_exprs(&mut self, input: &str) -> Result<Option<Value>, Error> {
        self.parsers
            .exprs
            .parse(input)
            .map_err(|err| Error::invalid_parse(&err))
            .and_then(|exprs| {
                exprs
                    .into_iter()
                    .map(|expr| self.interpreter.evaluate(&mut self.state, expr))
                    .collect::<Result<Vec<_>, _>>()
                    .map(|values| values.last().cloned())
            })
    }

    pub fn evaluate_expr(&mut self, expr: Expr) -> Result<Value, Error> {
        self.interpreter.evaluate(&mut self.state, expr)
    }

    pub fn evaluate_exprs(&mut self, exprs: Vec<Expr>) -> Result<Vec<Value>, Error> {
        exprs.into_iter().map(|expr| self.evaluate_expr(expr)).collect()
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
    fn test_evaluate_primitives() {
        let mut runtime = Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr("\"abc\""),
            Ok(Value::String(String::from("abc")))
        );
    }

    /*
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
        assert_eq!(runtime.evaluate_expr("#Bridge"), Ok(Value::Bridge));
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
    */
}
