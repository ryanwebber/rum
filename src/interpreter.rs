use core::{fmt, hash::Hash};
use std::{
    collections::{hash_map::Entry, HashMap},
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
    UnsupportedOperation,
    ValueNotCallable,
}

pub type StringInterner = interner::StringInterner<Id>;

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

    pub fn unsupported_operation(desciption: &str) -> Error {
        Error {
            error_type: ErrorType::UnsupportedOperation,
            message: format!("Unsupported operation: {}", desciption),
        }
    }

    pub fn value_not_callable(value: PrintableValue<'_>) -> Error {
        Error {
            error_type: ErrorType::ValueNotCallable,
            message: format!("Value is not callable: {}", value),
        }
    }

    pub fn table_not_callable() -> Error {
        Error {
            error_type: ErrorType::ValueNotCallable,
            message: format!("Table has no callable body defined"),
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
                ErrorType::UnsupportedOperation => "UnsupportedOperation",
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
    List(Vec<Expr>),
    Number(Numeric),
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

    pub fn typename(&self) -> &'static str {
        match self {
            Value::Bridge => "bridge",
            Value::Expr(_) => "expr",
            Value::List(_) => "list",
            Value::Number(_) => "number",
            Value::String(_) => "string",
            Value::Symbol(_) => "symbol",
            Value::Table(_) => "table",
            Value::Vector(_) => "vector",
        }
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
                    write!(f, "{} ", Value::Expr(item.clone()).display(self.0))?;
                }
                write!(f, ")")
            }
            Value::Number(n) => write!(f, "{}", n),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Symbol(sym) => match sym {
                Symbol::Static(name) => write!(f, "{}", name.0),
                Symbol::Shared(id) => match self.0.strings.resolve(*id) {
                    None => write!(f, "<???>"),
                    Some(name) => write!(f, "{}", name),
                },
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
pub enum Symbol {
    Shared(usize),
    Static(StaticSymbol),
}

impl Symbol {
    pub fn resolve(s: &str, state: &mut State) -> Self {
        if let Some(inner) = StaticSymbol::as_static_symbol(s) {
            return Symbol::Static(inner);
        } else {
            Symbol::Shared(state.strings.get_or_intern(s))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub struct StaticSymbol(&'static str);

impl StaticSymbol {
    pub const FN_BODY: StaticSymbol = StaticSymbol("fn.body");
    pub const FN_NAME: StaticSymbol = StaticSymbol("fn.name");
    pub const FN_PARAMETERS: StaticSymbol = StaticSymbol("fn.parameters");
    pub const FN_TYPE: StaticSymbol = StaticSymbol("fn.type");
    pub const LOCALS: StaticSymbol = StaticSymbol("locals");
    pub const MACRO: StaticSymbol = StaticSymbol("macro");

    const ALL: &'static [StaticSymbol] = &[
        StaticSymbol::FN_BODY,
        StaticSymbol::FN_NAME,
        StaticSymbol::FN_PARAMETERS,
        StaticSymbol::FN_TYPE,
        StaticSymbol::LOCALS,
        StaticSymbol::MACRO,
    ];

    fn as_static_symbol(sym: &str) -> Option<Self> {
        Self::ALL.iter().find(|ss| ss.0 == sym).copied()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Table(HashMap<Value, Value>);

impl Table {
    pub fn new() -> Self {
        Table(HashMap::new())
    }

    pub fn entry(&mut self, key: Value) -> Entry<Value, Value> {
        self.0.entry(key)
    }

    pub fn insert(&mut self, key: Value, value: Value) {
        self.0.insert(key, value);
    }

    pub fn get(&self, key: &Value) -> Option<&Value> {
        self.0.get(key)
    }

    pub fn remove(&mut self, key: &Value) -> Option<Value> {
        self.0.remove(key)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Value, &Value)> {
        self.0.iter()
    }
}

pub struct Scope {
    metatable: Gc<Table>,
}

impl Scope {
    fn new() -> Self {
        Scope {
            metatable: Gc::new(Table(HashMap::new())),
        }
    }

    pub fn set_local(&mut self, identifier: Symbol, value: Value) {
        let mut locals = self.metatable.borrow_mut();
        let locals = locals
            .0
            .entry(Value::Symbol(Symbol::Static(StaticSymbol::LOCALS)))
            .or_insert_with(|| Value::Table(Gc::new(Table(HashMap::new()))));

        let Value::Table(locals) = locals else {
            return;
        };

        locals.borrow_mut().0.insert(Value::Symbol(identifier), value);
    }

    pub fn get_local(&self, identifier: &Symbol) -> Option<Value> {
        let locals = self.metatable.borrow();
        let locals = locals.0.get(&Value::Symbol(Symbol::Static(StaticSymbol::LOCALS)))?;
        let Value::Table(locals) = locals else {
            return None;
        };

        let locals = locals.borrow();
        let Some(value) = locals.0.get(&Value::Symbol(*identifier)) else {
            return None;
        };

        Some(value.clone())
    }
}

pub struct State {
    strings: StringInterner,
    callstack: Vec<Scope>,
}

impl State {
    pub fn new() -> Self {
        Self {
            strings: StringInterner::new(),
            callstack: vec![Scope::new()],
        }
    }

    pub fn get_string<'a>(&'a self, symbol: &Symbol) -> Option<&'a str> {
        self.strings.resolve(match symbol {
            Symbol::Shared(id) => *id,
            Symbol::Static(name) => return Some(name.0),
        })
    }

    pub fn current_scope(&self) -> &Scope {
        self.callstack.last().unwrap()
    }

    pub fn current_scope_mut(&mut self) -> &mut Scope {
        self.callstack.last_mut().unwrap()
    }

    pub fn global_scope(&self) -> &Scope {
        self.callstack.first().unwrap()
    }

    pub fn global_scope_mut(&mut self) -> &mut Scope {
        self.callstack.first_mut().unwrap()
    }

    pub fn resolve(&self, id: Symbol) -> Option<Value> {
        for scope in self.callstack.iter().rev() {
            if let Some(value) = scope.get_local(&id) {
                return Some(value.clone());
            }
        }

        None
    }

    pub fn create_empty(&mut self) -> Value {
        Value::List(vec![])
    }

    pub fn create_table(&mut self, table: impl Into<Table>) -> Value {
        Value::Table(Gc::new(table.into()))
    }

    pub fn create_vector(&mut self, items: impl Into<Vec<Value>>) -> Value {
        Value::Vector(items.into())
    }

    pub fn create_string(&mut self, s: impl Into<String>) -> Value {
        Value::String(s.into())
    }

    pub fn create_symbol(&mut self, name: impl AsRef<str>) -> Value {
        Value::Symbol(Symbol::resolve(name.as_ref(), self))
    }

    pub fn create_list(&mut self, items: impl Into<Vec<Expr>>) -> Value {
        Value::List(items.into())
    }

    pub fn create_expr(&mut self, expr: impl Into<Expr>) -> Value {
        Value::Expr(expr.into())
    }

    pub fn with_new_stack_frame(
        &mut self,
        args: impl Iterator<Item = (Symbol, Value)>,
        f: impl FnOnce(&mut Self) -> Result<Value, Error>,
    ) -> Result<Value, Error> {
        let mut scope = Scope::new();
        for (id, value) in args {
            scope.set_local(id, value);
        }

        self.callstack.push(scope);
        let result = f(self);
        self.callstack.pop();
        result
    }
}

pub struct Interpreter {
    backend: Backend,
}

impl Interpreter {
    fn new() -> Self {
        Interpreter {
            backend: Backend::new(),
        }
    }

    pub fn evaluate(&self, state: &mut State, expr: Expr) -> Result<Value, Error> {
        match expr {
            Expr::Identifier(id) => {
                let sym = Symbol::resolve(&id, state);
                state.resolve(sym).ok_or_else(|| Error::unbound_identifier(&id))
            }
            Expr::List(exprs) => match exprs.split_first() {
                None => Ok(state.create_empty()),
                Some((first, args)) => {
                    let callee = self.evaluate(state, first.clone())?;
                    self.try_call(state, &callee, args)
                }
            },
            Expr::Number(n) => Ok(Value::Number(n)),
            Expr::PseudoValue(name) => match &name[..] {
                "bridge" => Ok(Value::Bridge),
                "global" => Ok(Value::Table(state.global_scope().metatable.clone())),
                "meta" => Ok(Value::Table(state.current_scope().metatable.clone())),
                _ => Err(Error::unknown_pseudo_value(&name)),
            },
            Expr::Quoted(expr) => Ok(Value::Expr(*expr)),
            Expr::String(s) => Ok(Value::String(s)),
            Expr::Symbol(sym) => Ok(Value::Symbol(Symbol::resolve(&sym, state))),
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

    pub fn try_call(&self, state: &mut State, callee: &Value, args: &[Expr]) -> Result<Value, Error> {
        match callee {
            Value::Bridge => match args {
                [Expr::Symbol(sym), args @ ..] => {
                    let sym = Symbol::resolve(&sym, state);
                    self.backend.try_native_call(self, state, sym, args)
                }
                _ => Err(Error::invalid_bridge_call(
                    "bridge",
                    &format!(
                        "Expected (<SYMBOL> ...), got: {}",
                        Value::List(args.to_vec()).display(state)
                    ),
                )),
            },
            Value::Table(table) => {
                let table = &mut table.borrow_mut().0;
                let Some(Value::Expr(body)) = table.get(&Value::Symbol(Symbol::Static(StaticSymbol::FN_BODY))) else {
                    return Err(Error::table_not_callable());
                };

                let is_macro = match table.get(&Value::Symbol(Symbol::Static(StaticSymbol::FN_TYPE))) {
                    Some(Value::Symbol(sym)) => *sym == Symbol::Static(StaticSymbol::MACRO),
                    _ => false,
                };

                let parameters: Vec<(Symbol, Value)> = {
                    let parameter_names = match table.get(&Value::Symbol(Symbol::Static(StaticSymbol::FN_PARAMETERS))) {
                        Some(Value::Expr(Expr::List(parameters))) => parameters.clone(),
                        _ => vec![],
                    };

                    std::iter::zip(parameter_names.iter(), args.iter())
                        .map(|(name, expr)| {
                            let Expr::Identifier(name) = name else {
                                return Err(Error::table_not_callable());
                            };

                            let value = if is_macro {
                                state.create_expr(expr.clone())
                            } else {
                                self.evaluate(state, expr.clone())?
                            };

                            Ok((Symbol::resolve(&name, state), value))
                        })
                        .collect::<Result<_, _>>()?
                };

                state.with_new_stack_frame(parameters.into_iter(), |state| {
                    // Evaluate the body of the function with the new stack frame
                    self.evaluate(state, body.clone())
                })
            }
            _ => Err(Error::value_not_callable(callee.display(state))),
        }
    }
}

pub enum NativeCall {
    Macro(NativeMacroImpl),
    Function(NativeFunctionImpl),
}

pub type NativeMacroImpl = fn(&Interpreter, &mut State, &[Expr]) -> Result<Value, Error>;
pub type NativeFunctionImpl = fn(&Interpreter, &mut State, &[Value]) -> Result<Value, Error>;

pub struct Backend {
    builtins: HashMap<&'static str, NativeCall>,
}

impl Backend {
    fn new() -> Self {
        Backend {
            builtins: HashMap::new(),
        }
    }

    pub fn register(&mut self, name: &'static str, implementation: NativeCall) {
        self.builtins.insert(name, implementation);
    }

    fn try_native_call(
        &self,
        interpreter: &Interpreter,
        state: &mut State,
        sym: Symbol,
        args: &[Expr],
    ) -> Result<Value, Error> {
        match sym {
            Symbol::Static(name) => Err(Error::invalid_bridge_call(name.0, "Static symbols are not callable")),
            Symbol::Shared(id) => match state.strings.resolve(id) {
                None => Err(Error::no_such_string()),
                Some(name) => match self.builtins.get(&name[1..]) {
                    None => Err(Error::unknown_native_call(name)),
                    Some(NativeCall::Macro(implementation)) => implementation(interpreter, state, &args),
                    Some(NativeCall::Function(implementation)) => {
                        let args = args
                            .iter()
                            .map(|expr| interpreter.evaluate(state, expr.clone()))
                            .collect::<Result<Vec<_>, _>>()?;

                        state.with_new_stack_frame(std::iter::empty(), |state| {
                            // Note: native fns don't have named parameters
                            implementation(interpreter, state, &args)
                        })
                    }
                },
            },
        }
    }
}

pub trait Module
where
    Self: Sized,
{
    fn prelude() -> &'static str;
    fn register_builtins(&self, backend: &mut Backend);
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
        runtime.load_module(&modules::collections::Collections).unwrap();
        runtime.load_module(&modules::reflection::Reflection).unwrap();

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

    #[test]
    fn test_evaluate_primitives() {
        let mut runtime = Runtime::new();
        assert_eq!(
            runtime.parse_and_evaluate_expr("\"abc\""),
            Ok(Value::String(String::from("abc")))
        );
    }

    #[test]
    fn test_simple_function() {
        let mut runtime = Runtime::new();
        let result = runtime.parse_and_evaluate_exprs(indoc::indoc! {"
            (def-fn! twice (x) [x x])
            (twice 2)
        "});

        assert_eq!(
            result,
            Ok(Some(Value::Vector(vec![Value::Number(2), Value::Number(2)])))
        );
    }
}
