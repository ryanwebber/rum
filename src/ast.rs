use crate::types::Numeric;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Identifier(String),
    List(Vec<Expr>),
    Map(Vec<(Expr, Expr)>),
    Number(Numeric),
    PseudoValue(String),
    Quoted(Box<Expr>),
    String(String),
    Symbol(String),
    Vector(Vec<Expr>),
}
