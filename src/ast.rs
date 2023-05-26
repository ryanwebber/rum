use crate::types::Numeric;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr<'input> {
    Identifier(&'input str),
    Number(Numeric),
    List(Vec<Expr<'input>>),
    Map(Vec<(Expr<'input>, Expr<'input>)>),
    Path(Vec<&'input str>),
    Placeholder(MatchSize),
    String(&'input str),
    Symbol(&'input str),
    Value(&'input str),
    Vector(Vec<Expr<'input>>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MatchSize {
    ZeroOrMore,
    One,
}

pub mod builtin {
    use super::*;

    pub fn quote<'input>(expr: Expr<'input>) -> Expr<'input> {
        Expr::List(vec![Expr::Identifier("quote"), expr])
    }
}
