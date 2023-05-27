use crate::types::Numeric;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr<'input> {
    Identifier(&'input str),
    List(Vec<Expr<'input>>),
    Map(Vec<(Expr<'input>, Expr<'input>)>),
    Number(Numeric),
    Path(Vec<&'input str>),
    Placeholder(MatchSize),
    PseudoValue(&'input str),
    String(&'input str),
    Symbol(&'input str),
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
