use crate::types::Numeric;

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

pub enum MatchSize {
    ZeroOrMore,
    One,
}
