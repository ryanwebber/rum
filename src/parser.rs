use core::fmt;
use std::fmt::Display;
use std::fmt::Formatter;

use crate::ast;
use crate::types;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub rum);

pub use rum::ExprParser;
pub use rum::ExprsParser;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SemanticError {
    NumberLiteralOverflow,
}

impl Display for SemanticError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        use self::SemanticError::*;
        match *self {
            NumberLiteralOverflow => write!(f, "Number literal overflow"),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_parse_expr() {
        assert!(rum::ExprParser::new().parse("22").is_ok());
        assert!(rum::ExprParser::new().parse("(22)").is_ok());
        assert!(rum::ExprParser::new().parse("((((22))))").is_ok());
        assert!(rum::ExprParser::new().parse("(2 2)").is_ok());
        assert!(rum::ExprParser::new().parse("(2)").is_ok());
        assert!(rum::ExprParser::new().parse("2 2").is_err());
        assert!(rum::ExprParser::new().parse("((22)").is_err());
        assert!(rum::ExprParser::new().parse("hello").is_ok());
        assert!(rum::ExprParser::new().parse("hello-world").is_ok());
        assert!(rum::ExprParser::new().parse("hello1").is_ok());
        assert!(rum::ExprParser::new().parse(":hello").is_ok());
        assert!(rum::ExprParser::new().parse(":hello-world").is_err());
        assert!(rum::ExprParser::new().parse("(hello1 2 3)").is_ok());
        assert!(rum::ExprParser::new().parse("2147483648").is_err());
        assert!(rum::ExprParser::new().parse(":2").is_ok());
        assert!(rum::ExprParser::new().parse(":__abc$xyz").is_ok());
        assert!(rum::ExprParser::new().parse(":id").is_ok());
        assert!(rum::ExprParser::new().parse(":").is_err());
        assert!(rum::ExprParser::new().parse("abc-123.xyz").is_ok());
        assert!(rum::ExprParser::new().parse("$abc").is_ok());
        assert!(rum::ExprParser::new().parse("abc$").is_err());
        assert!(rum::ExprParser::new().parse("-abc").is_err());
        assert!(rum::ExprParser::new().parse("\"\"").is_ok());
        assert!(rum::ExprParser::new().parse("\"Hello world!\"").is_ok());
        assert!(rum::ExprParser::new().parse("[]").is_ok());
        assert!(rum::ExprParser::new().parse("[").is_err());
        assert!(rum::ExprParser::new().parse("[1 2 () [()] [\"345\"]]").is_ok());
        assert!(rum::ExprParser::new().parse("{ () => () 9 => 0 {} => [] }").is_ok());
        assert!(rum::ExprParser::new().parse("_").is_ok());
        assert!(rum::ExprParser::new().parse("...").is_ok());
        assert!(rum::ExprParser::new().parse("`my/path`").is_ok());
        assert!(rum::ExprParser::new().parse("`path`").is_ok());
        assert!(rum::ExprParser::new().parse("`path/`").is_ok());
        assert!(rum::ExprParser::new().parse("`/`").is_err());
        assert!(rum::ExprParser::new().parse("`/hello`").is_err());
        assert!(rum::ExprParser::new().parse("``").is_ok());
        assert!(rum::ExprParser::new().parse("#True").is_ok());
        assert!(rum::ExprParser::new().parse("#Foo").is_ok());
        assert!(rum::ExprParser::new().parse("#foo").is_ok());
        assert!(rum::ExprParser::new().parse("#FooBar").is_ok());
        assert!(rum::ExprParser::new().parse("+").is_ok());
        assert!(rum::ExprParser::new().parse("'()").is_ok());
        assert!(rum::ExprParser::new().parse("(')").is_err());
    }

    #[test]
    fn test_parse_exprs() {
        assert!(rum::ExprsParser::new().parse(include_str!("samples/core.rum")).is_ok());
    }
}
