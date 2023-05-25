mod ast;
mod interpreter;
mod parser;
mod types;

extern crate lalrpop_util;

fn main() {
    _ = parser::ExprParser::new().parse("((((22))))");
}
