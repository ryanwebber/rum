#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(pub rum);

#[test]
fn calculator1() {
    assert!(rum::TermParser::new().parse("22").is_ok());
    assert!(rum::TermParser::new().parse("(22)").is_ok());
    assert!(rum::TermParser::new().parse("((((22))))").is_ok());
    assert!(rum::TermParser::new().parse("((22)").is_err());
}
