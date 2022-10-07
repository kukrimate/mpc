use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parse);

fn main() {
    assert!(parse::ModuleParser::new().parse("test").is_ok());
}
