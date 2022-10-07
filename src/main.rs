mod ast;

use clap::{Arg,App};
use std::fs;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parse);

fn main() {
  let args = App::new("bootstrap")
    .version("0.1.0")
    .author("Mate Kukri <km@mkukri.xyz>")
    .about("Boostrap compiler")
    .arg(Arg::with_name("INPUT")
      .help("Input file")
      .required(true)
      .index(1))
    .get_matches();

  let input = fs::read_to_string(args.value_of("INPUT").unwrap()).unwrap();
  println!("{:?}", parse::ModuleParser::new().parse(&input));
}
