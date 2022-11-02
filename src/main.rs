#![feature(hash_set_entry)]

mod parse;
mod sema;
mod util;

use crate::util::*;
use clap::{Arg,App};

fn compile(path: &str) -> MRes<()> {
  // Parse module
  let parsed_module = parse::parse_module(path)?;

  // Typecheck
  let checked_module = sema::check::check_module(&parsed_module)?;

  println!("{:#?}", checked_module.defs);

  Ok(())
}

fn main() {
  util::init();

  let args = App::new("bootstrap")
    .version("0.1.0")
    .author("Mate Kukri <km@mkukri.xyz>")
    .about("Boostrap compiler")
    .arg(Arg::with_name("INPUT")
      .help("Input file")
      .required(true)
      .index(1))
    .get_matches();

  match compile(args.value_of("INPUT").unwrap()) {
    Ok(()) => println!("ok :)"),
    Err(error) => println!("{} :(", error),
  }
}
