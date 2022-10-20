#![feature(hash_set_entry)]

mod check;
mod gen;
mod parse;

#[allow(dead_code)]
mod util;

use clap::{Arg,App};
use check::*;
use gen::*;
use parse::*;
use util::*;

fn compile(path: &str) -> MRes<()> {
  let module = parse_module(path)?;
  check_module(&module)
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
