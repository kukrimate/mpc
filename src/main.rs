#![feature(hash_set_entry)]
#![feature(hash_raw_entry)]

mod check;
mod parse;

#[allow(dead_code)]
mod util;

use clap::{Arg,App};
use check::*;
use parse::*;
use util::*;

fn compile(path: &str) -> MRes<()> {
  // Parse module
  let module = parse_module(path)?;

  // Typecheck
  let mut check_ctx = CheckCtx::new();
  check_ctx.check_module(&module)

  // let mut gen_ctx = GenCtx::new(RefStr::new(module_id));
  // gen_ctx.dump();
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
