#![feature(coerce_unsized)]
#![feature(hash_set_entry)]
#![feature(unsize)]

mod parse;
mod sema;
mod util;

use crate::util::*;
use crate::sema::lower::CompileTo;
use clap::*;

fn compile(input_path: &str, output_path: &str, compile_to: CompileTo) -> MRes<()> {
  // Parse module
  let parsed_module = parse::parse_module(input_path)?;
  // Typecheck
  let mut checked_module = sema::check::check_module(&parsed_module)?;
  println!("{:#?}", checked_module);
  // Lower
  sema::lower::lower_module(&mut checked_module, output_path, compile_to)?;
  Ok(())
}

fn main() {
  util::init();

  let args = app_from_crate!()
    .arg(Arg::with_name("input")
      .help("Input file")
      .required(true)
      .index(1))
    .arg(Arg::with_name("assembly")
      .short("S")
      .help("Generate assembly"))
    .arg(Arg::with_name("llvm-ir")
      .short("L")
      .help("Generate LLVM IR"))
    .arg(Arg::with_name("output")
      .short("o")
      .long("output")
      .help("Output file")
      .required(true)
      .takes_value(true))
    .get_matches();

  let compile_to = if args.occurrences_of("llvm-ir") > 0 {
    CompileTo::LLVMIr
  } else if args.occurrences_of("assembly") > 0 {
    CompileTo::Assembly
  } else {
    CompileTo::Object
  };

  match compile(args.value_of("input").unwrap(),
                  args.value_of("output").unwrap(),
                  compile_to) {
    Ok(()) => eprintln!("ok :)"),
    Err(error) => eprintln!("{} :(", error),
  }

  util::uninit();
}
