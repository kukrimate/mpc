/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use clap::*;
use mpc::*;
use std::path::Path;

fn main() {
  let args = clap::app_from_crate!()
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
    .arg(Arg::with_name("target")
      .long("target")
      .help("Target triplet")
      .takes_value(true))
    .get_matches();

  let compile_to = if args.occurrences_of("llvm-ir") > 0 {
    CompileTo::LLVMIr
  } else if args.occurrences_of("assembly") > 0 {
    CompileTo::Assembly
  } else {
    CompileTo::Object
  };

  let status = match compile(Path::new(args.value_of_os("input").unwrap()),
                             Path::new(args.value_of_os("output").unwrap()),
                             compile_to, args.value_of("target")) {
    Ok(()) => 0,
    Err(error) => {
      print!("{}", error);
      1
    }
  };

  std::process::exit(status);
}
