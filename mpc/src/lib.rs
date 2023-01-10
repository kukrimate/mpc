#![feature(hash_set_entry)]
#![feature(hash_raw_entry)]

mod parse;
mod sema;
pub mod util;

use crate::util::*;
use std::path::Path;

/// Choice of output artifact

pub enum CompileTo {
  LLVMIr,
  Assembly,
  Object
}

pub fn compile(input_path: &Path, output_path: &Path, compile_to: CompileTo) -> MRes<()> {
  let repo = parse::parse_bundle(input_path)?;
  sema::compile(&repo, output_path, compile_to)
}
