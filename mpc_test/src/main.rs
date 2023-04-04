/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use std::ffi::OsStr;
use std::path::Path;
use std::process::{Command};
use regex::Regex;
use mpc::CompileError;

/// Directory of test programs
const PROG_DIR: &str = "mpc_test/prog";

/// Output directory
const OUTPUT_DIR: &str = "mpc_test/output";

fn main() {
  for cur in std::fs::read_dir(PROG_DIR).unwrap() {
    let src_path = cur.unwrap().path();
    let file_name = src_path.file_name().unwrap();
    let obj_path = Path::new(OUTPUT_DIR)
      .join(&file_name)
      .with_extension("o");
    let bin_path = Path::new(OUTPUT_DIR)
      .join(&file_name)
      .with_extension("");

    match mpc::compile(&src_path, &obj_path, mpc::CompileTo::Object, None)
      .map_err(|err| TestError::CompileFailure(err))
      .and_then(|_| link(&obj_path, &bin_path))
      .and_then(|_| run_and_check(&src_path, &bin_path))
    {
      Ok(_) => println!("[OK] {}", file_name.to_str().unwrap()),
      Err(err) => println!("[ERR] {} {}", file_name.to_str().unwrap(), err),
    }
  }
}


/// Error conditions
#[derive(Debug)]
enum TestError {
  CompileFailure(CompileError),
  LinkFailure,
  ExitFailure,
  IncorrectOutput
}

impl From<CompileError> for TestError {
  fn from(value: CompileError) -> Self {
    TestError::CompileFailure(value)
  }
}

impl std::fmt::Display for TestError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      TestError::CompileFailure(err) => write!(f, "{}", err),
      TestError::LinkFailure => write!(f, "Failed to link"),
      TestError::ExitFailure => write!(f, "Test exited with error"),
      TestError::IncorrectOutput => write!(f, "Incorrect test output"),
    }
  }
}

impl std::error::Error for TestError {}

/// Link an object file into an executable
fn link(obj_path: &Path, bin_path: &Path) -> Result<(), TestError> {
  let status = Command::new("cc")
    .args([OsStr::new("-o"), bin_path.as_os_str(), obj_path.as_os_str()])
    .status()
    .map_err(|err| TestError::CompileFailure(
       CompileError::IoError(bin_path.to_owned(), err)))?;

  match status.success() {
    true => Ok(()),
    false => Err(TestError::LinkFailure)
  }
}

/// Run and check program output
fn run_and_check(src_path: &Path, bin_path: &Path) -> Result<(), TestError> {
  // Parse source
  let source = std::fs::read_to_string(src_path).unwrap();
  let args = Regex::new(r"ARGS *(.*) *\n")
    .unwrap()
    .captures(&source)
    .and_then(|x| x.get(1))
    .and_then(|x| {
      Some(Regex::new(r" +").unwrap()
        .split(x.as_str())
        .collect())
    })
    .unwrap_or_else(Vec::new);
  let expected_stdout = Regex::new(r"(?s)STDOUT\n(.*)END", ).unwrap().captures(&source).and_then(|x| x.get(1));
  let expected_stderr = Regex::new(r"(?s)STDERR\n(.*)END", ).unwrap().captures(&source).and_then(|x| x.get(1));

  // Execute program
  let output = Command::new(bin_path)
    .args(args)
    .output()
    .map_err(|err| TestError::CompileFailure(
      CompileError::IoError(bin_path.to_owned(), err)))?;

  // Check status
  if !output.status.success() {
    Err(TestError::ExitFailure)?
  }

  // Check expected output
  match expected_stdout {
    Some(s) if output.stdout != s.as_str().as_bytes() => {
      Err(TestError::IncorrectOutput)?
    }
    _ => ()
  }
  match expected_stderr {
    Some(s) if output.stderr != s.as_str().as_bytes() => {
      Err(TestError::IncorrectOutput)?
    }
    _ => ()
  }

  Ok(())
}
