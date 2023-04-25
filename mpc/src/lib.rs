/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

#![feature(hash_set_entry)]
#![feature(hash_raw_entry)]
#![feature(map_try_insert)]

mod parse;
mod sema;
mod lower;
pub mod util;

use std::cmp::{max, min};
use crate::util::*;

/// Source file in memory
#[derive(Clone,Default,Debug)]
pub struct SourceFile {
  pub path: std::path::PathBuf,
  pub data: String
}

/// Location in a source file
#[derive(Clone,Default,Debug)]
pub struct SourceLocation {
  pub file: std::sync::Arc<SourceFile>,
  pub begin: usize,
  pub end: usize
}

/// Compiler errors

pub enum CompileError {
  IoError(std::path::PathBuf, std::io::Error),
  UnknownToken(SourceLocation),
  InvalidEscape(SourceLocation),
  UnterminatedStr(SourceLocation),
  UnterminatedChar(SourceLocation),
  UnterminatedBlockComment(SourceLocation),
  CharLiteralWithMoreThanOneCharacter(SourceLocation),
  UnexpectedToken(SourceLocation, parse::Token),
  UnknownModule(SourceLocation, RefStr),
  Redefinition(SourceLocation, RefStr),
  UnresolvedPath(SourceLocation, parse::Path),
  InvalidTypeName(SourceLocation, parse::Path),
  UnionLiteralWithMoreThanOneArgument(SourceLocation),
  CannotUnifyBounds(SourceLocation, sema::Bound, sema::Bound),
  CannotUnifyTypes(SourceLocation, sema::Ty, sema::Ty),
  TypeDoesNotHaveBound(SourceLocation, sema::Ty, sema::Bound),
  IncorrectNumberOfTypeArguments(SourceLocation),
  TypeHasNoField(SourceLocation, sema::Ty, RefStr),
  CannotIndexType(SourceLocation, sema::Ty),
  CannotDereferenceType(SourceLocation, sema::Ty),
  CannotCallType(SourceLocation, sema::Ty),
  IncorrectNumberOfArguments(SourceLocation),
  CannotMatchType(SourceLocation, sema::Ty),
  CannotAssignImmutable(SourceLocation),
  InvalidLvalueExpression(SourceLocation),
  InvalidRValueExpression(SourceLocation, parse::Path),
  ContinueOutsideLoop(SourceLocation),
  BreakOutsideLoop(SourceLocation),
  ReturnOutsideFunction(SourceLocation),
  IncorrectArgumentLabel(SourceLocation, RefStr),
  MissingMatchCase(SourceLocation),
  IncorrectMatchCase(SourceLocation),
  InvalidMethodReceiver(SourceLocation),
  MissingMethodReceiver(SourceLocation),
  InvalidConstantExpression(SourceLocation)
}

impl CompileError {
  pub fn display(&self) {
    match self {
      CompileError::IoError(path, error) => println!("{}: {}", path.to_string_lossy(), error),
      CompileError::UnknownToken(location) => display_err(location, || println!("error: unknown token")),
      CompileError::InvalidEscape(location) => display_err(location, || println!("error: unknown escape sequence")),
      CompileError::UnterminatedStr(location) => display_err(location, || println!("error: unterminated string literal")),
      CompileError::UnterminatedChar(location) => display_err(location, || println!("error: unterminated character literal")),
      CompileError::UnterminatedBlockComment(location) => display_err(location, || println!("error: unterminated block comment")),
      CompileError::CharLiteralWithMoreThanOneCharacter(location) => display_err(location, || println!("error: character literal with more than one character")),
      CompileError::UnexpectedToken(location, token) => display_err(location, || println!("error: unexpected token {:?}", token)),
      CompileError::UnknownModule(location, name) => display_err(location, || println!("error: unknown module {}", name)),
      CompileError::Redefinition(location, name) => display_err(location, || println!("error: re-definition of {}", name)),
      CompileError::UnresolvedPath(location, path) => display_err(location, || println!("error: unresolved path {}", path)),
      CompileError::InvalidTypeName(location, path) => display_err(location, || println!("error: invalid typename {}", path)),
      CompileError::UnionLiteralWithMoreThanOneArgument(location) => display_err(location, || println!("error: union literal with more than one argument")),
      CompileError::CannotUnifyBounds(location, b1, b2) => display_err(location, || println!("error: incompatible type bounds {:?} and {:?}", b1, b2)),
      CompileError::CannotUnifyTypes(location, ty1, ty2) => display_err(location, || println!("error: cannot unify types {:?} and {:?}", ty1, ty2)),
      CompileError::TypeDoesNotHaveBound(location, ty, bound) => display_err(location, || println!("error: cannot bound type {:?} by {:?}", ty, bound)),
      CompileError::IncorrectNumberOfTypeArguments(location) => display_err(location, || println!("error: incorrect number of type arguments")),
      CompileError::TypeHasNoField(location, ty, field)  => display_err(location, || println!("error: type {:?} has no field named {}", ty, field)),
      CompileError::CannotIndexType(location, ty) => display_err(location, || println!("error: type {:?} cannot be indexed", ty)),
      CompileError::CannotDereferenceType(location, ty) => display_err(location, || println!("error: type {:?} cannot be de-referenced", ty)),
      CompileError::CannotCallType(location, ty)  => display_err(location, || println!("error: type {:?} cannot be called", ty)),
      CompileError::IncorrectNumberOfArguments(location) => display_err(location, || println!("error: incorrect number of arguments")),
      CompileError::CannotMatchType(location, ty) => display_err(location, || println!("error: cannot match on non-enum type {:?}", ty)),
      CompileError::CannotAssignImmutable(location) => display_err(location, || println!("error: cannot assign to immutable location")),
      CompileError::InvalidLvalueExpression(location) => display_err(location, || println!("error: invalid lvalue expression")),
      CompileError::InvalidRValueExpression(location, path) => display_err(location, || println!("error: invalid rvalue {}", path)),
      CompileError::ContinueOutsideLoop(location) => display_err(location, || println!("error: continue outside loop")),
      CompileError::BreakOutsideLoop(location) => display_err(location, || println!("error: break outside loop")),
      CompileError::ReturnOutsideFunction(location) => display_err(location, || println!("error: return outside function")),
      CompileError::IncorrectArgumentLabel(location, label) => display_err(location, || println!("error: incorrect argument label {}", label)),
      CompileError::MissingMatchCase(location) => display_err(location, || println!("error: missing match case")),
      CompileError::IncorrectMatchCase(location) => display_err(location, || println!("error: incorrect match case")),
      CompileError::InvalidMethodReceiver(location) => display_err(location, || println!("error: invalid method receiver")),
      CompileError::MissingMethodReceiver(location) => display_err(location, || println!("error: missing method receiver")),
      CompileError::InvalidConstantExpression(location) => display_err(location, || println!("error: invalid constant expression")),
    }
  }
}

/// Convert a position to a line and column number
fn position_to_line_column(input: &str, pos: usize) -> (usize, usize) {
  let mut line = 1;
  let mut col = 1;
  for index in 0..pos {
    if &input[index..index+1] == "\n" {
      line += 1;
      col = 1;
    } else {
      col += 1;
    }
  }
  (line, col)
}

/// Display an error condition
fn display_err<F>(location: &SourceLocation, with: F)
  where F: FnOnce()
{
  // Compute line and column numbers
  let (line, col) = position_to_line_column(&location.file.data, location.begin);

  // Split surrounding context into lines
  let lines = split_lines(&location.file.data,
                          scan_backward_nl(&location.file.data, location.begin),
                          scan_forward_nl(&location.file.data, location.end));

  // Width to pad line numbers to
  let max_line_num_width = (line + lines.len() - 1).to_string().len();

  // Print error condition
  with();

  // Print location heading
  println!("{}--> {}:{}:{}\n{} |",
           " ".repeat(max_line_num_width),
           location.file.path.to_string_lossy(),
           line,
           col,
           " ".repeat(max_line_num_width));

  // Print lines
  for (line_index, (line_start, line_text)) in lines.iter().enumerate() {
    // Print line number + line text
    println!("{} | {}", line + line_index, line_text);
    // Highlight offending text
    if *line_start < location.end {
      let pad = max(location.begin, *line_start) - *line_start;
      let cnt = min(location.end - *line_start, line_text.len()) - pad;
      println!("{} | {}{}",
               " ".repeat(max_line_num_width),
               " ".repeat(pad),
               "^".repeat(cnt));
    }
  }
}

/// Scan backward for a newline
fn scan_backward_nl(input: &str, mut pos: usize) -> usize {
  while pos > 0 && &input[pos - 1..pos] != "\n" {
    pos -= 1;
  }
  pos
}

/// Scan forward for a newline
fn scan_forward_nl(input: &str, mut pos: usize) -> usize {
  while pos < input.len() && &input[pos..pos+1] != "\n" {
    pos += 1;
  }
  pos
}

/// Collect a list of lines contained in an input span
fn split_lines(input: &str, mut pos: usize, end: usize) -> Vec<(usize, &str)> {
  let mut lines = Vec::new();
  while {
    let begin = pos;
    while pos < end && &input[pos..pos + 1] != "\n" {
      pos += 1;
    }
    if begin < pos {
      lines.push((begin, &input[begin..pos]));
    }
    pos < end
  } {
    pos += 1
  }
  lines
}

/// Choice of output artifact

pub enum CompileTo {
  LLVMIr,
  Assembly,
  Object
}

/// Top level API

pub fn compile(input_path: &std::path::Path, output_path: &std::path::Path, compile_to: CompileTo, triple: Option<&str>) -> Result<(), CompileError> {
  let parsed_repo = parse::parse_bundle(input_path)?;
  let mut inst_collection = sema::analyze(&parsed_repo)?;
  lower::compile(&mut inst_collection, output_path, compile_to, triple)
}
