/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

#![feature(hash_set_entry)]
#![feature(hash_raw_entry)]

mod parse;
mod resolve;
mod sema;
mod lower;
pub mod util;

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
  pub line: usize,
  pub column: usize
}

impl std::fmt::Display for SourceLocation {
  fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    write!(fmt, "file {} line {} column {}", self.file.path.to_string_lossy(), self.line, self.column)
  }
}

/// Compiler errors (from anywhere)

#[derive(Debug)]
pub enum CompileError {
  IoError(std::path::PathBuf, std::io::Error),
  UnknownToken(SourceLocation),
  UnknownEscape(SourceLocation),
  UnterminatedStr(SourceLocation),
  UnterminatedChar(SourceLocation),
  UnterminatedComment(SourceLocation),
  InvalidChar(SourceLocation),
  UnexpectedToken(SourceLocation, parse::Token),
  UnknownModule(SourceLocation, RefStr),
  Redefinition(SourceLocation, RefStr),
  UnresolvedPath(SourceLocation, parse::Path),
  InvalidValueName(SourceLocation, parse::Path),
  InvalidTypeName(SourceLocation, parse::Path),
  InvalidUnionLiteral(SourceLocation),
  CannotUnifyBounds(SourceLocation, sema::Bound, sema::Bound),
  CannotUnifyTypes(SourceLocation, sema::Ty, sema::Ty),
  TypeDoesNotHaveBound(SourceLocation, sema::Ty, sema::Bound),
  IncorrectNumberOfTypeArguments(SourceLocation),
  TypeHasNoField(SourceLocation, sema::Ty, RefStr),
  CannotIndexType(SourceLocation, sema::Ty),
  CannotDereferenceType(SourceLocation, sema::Ty),
  CannotCallType(SourceLocation, sema::Ty),
  IncorrectNumberOfArguments(SourceLocation, sema::Ty),
  CannotMatchType(SourceLocation, sema::Ty),
  CannotAssignImmutable(SourceLocation),
  StructVariantExpectedArguments(SourceLocation),
  UnitVariantUnexpectedArguments(SourceLocation),
  InvalidLvalueExpression(SourceLocation),
  ContinueOutsideLoop(SourceLocation),
  BreakOutsideLoop(SourceLocation),
  ReturnOutsideFunction(SourceLocation),
  IncorrectArgumentLabel(SourceLocation, RefStr),
  DuplicateMatchCase(SourceLocation),
  MissingMatchCase(SourceLocation),
  IncorrectMatchCase(SourceLocation),
  InvalidConstantExpression(SourceLocation)
}

impl std::fmt::Display for CompileError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    match self {
      CompileError::IoError(path, error) => write!(f, "{}: {}", path.to_string_lossy(), error),
      CompileError::UnknownToken(location) => write!(f, "Error at {}: Unknown token", location),
      CompileError::UnknownEscape(location) => write!(f, "Error at {}: Unknown escape sequence", location),
      CompileError::UnterminatedStr(location) => write!(f, "Error at {}: Unterminated string literal", location),
      CompileError::UnterminatedChar(location) => write!(f, "Error at {}: Unterminated character literal", location),
      CompileError::UnterminatedComment(location) => write!(f, "Error at {}: Unterminated block comment", location),
      CompileError::InvalidChar(location) => write!(f, "Error at {}: Invalid char literal", location),
      CompileError::UnexpectedToken(location, token) => write!(f, "Error at {}: Unexpected token {:?}", location, token),
      CompileError::UnknownModule(location, name) => write!(f, "Error at {}: Unknown module {}", location, name),
      CompileError::Redefinition(location, name) => write!(f, "Error at {}: Re-definition of {}", location, name),
      CompileError::UnresolvedPath(location, path) => write!(f, "Error at {}: Unresolved path {}", location, path),
      CompileError::InvalidValueName(location, path) => write!(f, "Error at {}: {} does not refer to a value", location, path),
      CompileError::InvalidTypeName(location, path) => write!(f, "Error at {}: {} does not refer to a type", location, path),
      CompileError::InvalidUnionLiteral(location) => write!(f, "Error at {}: Union literal with more than one argument", location),
      CompileError::CannotUnifyBounds(location, b1, b2) => write!(f, "Error at {}: Incompatible type bounds {:?} and {:?}", location, b1, b2),
      CompileError::CannotUnifyTypes(location, ty1, ty2) => write!(f, "Error at {}: Cannot unify types {:?} and {:?}", location, ty1, ty2),
      CompileError::TypeDoesNotHaveBound(location, ty, bound) => write!(f, "Error at {}: Cannot bound type {:?} by {:?}", location, ty, bound),
      CompileError::IncorrectNumberOfTypeArguments(location) => write!(f, "Error at {}: Incorrect number of type arguments", location),
      CompileError::TypeHasNoField(location, ty, field)  => write!(f, "Error at {}: Type {:?} has no field named {}", location, ty, field),
      CompileError::CannotIndexType(location, ty)  => write!(f, "Error at {}: Type {:?} cannot be indexed", location, ty),
      CompileError::CannotDereferenceType(location, ty)  => write!(f, "Error at {}: Type {:?} cannot be dereferenced", location, ty),
      CompileError::CannotCallType(location, ty)  => write!(f, "Error at {}: Type {:?} cannot be called", location, ty),
      CompileError::IncorrectNumberOfArguments(location, ty) => write!(f, "Error at {}: Wrong number of arguments for {:?}", location, ty),
      CompileError::CannotMatchType(location, ty) => write!(f, "Error at {}: Cannot match on non-enum type {:?}", location, ty),
      CompileError::CannotAssignImmutable(location) => write!(f, "Error at {}: Cannot assign to immutable location", location),
      CompileError::StructVariantExpectedArguments(location ) => write!(f, "Error at {}: Missing arguments for struct variant", location),
      CompileError::UnitVariantUnexpectedArguments(location) => write!(f, "Error at {}: Junk arguments for unit variants", location),
      CompileError::InvalidLvalueExpression(location) => write!(f, "Error at {}: Invalid lvalue expression", location),
      CompileError::ContinueOutsideLoop(location) => write!(f, "Error at {}: Continue outside loop", location),
      CompileError::BreakOutsideLoop(location) => write!(f, "Error at {}: Break outside loop", location),
      CompileError::ReturnOutsideFunction(location) => write!(f, "Error at {}: Return outside function", location),
      CompileError::IncorrectArgumentLabel(location, label) => write!(f, "Error at {}: Incorrect argument label {}", location, label),
      CompileError::DuplicateMatchCase(location) => write!(f, "Error at {}: Duplicate match case", location),
      CompileError::MissingMatchCase(location) => write!(f, "Error at {}: Missing match case", location),
      CompileError::IncorrectMatchCase(location) => write!(f, "Error at {}: Incorrect match case", location),
      CompileError::InvalidConstantExpression(location) => write!(f, "Error at {}: Invalid constant expression", location),

    }
  }
}

impl std::error::Error for CompileError {}

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
