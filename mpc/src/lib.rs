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

/// Source location

#[derive(Clone,Copy,Default,Debug)]
pub struct Location {
  pub line: usize,
  pub column: usize
}

impl std::fmt::Display for Location {
  fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    write!(fmt, "line {} column {}", self.line, self.column)
  }
}

/// Compiler errors (from anywhere)

#[derive(Debug)]
pub enum CompileError {
  IoError(std::path::PathBuf, std::io::Error),
  UnknownToken(Location),
  UnknownEscape(Location),
  UnterminatedStr(Location),
  UnterminatedChar(Location),
  UnterminatedComment(Location),
  InvalidChar(Location),
  UnexpectedToken(Location, parse::Token),
  UnknownModule(Location, RefStr),
  Redefinition(Location, RefStr),
  UnresolvedPath(parse::Path),
  InvalidValueName(parse::Path),
  InvalidTypeName(parse::Path),
  InvalidUnionLiteral,
  CannotUnifyBounds(sema::Bound, sema::Bound),
  CannotUnifyTypes(sema::Ty, sema::Ty),
  TypeDoesNotHaveBound(sema::Ty, sema::Bound),
  TypeError(String),
  IncorrectNumberOfTypeArguments,
  TypeHasNoField(sema::Ty, RefStr),
  CannotIndexType(sema::Ty),
  CannotDereferenceType(sema::Ty),
  CannotCallType(sema::Ty),
  IncorrectNumberOfArguments(sema::Ty),
  CannotMatchType(sema::Ty),
  CannotAssignImmutable,
  StructVariantExpectedArguments,
  UnitVariantUnexpectedArguments,
  InvalidLvalueExpression,
  ContinueOutsideLoop,
  BreakOutsideLoop,
  ReturnOutsideFunction,
  IncorrectArgumentLabel(RefStr),
  DuplicateMatchCase,
  MissingMatchCase,
  IncorrectMatchCase,
  InvalidConstantExpression
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
      CompileError::UnresolvedPath(path) => write!(f, "Unresolved path {}", path),
      CompileError::InvalidValueName(path) => write!(f, "{} does not refer to a value", path),
      CompileError::InvalidTypeName(path) => write!(f, "{} does not refer to a type", path),
      CompileError::InvalidUnionLiteral => write!(f, "Union literal with more than one argument"),
      CompileError::CannotUnifyBounds(b1, b2) => {
        write!(f, "Incompatible type bounds {:?} and {:?}", b1, b2)
      }
      CompileError::CannotUnifyTypes(ty1, ty2) => {
        write!(f, "Cannot unify types {:?} and {:?}", ty1, ty2)
      }
      CompileError::TypeDoesNotHaveBound(ty, bound) => {
        write!(f, "Cannot bound type {:?} by {:?}", ty, bound)
      }
      CompileError::TypeError(s) => {
        write!(f, "{}", s)
      }
      CompileError::IncorrectNumberOfTypeArguments => write!(f, "Incorrect number of type arguments"),
      CompileError::TypeHasNoField(ty, field)  => write!(f, "Type {:?} has no field named {}", ty, field),
      CompileError::CannotIndexType(ty)  => write!(f, "Type {:?} cannot be indexed", ty),
      CompileError::CannotDereferenceType(ty)  => write!(f, "Type {:?} cannot be dereferenced", ty),
      CompileError::CannotCallType(ty)  => write!(f, "Type {:?} cannot be called", ty),
      CompileError::IncorrectNumberOfArguments(ty) => write!(f, "Wrong number of arguments for {:?}", ty),
      CompileError::CannotMatchType(ty) => write!(f, "Cannot match on non-enum type {:?}", ty),
      CompileError::CannotAssignImmutable => write!(f, "Cannot assign to immutable location"),
      CompileError::StructVariantExpectedArguments => write!(f, "Missing arguments for struct variant"),
      CompileError::UnitVariantUnexpectedArguments => write!(f, "Junk arguments for unit variants"),
      CompileError::InvalidLvalueExpression => write!(f, "Invalid lvalue expression"),
      CompileError::ContinueOutsideLoop => write!(f, "Continue outside loop"),
      CompileError::BreakOutsideLoop => write!(f, "Break outside loop"),
      CompileError::ReturnOutsideFunction => write!(f, "Return outside function"),
      CompileError::IncorrectArgumentLabel(label) => write!(f, "Incorrect argument label {}", label),
      CompileError::DuplicateMatchCase => write!(f, "Duplicate match case"),
      CompileError::MissingMatchCase => write!(f, "Missing match case"),
      CompileError::IncorrectMatchCase => write!(f, "Incorrec match casefunction"),
      CompileError::InvalidConstantExpression => write!(f, "Invalid constant expression"),

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
