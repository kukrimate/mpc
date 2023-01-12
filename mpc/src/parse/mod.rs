/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use crate::util::RefStr;
use lexer::Token;
use lalrpop_util::{self,lalrpop_mod};
use std::collections::HashMap;
use std::{error, fs, fmt, io};
use std::path::PathBuf;

mod lexer;

lalrpop_mod!(maple, "/parse/maple.rs");

/// Syntax tree produced by the parser

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IsMut { Yes, No }

impl fmt::Display for IsMut {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      IsMut::Yes => write!(f, "mut "),
      IsMut::No => write!(f, ""),
    }
  }
}

pub type Path = Vec<RefStr>;

#[derive(Debug)]
pub enum Ty {
  Bool,
  Uint8,
  Int8,
  Uint16,
  Int16,
  Uint32,
  Int32,
  Uint64,
  Int64,
  Uintn,
  Intn,
  Float,
  Double,
  Inst(Path, Vec<Ty>),
  Ptr(IsMut, Box<Ty>),
  Func(Vec<(RefStr, Ty)>, Box<Ty>),
  Arr(Box<Expr>, Box<Ty>),
  Tuple(Vec<(RefStr, Ty)>),
}

#[derive(Clone,Copy,Debug)]
pub enum UnOp {
  UPlus, UMinus, Not
}

#[derive(Clone,Copy,Debug)]
pub enum BinOp {
  Mul, Div, Mod, Add, Sub, Lsh, Rsh, And, Xor, Or, Eq, Ne, Lt, Gt, Le, Ge
}

#[derive(Debug)]
pub enum Expr {
  Empty,
  Path(Path),
  Nil,
  Bool(bool),
  Int(usize),
  Flt(f64),
  Str(Vec<u8>),
  CStr(Vec<u8>),
  Arr(Vec<Expr>),
  Dot(Box<Expr>, RefStr),
  Call(Box<Expr>, Vec<(RefStr, Expr)>),
  Index(Box<Expr>, Box<Expr>),
  Adr(Box<Expr>),
  Ind(Box<Expr>),
  Un(UnOp, Box<Expr>),
  LNot(Box<Expr>),
  Cast(Box<Expr>, Ty),
  Bin(BinOp, Box<Expr>, Box<Expr>),
  LAnd(Box<Expr>, Box<Expr>),
  LOr(Box<Expr>, Box<Expr>),
  Block(Vec<Expr>),
  As(Box<Expr>, Box<Expr>),
  Rmw(BinOp, Box<Expr>, Box<Expr>),
  Continue,
  Break(Box<Expr>),
  Return(Box<Expr>),
  Let(RefStr, IsMut, Option<Ty>, Option<Box<Expr>>),
  If(Box<Expr>, Box<Expr>, Box<Expr>),
  While(Box<Expr>, Box<Expr>),
  Loop(Box<Expr>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId(usize);

impl fmt::Debug for DefId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}

#[derive(Debug)]
pub enum Def {
  Type(TypeDef),
  Struct(StructDef),
  Union(UnionDef),
  Enum(EnumDef),
  Const(ConstDef),
  Data(DataDef),
  Func(FuncDef),
  ExternData(ExternDataDef),
  ExternFunc(ExternFuncDef)
}

#[derive(Debug)]
pub struct TypeDef {
  pub name: RefStr,
  pub ty: Ty
}

#[derive(Debug)]
pub struct StructDef {
  pub name: RefStr,
  pub type_params: Vec<RefStr>,
  pub params: Vec<(RefStr, Ty)>
}

#[derive(Debug)]
pub struct UnionDef {
  pub name: RefStr,
  pub type_params: Vec<RefStr>,
  pub params: Vec<(RefStr, Ty)>
}

#[derive(Debug)]
pub struct EnumDef {
  pub name: RefStr,
  pub type_params: Vec<RefStr>,
  pub variants: Vec<Variant>
}

#[derive(Debug)]
pub struct ConstDef {
  pub name: RefStr,
  pub ty: Ty,
  pub val: Expr
}

#[derive(Debug)]
pub struct DataDef {
  pub name: RefStr,
  pub is_mut: IsMut,
  pub ty: Ty,
  pub init: Expr
}

#[derive(Debug)]
pub struct FuncDef {
  pub name: RefStr,
  pub type_params: Vec<RefStr>,
  pub params: Vec<(RefStr, IsMut, Ty)>,
  pub ret_ty: Ty,
  pub body: Expr
}

#[derive(Debug)]
pub struct ExternDataDef {
  pub name: RefStr,
  pub is_mut: IsMut,
  pub ty: Ty
}

#[derive(Debug)]
pub struct ExternFuncDef {
  pub name: RefStr,
  pub params: Vec<(RefStr, Ty)>,
  pub varargs: bool,
  pub ret_ty: Ty
}

#[derive(Debug)]
pub enum Variant {
  Unit(RefStr),
  Struct(RefStr, Vec<(RefStr, Ty)>),
}

/// Parser API

pub fn parse_bundle(path: &std::path::Path) -> Result<Repository, Error> {
  let mut repo = Repository::new();
  repo.root_module_id = repo.parse_module(path)?;
  Ok(repo)
}

#[derive(Debug)]
pub struct Repository {
  def_cnt: usize,
  search_dirs: Vec<PathBuf>,
  pub root_module_id: DefId,
  pub defs: HashMap<DefId, Def>,
  pub syms: HashMap<DefId, HashMap<RefStr, DefId>>
}

impl Repository {
  pub fn new() -> Repository {
    // Crate repository
    Repository {
      def_cnt: 0,
      search_dirs: vec![ PathBuf::from(env!("MPC_STD_DIR")) ],
      root_module_id: DefId(0),
      defs: HashMap::new(),
      syms: HashMap::new()
    }
  }

  fn new_id(&mut self) -> DefId {
    let id = DefId(self.def_cnt);
    self.def_cnt += 1;
    id
  }

  fn def(&mut self, def: Def) -> DefId {
    let id = self.new_id();
    self.defs.insert(id, def);
    id
  }

  fn sym(&mut self, parent: DefId, name: RefStr, def: DefId) {
    if let Some(syms) = self.syms.get_mut(&parent) {
      syms.insert(name, def);
    } else {
      self.syms.insert(parent,HashMap::from([ (name, def) ]));
    }
  }

  pub fn resolve_global_def(&self, path: &Path) -> Option<DefId> {
    let mut cur_id = self.root_module_id;
    for crumb in path.iter() {
      let symtab = self.syms.get(&cur_id).unwrap();
      if let Some(def_id) = symtab.get(crumb) {
        cur_id = *def_id;
      } else {
        return None
      }
    }
    Some(cur_id)
  }

  fn find_module(&mut self, name: RefStr) -> Option<PathBuf> {
    for dir in self.search_dirs.iter().rev() {
      let path = dir
        .join(std::path::Path::new(name.borrow_rs()))
        .with_extension("m");
      if path.is_file() { return Some(path) }
    }
    None
  }

  fn parse_module(&mut self, path: &std::path::Path) -> Result<DefId, Error> {
    let input = fs::read_to_string(path)
      .map_err(|error| Error::IoError(path.to_path_buf(), error))?;
    let lexer = lexer::Lexer::new(&input);
    let parser = maple::ModuleParser::new();
    let module_id = self.new_id();
    self.search_dirs.push(path.parent().unwrap().to_path_buf());
    let result = match parser.parse(module_id, self, lexer) {
      Ok(()) => Ok(module_id),
      Err(err) => Err(Error::from_lalrpop(err))
    };
    self.search_dirs.pop();
    result
  }
}

#[derive(Clone,Copy,Default,Debug)]
pub struct Location {
  pub line: usize,
  pub column: usize
}

impl fmt::Display for Location {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    write!(fmt, "line {} column {}", self.line, self.column)
  }
}

#[derive(Debug)]
pub enum Error {
  IoError(PathBuf, io::Error),
  UnknownToken(Location),
  UnknownEscape(Location),
  UnterminatedStr(Location),
  UnterminatedChar(Location),
  UnterminatedComment(Location),
  InvalidChar(Location),
  UnexpectedToken(Location),
  UnexpectedEndOfFile(Location),
  UnknownModule(Location, RefStr)
}

impl Error {
  fn from_lalrpop(err: lalrpop_util::ParseError<Location, Token, Error>) -> Error {
    match err {
      // Parser expected a different token
      lalrpop_util::ParseError::UnrecognizedToken { token: (location, ..), .. } => {
        Error::UnexpectedToken(location)
      }
      // Parser expected token instead of EOF
      lalrpop_util::ParseError::UnrecognizedEOF { location, .. } => {
        Error::UnexpectedEndOfFile(location)
      }
      // Lexer errors propagate to here
      lalrpop_util::ParseError::User { error } => {
        error
      }
      // NOTE: the following two are not generated using our setup
      lalrpop_util::ParseError::InvalidToken { .. } => unreachable!(),
      lalrpop_util::ParseError::ExtraToken { .. } => unreachable!()
    }
  }
}

impl fmt::Display for Error {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    match self {
      Error::IoError(path, error) => write!(fmt, "{}: {}", path.to_string_lossy(), error),
      Error::UnknownToken(location) => write!(fmt, "Error at {}: Unknown token", location),
      Error::UnknownEscape(location) => write!(fmt, "Error at {}: Unknown escape sequence", location),
      Error::UnterminatedStr(location) => write!(fmt, "Error at {}: Unterminated string literal", location),
      Error::UnterminatedChar(location) => write!(fmt, "Error at {}: Unterminated character literal", location),
      Error::UnterminatedComment(location) => write!(fmt, "Error at {}: Unterminated block comment", location),
      Error::InvalidChar(location) => write!(fmt, "Error at {}: Invalid char literal", location),
      Error::UnexpectedToken(location) => write!(fmt, "Error at {}: Unexpected token", location),
      Error::UnexpectedEndOfFile(location) => write!(fmt, "Error at {}: Unexpected end of file", location),
      Error::UnknownModule(location, name) => write!(fmt, "Error at {}: Unknown module {}", location, name)
    }
  }
}

impl error::Error for Error {}