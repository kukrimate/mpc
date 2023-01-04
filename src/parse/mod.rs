use crate::util::*;
use lalrpop_util::{self,lalrpop_mod};
use std::collections::{HashMap,HashSet};
use std::{error,fs,fmt};

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
  Null,
  Path(Path),
  Bool(bool),
  Int(usize),
  Flt(f64),
  Char(Vec<u8>),
  Str(Vec<u8>),
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
  Let(RefStr, IsMut, Option<Ty>, Box<Expr>),
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
  pub variants: Vec<(RefStr, Variant)>
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
  pub ret_ty: Ty
}

impl Def {
  pub fn name(&self) -> RefStr {
    match self {
      Def::Struct(def) => def.name,
      Def::Union(def) => def.name,
      Def::Enum(def) => def.name,
      Def::Const(def) => def.name,
      Def::Data(def) => def.name,
      Def::Func(def) => def.name,
      Def::ExternData(def) => def.name,
      Def::ExternFunc(def) => def.name,
    }
  }
}

#[derive(Debug)]
pub enum Variant {
  Unit,
  Struct(Vec<(RefStr, Ty)>),
}

#[derive(Debug)]
pub struct Module {
  pub deps: HashSet<RefStr>,
  pub defs: HashMap<DefId, Def>,
}

impl Module {
  pub fn new() -> Module {
    Module {
      deps: HashSet::new(),
      defs: HashMap::new(),
    }
  }

  fn def(&mut self, def: Def) {
    let id = DefId(self.defs.len());
    self.defs.insert(id, def);
  }
}

/// Wrapper around lalrpop

#[derive(Debug)]
struct SyntaxError {
  msg: RefStr
}

impl SyntaxError {
  fn new<T: fmt::Debug, E: fmt::Debug>(e: lalrpop_util::ParseError<usize, T, E>) -> SyntaxError {
    let s = format!("{:?}", e);
    SyntaxError { msg: RefStr::new(&s) }
  }
}

impl fmt::Display for SyntaxError {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    write!(fmt, "{}", self.msg)
  }
}

impl error::Error for SyntaxError {}

pub fn parse_module(path: &str) -> MRes<Module> {
  let input = fs::read_to_string(path)?;
  let mut lexer = lexer::Lexer::new(&input);
  let mut module = Module::new();

  match maple::ModuleParser::new().parse(&mut module, &mut lexer) {
    Ok(()) => Ok(module),
    Err(error) => Err(Box::new(SyntaxError::new(error))),
  }
}
