use crate::util::*;
use indexmap::IndexMap;
use lalrpop_util::{self,lalrpop_mod};
use std::collections::HashSet;
use std::{error,fs,fmt};

lalrpop_mod!(parse_gen);

/// Syntax tree produced by the parser

pub type Path = Vec<RefStr>;

#[derive(Debug)]
pub enum TyRef {
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
  Path(Path),
  Fn(IndexMap<RefStr, TyRef>, Box<TyRef>),
  Ptr(Box<TyRef>),
  Arr(Box<Expr>, Box<TyRef>),
  Tuple(IndexMap<RefStr, TyRef>),
}

#[derive(Debug)]
pub enum Variant {
  Unit,
  Struct(IndexMap<RefStr, TyRef>),
}

#[derive(Debug)]
pub enum TyDef {
  Struct {
    params: IndexMap<RefStr, TyRef>,
  },
  Union {
    params: IndexMap<RefStr, TyRef>,
  },
  Enum {
    variants: IndexMap<RefStr, Variant>,
  },
}

#[derive(Clone,Copy,Debug)]
pub enum BinOp {
  Mul, Div, Mod, Add, Sub, Lsh, Rsh, And, Xor, Or, Eq, Ne, Lt, Gt, Le, Ge, LAnd, LOr
}

#[derive(Debug)]
pub enum Expr {
  Path(Path),
  Bool(bool),
  Int(usize),
  Char(RefStr),
  Str(RefStr),

  Dot(Box<Expr>, RefStr),
  Call(Box<Expr>, IndexMap<RefStr, Expr>),
  Index(Box<Expr>, Box<Expr>),

  Adr(Box<Expr>),
  Ind(Box<Expr>),
  UPlus(Box<Expr>),
  UMinus(Box<Expr>),
  Not(Box<Expr>),
  LNot(Box<Expr>),

  Cast(Box<Expr>, TyRef),

  Bin(BinOp, Box<Expr>, Box<Expr>),

  As(Box<Expr>, Box<Expr>),
  Rmw(BinOp, Box<Expr>, Box<Expr>),

  Block(Vec<Expr>),
  Continue,
  Break(Option<Box<Expr>>),
  Return(Option<Box<Expr>>),
  Let(RefStr, bool, Option<TyRef>, Box<Expr>),
  If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
  While(Box<Expr>, Box<Expr>),
  Loop(Box<Expr>),
}

#[derive(Debug)]
pub enum Def {
  Const {
    ty: TyRef,
    val: Expr
  },
  Data {
    is_mut: bool,
    ty: TyRef,
    init: Expr
  },
  Fn {
    params: IndexMap<RefStr, (bool, TyRef)>,
    ret_ty: TyRef,
    body: Expr,
  },
  Extern {
    is_mut: bool,
    ty: TyRef,
  },
  ExternFn {
    params: IndexMap<RefStr, TyRef>,
    ret_ty: TyRef,
  },
}

#[derive(Debug)]
pub struct Module {
  pub deps: HashSet<RefStr>,
  pub defs: IndexMap<RefStr, Def>,
  pub ty_defs: IndexMap<RefStr, TyDef>,
}

impl Module {
  pub fn new() -> Module {
    Module {
      deps: HashSet::new(),
      defs: IndexMap::new(),
      ty_defs: IndexMap::new(),
    }
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
  let mut module = Module::new();
  match parse_gen::ModuleParser::new().parse(&mut module, &input) {
    Ok(()) => Ok(module),
    Err(error) => Err(Box::new(
      SyntaxError::new(error))),
  }
}
