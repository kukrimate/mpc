use crate::util::*;
use lalrpop_util::{self,lalrpop_mod};
use std::collections::HashSet;
use std::{error,fs,fmt};

lalrpop_mod!(maple, "/parse/maple.rs");

/// Syntax tree produced by the parser

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
  Fn(Vec<(RefStr, TyRef)>, Box<TyRef>),
  Ptr(IsMut, Box<TyRef>),
  Arr(Box<Expr>, Box<TyRef>),
  Tuple(Vec<(RefStr, TyRef)>),
}

#[derive(Debug)]
pub enum Variant {
  Unit,
  Struct(Vec<(RefStr, TyRef)>),
}

#[derive(Debug)]
pub enum TyDef {
  Struct {
    name: RefStr,
    params: Vec<(RefStr, TyRef)>,
  },
  Union {
    name: RefStr,
    params: Vec<(RefStr, TyRef)>,
  },
  Enum {
    name: RefStr,
    variants: Vec<(RefStr, Variant)>,
  },
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
  Char(RefStr),
  Str(RefStr),
  Dot(Box<Expr>, RefStr),
  Call(Box<Expr>, Vec<(RefStr, Expr)>),
  Index(Box<Expr>, Box<Expr>),
  Adr(Box<Expr>),
  Ind(Box<Expr>),
  Un(UnOp, Box<Expr>),
  LNot(Box<Expr>),
  Cast(Box<Expr>, TyRef),
  Bin(BinOp, Box<Expr>, Box<Expr>),
  LAnd(Box<Expr>, Box<Expr>),
  LOr(Box<Expr>, Box<Expr>),
  Block(Vec<Expr>),
  As(Box<Expr>, Box<Expr>),
  Rmw(BinOp, Box<Expr>, Box<Expr>),
  Continue,
  Break(Box<Expr>),
  Return(Box<Expr>),
  Let(RefStr, IsMut, Option<TyRef>, Box<Expr>),
  If(Box<Expr>, Box<Expr>, Box<Expr>),
  While(Box<Expr>, Box<Expr>),
  Loop(Box<Expr>),
}

#[derive(Debug)]
pub enum Def {
  Const {
    name: RefStr,
    ty: TyRef,
    val: Expr
  },
  Data {
    name: RefStr,
    is_mut: IsMut,
    ty: TyRef,
    init: Expr
  },
  Fn {
    name: RefStr,
    params: Vec<(RefStr, IsMut, TyRef)>,
    ret_ty: TyRef,
    body: Expr,
  },
  ExternData {
    name: RefStr,
    is_mut: IsMut,
    ty: TyRef,
  },
  ExternFn {
    name: RefStr,
    params: Vec<(RefStr, TyRef)>,
    ret_ty: TyRef,
  },
}

#[derive(Debug)]
pub struct Module {
  pub deps: HashSet<RefStr>,
  pub defs: Vec<Def>,
  pub ty_defs: Vec<TyDef>,
}

impl Module {
  pub fn new() -> Module {
    Module {
      deps: HashSet::new(),
      defs: Vec::new(),
      ty_defs: Vec::new(),
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
  match maple::ModuleParser::new().parse(&mut module, &input) {
    Ok(()) => Ok(module),
    Err(error) => Err(Box::new(
      SyntaxError::new(error))),
  }
}
