use crate::util::*;
use indexmap::IndexMap;
use lalrpop_util::{self,lalrpop_mod};
use std::collections::HashSet;
use std::{error,fs,fmt};

lalrpop_mod!(parse_gen);

/// Syntax tree produced by the parser

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
  Path(Path),
  Fn(IndexMap<RefStr, Ty>, Box<Ty>),
  Ptr(Box<Ty>),
  Arr(Box<Expr>, Box<Ty>),
  Tuple(IndexMap<RefStr, Ty>),
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

  Ref(Box<Expr>),
  Deref(Box<Expr>),
  UPlus(Box<Expr>),
  UMinus(Box<Expr>),
  Not(Box<Expr>),
  LNot(Box<Expr>),

  Cast(Box<Expr>, Ty),

  Mul(Box<Expr>, Box<Expr>),
  Div(Box<Expr>, Box<Expr>),
  Mod(Box<Expr>, Box<Expr>),
  Add(Box<Expr>, Box<Expr>),
  Sub(Box<Expr>, Box<Expr>),
  Lsh(Box<Expr>, Box<Expr>),
  Rsh(Box<Expr>, Box<Expr>),
  And(Box<Expr>, Box<Expr>),
  Xor(Box<Expr>, Box<Expr>),
  Or(Box<Expr>, Box<Expr>),
  Eq(Box<Expr>, Box<Expr>),
  Ne(Box<Expr>, Box<Expr>),
  Lt(Box<Expr>, Box<Expr>),
  Gt(Box<Expr>, Box<Expr>),
  Le(Box<Expr>, Box<Expr>),
  Ge(Box<Expr>, Box<Expr>),
  LAnd(Box<Expr>, Box<Expr>),
  LOr(Box<Expr>, Box<Expr>),

  As(Box<Expr>, Box<Expr>),
  MulAs(Box<Expr>, Box<Expr>),
  DivAs(Box<Expr>, Box<Expr>),
  ModAs(Box<Expr>, Box<Expr>),
  AddAs(Box<Expr>, Box<Expr>),
  SubAs(Box<Expr>, Box<Expr>),
  LshAs(Box<Expr>, Box<Expr>),
  RshAs(Box<Expr>, Box<Expr>),
  AndAs(Box<Expr>, Box<Expr>),
  XorAs(Box<Expr>, Box<Expr>),
  OrAs(Box<Expr>, Box<Expr>),

  Block(Vec<Expr>),
  Continue,
  Break(Option<Box<Expr>>),
  Return(Option<Box<Expr>>),
  Let(RefStr, bool, Option<Ty>, Box<Expr>),
  If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
  While(Box<Expr>, Box<Expr>),
  Loop(Box<Expr>),
}

#[derive(Debug)]
pub enum Variant {
  Unit,
  Struct(IndexMap<RefStr, Ty>),
}

#[derive(Debug)]
pub enum Def {
  Struct {
    params: IndexMap<RefStr, Ty>,
  },
  Union {
    params: IndexMap<RefStr, Ty>,
  },
  Enum {
    variants: IndexMap<RefStr, Variant>,
  },
  Fn {
    params: IndexMap<RefStr, (bool, Ty)>,
    ret_ty: Ty,
    body: Expr,
  },
  Const {
    ty: Ty,
    val: Expr
  },
  Data {
    is_mut: bool,
    ty: Ty,
    init: Expr
  },
  Extern {
    is_mut: bool,
    ty: Ty,
  },
  ExternFn {
    params: IndexMap<RefStr, Ty>,
    ret_ty: Ty,
  },
}

#[derive(Debug)]
pub struct Module {
  pub deps: HashSet<RefStr>,
  pub defs: IndexMap<RefStr, Def>,
}

impl Module {
  pub fn new() -> Module {
    Module {
      deps: HashSet::new(),
      defs: IndexMap::new(),
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
