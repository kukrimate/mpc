use crate::util::*;
use indexmap::IndexMap;
use std::collections::HashSet;

pub type Path = Vec<RefStr>;

#[derive(Debug)]
pub enum Ty {
  Path(Path),
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
  Fn(IndexMap<RefStr, Ty>, Box<Ty>),
  Ptr(Box<Ty>),
  Arr(Box<Expr>, Box<Ty>),
  Tuple(IndexMap<RefStr, Ty>),
  Struct(IndexMap<RefStr, Ty>),
  Union(IndexMap<RefStr, Ty>),
  Enumerator,
  Enum(IndexMap<RefStr, Ty>),
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
pub enum Def {
  Ty(Ty),
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
