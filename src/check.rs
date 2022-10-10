use crate::parse;
use crate::util::*;
use indexmap::{indexmap,IndexMap};
use std::{error,fmt};
use std::collections::{HashMap};

/// Syntax tree after type checking

pub type Ty = Ptr<TyS>;

#[derive(Debug)]
pub enum TyS {
  Unresolved,

  Var(usize),

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
  Fn(IndexMap<RefStr, Ty>, Ty),
  Ptr(Ty),
  Arr(usize, Ty),
  Unit(RefStr),
  Tuple(IndexMap<RefStr, Ty>),

  Struct(RefStr, IndexMap<RefStr, Ty>),
  Union(RefStr, IndexMap<RefStr, Ty>),
  Enum(RefStr, IndexMap<RefStr, Ty>),
}

pub type Expr = Ptr<ExprS>;

#[derive(Debug)]
pub struct ExprS {
  ty: Ty,
  kind: ExprKind,
}

#[derive(Debug)]
pub enum ExprKind {
  Unresolved,

  Def(Ty, Ptr<Def>),

  Bool(bool),
  Int(usize),
  Char(RefStr),
  Str(RefStr),

  Dot(Expr, RefStr),
  Call(Expr, IndexMap<RefStr, Expr>),
  Index(Expr, Expr),

  Ref(Expr),
  Deref(Expr),
  UPlus(Expr),
  UMinus(Expr),
  Not(Expr),
  LNot(Expr),

  Cast(Expr, Ty),

  Mul(Expr, Expr),
  Div(Expr, Expr),
  Mod(Expr, Expr),
  Add(Expr, Expr),
  Sub(Expr, Expr),
  Lsh(Expr, Expr),
  Rsh(Expr, Expr),
  And(Expr, Expr),
  Xor(Expr, Expr),
  Or(Expr, Expr),
  Eq(Expr, Expr),
  Ne(Expr, Expr),
  Lt(Expr, Expr),
  Gt(Expr, Expr),
  Le(Expr, Expr),
  Ge(Expr, Expr),
  LAnd(Expr, Expr),
  LOr(Expr, Expr),

  As(Expr, Expr),
  MulAs(Expr, Expr),
  DivAs(Expr, Expr),
  ModAs(Expr, Expr),
  AddAs(Expr, Expr),
  SubAs(Expr, Expr),
  LshAs(Expr, Expr),
  RshAs(Expr, Expr),
  AndAs(Expr, Expr),
  XorAs(Expr, Expr),
  OrAs(Expr, Expr),

  Block(Vec<Expr>),
  Continue,
  Break(Option<Expr>),
  Return(Option<Expr>),
  Let(RefStr, bool, Option<Ty>, Expr),
  If(Expr, Expr, Option<Expr>),
  While(Expr, Expr),
  Loop(Expr),
}

#[derive(Debug)]
pub enum Def {
  Ty(Ty),
  Fn(IndexMap<RefStr, (Ty, bool)>, Ty, Expr),
  Const(Ty, Expr),
  Data(Ty, bool, Expr),
  Extern(Ty, bool),
  ExternFn(IndexMap<RefStr, Ty>, Ty),
}

/// Errors occuring during type checking

#[derive(Debug)]
struct UnknownTypeError {
  name: RefStr
}

impl fmt::Display for UnknownTypeError {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    write!(fmt, "Unknown typename {}", self.name)
  }
}

impl error::Error for UnknownTypeError {}

#[derive(Debug)]
struct UnknownObjectError {
  name: RefStr
}

impl fmt::Display for UnknownObjectError {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    write!(fmt, "Unknown object {}", self.name)
  }
}

impl error::Error for UnknownObjectError {}

struct Ctx<'ctx> {
  module: &'ctx parse::Module,
  arena: Arena,
  globals: HashMap<RefStr, Def>,
  tvars: Vec<Ty>,
}

impl<'ctx> Ctx<'ctx> {
  fn new(module: &'ctx parse::Module) -> Self {
    Ctx {
      module,
      arena: Arena::new(),
      globals: HashMap::new(),
      tvars: Vec::new(),
    }
  }

  fn alloc_ty(&mut self, ty: TyS) -> Ty {
    self.arena.alloc(ty).ptr()
  }

  fn alloc_expr(&mut self, expr: ExprS) -> Expr {
    self.arena.alloc(expr).ptr()
  }

  fn newtvar(&mut self) -> Ty {
    let ty = self.alloc_ty(TyS::Var(self.tvars.len()));
    self.tvars.push(ty);
    ty
  }

  fn resolve_ty(&mut self, name: RefStr) -> MRes<Ty> {
    match self.globals.get(&name) {
      Some(Def::Ty(ty)) => Ok(*ty),
      _ => Err(Box::new(UnknownTypeError { name })),
    }
  }

  fn check_params(&mut self, params: &IndexMap<RefStr, parse::Ty>) -> MRes<IndexMap<RefStr, Ty>> {
    let mut nparams = indexmap!{};
    for (name, ty) in params {
      nparams.insert(*name, self.check_ty(ty)?);
    }
    Ok(nparams)
  }

  fn check_variants(&mut self, variants: &IndexMap<RefStr, parse::Variant>) -> MRes<IndexMap<RefStr, Ty>> {
    let mut nparams = indexmap!{};
    for (name, variant) in variants {
      use parse::Variant::*;
      match variant {
        Unit => {
          nparams.insert(*name, self.alloc_ty(TyS::Unit(*name)));
        }
        Struct(params) => {
          let sparams = self.check_params(params)?;
          nparams.insert(*name, self.alloc_ty(TyS::Struct(*name, sparams)));
        }
      }
    }
    Ok(nparams)
  }

  fn check_ty(&mut self, ty: &parse::Ty) -> MRes<Ty> {
    use parse::Ty::*;
    Ok(match ty {
      Bool => self.alloc_ty(TyS::Bool),
      Uint8 => self.alloc_ty(TyS::Uint8),
      Int8 => self.alloc_ty(TyS::Int8),
      Uint16 => self.alloc_ty(TyS::Uint16),
      Int16 => self.alloc_ty(TyS::Int16),
      Uint32 => self.alloc_ty(TyS::Uint32),
      Int32 => self.alloc_ty(TyS::Int32),
      Uint64 => self.alloc_ty(TyS::Uint64),
      Int64 => self.alloc_ty(TyS::Int64),
      Uintn => self.alloc_ty(TyS::Uintn),
      Intn => self.alloc_ty(TyS::Intn),
      Float => self.alloc_ty(TyS::Float),
      Double => self.alloc_ty(TyS::Double),
      Path(path) => self.resolve_ty(path[0])?,
      Fn(params, ret_ty) => {
        let ty = TyS::Fn(self.check_params(params)?,
                              self.check_ty(ret_ty)?);
        self.alloc_ty(ty)
      },
      Ptr(base_ty) => {
        let ty = TyS::Ptr(self.check_ty(base_ty)?);
        self.alloc_ty(ty)
      },
      Arr(elem_cnt, elem_ty) => {
        // FIXME: evaluate elem_cnt constant expression
        let ty = TyS::Arr(0, self.check_ty(elem_ty)?);
        self.alloc_ty(ty)
      },
      Tuple(params) => {
        let ty = TyS::Tuple(self.check_params(params)?);
        self.alloc_ty(ty)
      }
    })
  }

  fn resolve_def(&mut self, name: RefStr) -> MRes<Expr> {
    match self.globals.get(&name) {
      Some(Def::Ty(_)) | None => Err(Box::new(UnknownObjectError { name })),
      Some(def) => todo!(),
    }
  }

  fn check_expr(&mut self, expr: &parse::Expr) -> MRes<Expr> {
    use parse::Expr::*;

    Ok(match expr {
      Path(path) => {
        self.resolve_def(path[0])?
      }
      Bool(val) => {
        let ty = self.alloc_ty(TyS::Bool);
        self.alloc_expr(ExprS {
          ty: ty,
          kind: ExprKind::Bool(*val),
        })
      }
      Int(val) => {
        let ty = self.newtvar();
        self.alloc_expr(ExprS {
          ty: ty,
          kind: ExprKind::Int(*val),
        })
      }
      Char(val) => {
        let ty = self.newtvar();
        self.alloc_expr(ExprS {
          ty: ty,
          kind: ExprKind::Char(*val),
        })
      }
      Str(val) => {
        let ty = self.newtvar();
        self.alloc_expr(ExprS {
          ty: ty,
          kind: ExprKind::Str(*val),
        })
      }

      Dot(arg, name) => {
        let arg = self.check_expr(arg)?;
        let ty = match arg.ty {

        };
        self.alloc_expr(ExprS {
          ty: ty,
          kind: ExprKind::Dot(arg, *name),
        })
      }
      Call(arg, args) => {
        todo!()
      }
      Index(arg, idx) => {
        todo!()
      }

      Ref(arg) => {
        todo!()
      }
      Deref(arg) => {
        todo!()
      }
      UPlus(arg) => {
        todo!()
      }
      UMinus(arg) => {
        todo!()
      }
      Not(arg) => {
        todo!()
      }
      LNot(arg) => {
        todo!()
      }

      Cast(arg, ty) => {
        todo!()
      }

      Mul(lhs, rhs) => {
        todo!()
      }
      Div(lhs, rhs) => {
        todo!()
      }
      Mod(lhs, rhs) => {
        todo!()
      }
      Add(lhs, rhs) => {
        todo!()
      }
      Sub(lhs, rhs) => {
        todo!()
      }
      Lsh(lhs, rhs) => {
        todo!()
      }
      Rsh(lhs, rhs) => {
        todo!()
      }
      And(lhs, rhs) => {
        todo!()
      }
      Xor(lhs, rhs) => {
        todo!()
      }
      Or(lhs, rhs) => {
        todo!()
      }
      Eq(lhs, rhs) => {
        todo!()
      }
      Ne(lhs, rhs) => {
        todo!()
      }
      Lt(lhs, rhs) => {
        todo!()
      }
      Gt(lhs, rhs) => {
        todo!()
      }
      Le(lhs, rhs) => {
        todo!()
      }
      Ge(lhs, rhs) => {
        todo!()
      }
      LAnd(lhs, rhs) => {
        todo!()
      }
      LOr(lhs, rhs) => {
        todo!()
      }

      As(lhs, rhs) => {
        todo!()
      }
      MulAs(lhs, rhs) => {
        todo!()
      }
      DivAs(lhs, rhs) => {
        todo!()
      }
      ModAs(lhs, rhs) => {
        todo!()
      }
      AddAs(lhs, rhs) => {
        todo!()
      }
      SubAs(lhs, rhs) => {
        todo!()
      }
      LshAs(lhs, rhs) => {
        todo!()
      }
      RshAs(lhs, rhs) => {
        todo!()
      }
      AndAs(lhs, rhs) => {
        todo!()
      }
      XorAs(lhs, rhs) => {
        todo!()
      }
      OrAs(lhs, rhs) => {
        todo!()
      }

      Block(body) => {
        todo!()
      }
      Continue => {
        todo!()
      }
      Break(arg) => {
        todo!()
      }
      Return(arg) => {
        todo!()
      }
      Let(name, is_mut, ty, init) => {
        todo!()
      }
      If(cond, tbody, ebody) => {
        todo!()
      }
      While(cond, body) => {
        todo!()
      }
      Loop(body) => {
        todo!()
      }
    })
  }

  fn check_root(&mut self) -> MRes<()> {
    // Pass 1: create symbols
    let mut todo_types = vec![];

    for (name, def) in &self.module.defs {
      match def {
        parse::Def::Struct { .. } |
        parse::Def::Union { .. } |
        parse::Def::Enum { .. } => {
          let ptr_mut = self.arena.alloc(TyS::Unresolved);
          self.globals.insert(*name, Def::Ty(ptr_mut.ptr()));
          todo_types.push((*name, def, ptr_mut));
        },
        parse::Def::Fn { params, ret_ty, body } => {

        }
        _ => continue,
      }
    }

    // Pass 2: resolve references
    for (name, def, ptr_mut) in &mut todo_types {
      let ty = match def {
        parse::Def::Struct { params }
          => TyS::Struct(*name, self.check_params(params)?),
        parse::Def::Union { params }
          => TyS::Union(*name, self.check_params(params)?),
        parse::Def::Enum { variants }
          => TyS::Enum(*name, self.check_variants(variants)?),
        _ => unreachable!(),
      };
      **ptr_mut = ty;
    }

    println!("{:#?}", self.globals);
    Ok(())
  }
}

pub fn check_module(module: &parse::Module) -> MRes<()> {
  let mut ctx = Ctx::new(module);
  ctx.check_root()
}
