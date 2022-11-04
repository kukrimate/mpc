// SPDX-License-Identifier: GPL-2.0-only

//
// Semantic analysis
//
// Type checking and LLVM lowering is done by this module. These two passes
// operate on the same intermediate representation.
//

use crate::parse::{self,IsMut,UnOp,BinOp};
use crate::util::*;
use std::fmt::{self,Write};
use indexmap::IndexMap;
use llvm_sys::prelude::*;

/// Types

#[derive(Clone)]
pub enum Ty {
  // Real types
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
  Ref(RefStr, Ptr<TyDef>),
  Fn(Vec<(RefStr, Ty)>, Box<Ty>),
  Ptr(IsMut, Box<Ty>),
  Arr(usize, Box<Ty>),
  Tuple(Vec<(RefStr, Ty)>),
  // Deduction
  ClassAny,
  ClassNum,
  ClassInt,
}

pub enum Variant {
  Unit(RefStr),
  Struct(RefStr, Vec<(RefStr, Ty)>),
}

pub struct TyDef {
  name: RefStr,
  kind: TyDefKind,
  l_type: LLVMTypeRef,
}

pub enum TyDefKind {
  ToBeFilled,
  Struct(Vec<(RefStr, Ty)>),
  Union(Vec<(RefStr, Ty)>),
  Enum(Vec<(RefStr, Variant)>),
}

impl TyDef {
  fn new(name: RefStr) -> Self {
    TyDef {
      name,
      kind: TyDefKind::ToBeFilled,
      l_type: std::ptr::null_mut()
    }
  }
}

fn write_params(f: &mut fmt::Formatter<'_>, params: &Vec<(RefStr, Ty)>) -> fmt::Result {
  write_comma_separated(f, params.iter(), |f, (name, ty)| write!(f, "{}: {:?}", name, ty))
}

impl fmt::Debug for TyDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &self.kind {
      TyDefKind::ToBeFilled => unreachable!(),
      TyDefKind::Struct(params) => {
        write!(f, "struct {} ", self.name)?;
        write_params(f, params)
      },
      TyDefKind::Union(params) => {
        write!(f, "union {} ", self.name)?;
        write_params(f, params)
      },
      TyDefKind::Enum(variants) => {
        write!(f, "enum {} ", self.name)?;
        write_comma_separated(f, variants.iter(), |f, (_, variant)| {
          match variant {
            Variant::Unit(name) => {
              write!(f, "{}", name)
            },
            Variant::Struct(name, params) => {
              write!(f, "{} ", name)?;
              write_params(f, params)
            },
          }
        })
      }
    }
  }
}

impl fmt::Debug for Ty {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use Ty::*;
    match self {
      Bool => write!(f, "Bool"),
      Uint8 => write!(f, "Uint8"),
      Int8 => write!(f, "Int8"),
      Uint16 => write!(f, "Uint16"),
      Int16 => write!(f, "Int16"),
      Uint32 => write!(f, "Uint32"),
      Int32 => write!(f, "Int32"),
      Uint64 => write!(f, "Uint64"),
      Int64 => write!(f, "Int64"),
      Uintn => write!(f, "Uintn"),
      Intn => write!(f, "Intn"),
      Float => write!(f, "Float"),
      Double => write!(f, "Double"),
      Ref(name, _) => write!(f, "{}", name),
      Fn(params, ty) => {
        write!(f, "Function")?;
        write_params(f, params)?;
        write!(f, " -> {:?}", ty)
      },
      Ptr(is_mut, ty) => write!(f, "*{}{:?}", is_mut, ty),
      Arr(cnt, ty) => write!(f, "[{}]{:?}", cnt, ty),
      Tuple(params) => write_params(f, params),
      ClassAny => write!(f, "ClassAny"),
      ClassNum => write!(f, "ClassNum"),
      ClassInt => write!(f, "ClassInt"),
    }
  }
}

/// Expressions

pub type Expr = Own<ExprS>;

pub struct ExprS {
  ty: Ty,
  kind: ExprKind,
}

pub enum ExprKind {
  Ref(Ptr<Def>),
  Bool(bool),
  Int(usize),
  Char(RefStr),
  Str(RefStr),
  Dot(IsMut, Expr, RefStr, usize),
  Call(Expr, Vec<(RefStr, Expr)>),
  Index(IsMut, Expr, Expr),
  Adr(Expr),
  Ind(IsMut, Expr),
  Un(UnOp, Expr),
  LNot(Expr),
  Cast(Expr, Ty),
  Bin(BinOp, Expr, Expr),
  LAnd(Expr, Expr),
  LOr(Expr, Expr),
  Block(IndexMap<RefStr, Own<Def>>, Vec<Expr>),
  As(Expr, Expr),
  Rmw(BinOp, Expr, Expr),
  Continue,
  Break(Option<Expr>),
  Return(Option<Expr>),
  Let(Ptr<Def>, Expr),
  If(Expr, Expr, Expr),
  While(Expr, Expr),
  Loop(Expr),
}

impl ExprS {
  fn new(ty: Ty, kind: ExprKind) -> Expr {
    Own::new(ExprS { ty, kind })
  }
}

impl fmt::Debug for ExprS {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use ExprKind::*;
    match &self.kind {
      Ref(def) => write!(f, "{}", def.name),
      Bool(val) => write!(f, "{}", val),
      Int(val) => write!(f, "{}", val),
      Char(val) => write!(f, "c{:?}", val),
      Str(val) => write!(f, "s{:?}", val),
      Dot(_, arg, name, _) => write!(f, ". {:?} {}", arg, name),
      Call(arg, args) => {
        write!(f, "{:?}", arg)?;
        write_comma_separated(f, args.iter(),
          |f, (name, arg)| write!(f, "{}: {:?}", name, arg))
      }
      Index(_, arg, idx) => write!(f, "{:?}[{:?}]", arg, idx),
      Adr(arg) => write!(f, "Adr {:?}", arg),
      Ind(_, arg) => write!(f, "Ind {:?}", arg),
      Un(op, arg) => write!(f, "{:?} {:?}", op, arg),
      LNot(arg) => write!(f, "LNot {:?}", arg),
      Cast(arg, ty) => write!(f, "Cast {:?} {:?}", arg, ty),
      Bin(op, lhs, rhs) => write!(f, "{:?} {:?} {:?}", op, lhs, rhs),
      LAnd(lhs, rhs) => write!(f, "LAnd {:?} {:?}", lhs, rhs),
      LOr(lhs, rhs) => write!(f, "LOr {:?} {:?}", lhs, rhs),
      As(dst, src) => write!(f, "As {:?} {:?}", dst, src),
      Rmw(op, lhs, rhs) => write!(f, "{:?}As {:?} {:?}", op, lhs, rhs),
      Block(_, body) => {
        write!(f, "{{\n")?;
        let mut pf = PadAdapter::wrap(f);
        for expr in body {
          write!(&mut pf, "{:?};\n", expr)?;
        }
        write!(f, "}}")
      },
      Continue => write!(f, "continue"),
      Break(None) => write!(f, "break"),
      Break(Some(arg)) => write!(f, "break {:?}", arg),
      Return(None) => write!(f, "return"),
      Return(Some(arg)) => write!(f, "return {:?}", arg),
      Let(def, init) => write!(f, "let {}{}: {:?} = {:?}",
                                def.is_mut, def.name, def.ty, init),
      If(cond, tbody, ebody) => write!(f, "if {:?} {:?} {:?}",
                                        cond, tbody, ebody),
      While(cond, body) => write!(f, "while {:?} {:?}", cond, body),
      Loop(body) => write!(f, "loop {:?}", body),
    }
  }
}

/// Definitions

pub struct Def {
  name: RefStr,
  is_mut: IsMut,
  ty: Ty,
  kind: DefKind,
  l_value: LLVMValueRef,
}

pub enum DefKind {
  ToBeFilled,
  Const(Expr),
  Func(IndexMap<RefStr, Own<Def>>, Expr),
  Data(Expr),
  ExternFunc,
  ExternData,
  Param(usize),
  Local,
}

impl Def {
  fn empty(name: RefStr, is_mut: IsMut, ty: Ty) -> Self {
    Def { name, is_mut, ty, kind: DefKind::ToBeFilled, l_value: std::ptr::null_mut() }
  }

  fn with_kind(name: RefStr, is_mut: IsMut, ty: Ty, kind: DefKind) -> Self {
    Def { name, is_mut, ty, kind, l_value: std::ptr::null_mut() }
  }
}

impl fmt::Debug for Def {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &self.kind {
      DefKind::ToBeFilled => unreachable!(),
      DefKind::Const(val) => {
        write!(f, "const {}: {:?} = {:#?}", self.name, val.ty, val)
      }
      DefKind::Func(params, body) => {
        write!(f, "fn {}(", self.name)?;
        let mut first = true;
        for (_, param) in params {
          if first {
            first = false;
          } else {
            write!(f, ", ")?;
          }
          write!(f, "{}{}: {:?}", param.is_mut, param.name, param.ty)?;
        }
        write!(f, ") -> {:?} {:#?}", body.ty, body)
      }
      DefKind::Data(init) => {
        write!(f, "data {}{}: {:?} = {:#?}",
          self.is_mut, self.name, init.ty, init)
      }
      DefKind::ExternFunc => {
        write!(f, "extern fn {}: {:?}", self.name, self.ty)
      }
      DefKind::ExternData => {
        write!(f, "extern data {}{}: {:?}", self.is_mut, self.name, self.ty)
      }
      DefKind::Param(index) => {
        todo!()
      }
      DefKind::Local => {
        todo!()
      }
    }
  }
}

/// Module

pub struct Module {
  // Type definitions
  pub ty_defs: IndexMap<RefStr, Own<TyDef>>,
  // Definitions
  pub defs: Vec<IndexMap<RefStr, Own<Def>>>,
}

/// Type checker and lowerer live in their own files

pub mod check;
pub mod lower;
