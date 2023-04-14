/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

//
// Semantic analysis
//
// Type checking and LLVM lowering is done by this module. These two passes
// operate on the same intermediate representation.
//

use crate::CompileError;
use crate::parse::{self, IsMut, UnOp, BinOp, DefId};
use crate::util::*;
use std::collections::HashMap;
use std::fmt;

mod consteval;
mod infer;
mod tctx;
mod inst;

use infer::*;
use inst::*;
pub use consteval::*;
pub use tctx::*;

pub fn analyze(repo: &parse::Repository) -> Result<Collection, CompileError> {
  let mut tctx = TVarCtx::new();
  let insts = infer(repo, &mut tctx)?;
  if let Some(_) = option_env!("MPC_SPEW") {
    eprintln!("{:#?}", insts);
    eprintln!("{:#?}", tctx);
  }
  Ok(Collection {
    tctx,
    insts
  })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LocalId(pub(super) usize);

/// Instance list
pub struct Collection {
  pub tctx: TVarCtx,
  pub insts: HashMap<(DefId, Vec<Ty>), Inst>
}

/// Definition instances
#[derive(Debug)]
pub enum Inst {
  Struct {
    name: RefStr,
    params: Option<Vec<(RefStr, Ty)>>
  },
  Union {
    name: RefStr,
    params: Option<Vec<(RefStr, Ty)>>
  },
  Enum {
    name: RefStr,
    variants: Vec<DefId>
  },
  UnitVariant {
    name: RefStr,
    parent_enum: (DefId, Vec<Ty>),
    variant_index: usize
  },
  StructVariant {
    name: RefStr,
    parent_enum: (DefId, Vec<Ty>),
    variant_index: usize,
    params: Vec<(RefStr, Ty)>
  },
  Func {
    name: RefStr,
    ty: Ty,
    params: Vec<LocalId>,
    locals: HashMap<LocalId, (IsMut, Ty)>,
    body: Option<RValue>
  },
  Data {
    name: RefStr,
    ty: Ty,
    is_mut: IsMut,
    init: ConstVal
  },
  ExternFunc {
    name: RefStr,
    ty: Ty
  },
  ExternData {
    name: RefStr,
    ty: Ty,
    is_mut: IsMut
  }
}

impl Inst {
  pub fn unwrap_struct(&self) -> (&RefStr, &Vec<(RefStr, Ty)>) {
    if let Inst::Struct { name, params } = self {
      (name, params.as_ref().unwrap())
    } else {
      unreachable!()
    }
  }

  pub fn unwrap_union(&self) -> (&RefStr, &Vec<(RefStr, Ty)>) {
    if let Inst::Union { name, params } = self {
      (name, params.as_ref().unwrap())
    } else {
      unreachable!()
    }
  }

  pub fn unwrap_enum(&self) -> (&RefStr, &Vec<DefId>) {
    if let Inst::Enum { name, variants } = self {
      (name, variants)
    } else {
      unreachable!()
    }
  }

  pub fn unwrap_struct_variant(&self) -> &Vec<(RefStr, Ty)> {
    if let Inst::StructVariant { params, .. } = self {
      params
    } else {
      unreachable!()
    }
  }
}

/// Types
#[derive(Clone, PartialEq, Eq, Hash)]
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
  StructRef(RefStr, (DefId, Vec<Ty>)),
  UnionRef(RefStr, (DefId, Vec<Ty>)),
  EnumRef(RefStr, (DefId, Vec<Ty>)),
  Ptr(IsMut, Box<Ty>),
  Func(Vec<(RefStr, Ty)>, bool, Box<Ty>),
  Arr(usize, Box<Ty>),
  Unit,
  Tuple(Vec<(RefStr, Ty)>),
  // Type variable
  Var(usize)
}

impl Ty {
  pub fn unwrap_func(&self) -> (&Vec<(RefStr, Ty)>, bool, &Ty) {
    if let Ty::Func(params, varargs, ret_ty) = self {
      (params, *varargs, ret_ty)
    } else {
      unreachable!()
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
      StructRef(name, type_args) |
      UnionRef(name, type_args) |
      EnumRef(name, type_args) => {
        write!(f, "{}", name)?;
        if type_args.1.len() > 0 {
          write_comma_separated(f, type_args.1.iter(), |f, ty| ty.fmt(f))
        } else {
          Ok(())
        }
      },
      Ptr(is_mut, ty) => write!(f, "*{}{:?}", is_mut, ty),
      Func(params, _va, ty) => {
        write!(f, "Function")?;
        write_comma_separated(f,
                              params.iter(), |f, (name, ty)| write!(f, "{}: {:?}", name, ty))?;
        write!(f, " -> {:?}", ty)
      }
      Arr(cnt, ty) => write!(f, "[{}]{:?}", cnt, ty),
      Unit => {
        write!(f, "()")
      }
      Tuple(params) => {
        write_comma_separated(f,
                              params.iter(), |f, (name, ty)| write!(f, "{}: {:?}", name, ty))
      }
      Var(idx) => write!(f, "'{}", idx)
    }
  }
}

/// Expressions
#[derive(Debug)]
pub enum LValue {
  DataRef { ty: Ty, is_mut: IsMut, id: DefId },
  ParamRef { ty: Ty, is_mut: IsMut, local_id: LocalId },
  LetRef { ty: Ty, is_mut: IsMut, local_id: LocalId },
  BindingRef { ty: Ty, is_mut: IsMut, local_id: LocalId },
  StrLit { ty: Ty, is_mut: IsMut, val: Vec<u8> },
  TupleLit { ty: Ty, is_mut: IsMut, fields: Vec<RValue> },
  ArrayLit { ty: Ty, is_mut: IsMut, elements: Vec<RValue> },
  StructLit { ty: Ty, is_mut: IsMut, fields: Vec<RValue> },
  UnionLit { ty: Ty, is_mut: IsMut, field: RValue },
  UnitVariantLit { ty: Ty, is_mut: IsMut, id: (DefId, Vec<Ty>) },
  StructVariantLit { ty: Ty, is_mut: IsMut, id: (DefId, Vec<Ty>), fields: Vec<RValue> },
  StruDot { ty: Ty, is_mut: IsMut, arg: Box<LValue>, idx: usize },
  UnionDot { ty: Ty, is_mut: IsMut, arg: Box<LValue> },
  Index { ty: Ty, is_mut: IsMut, arg: Box<LValue>, idx: Box<RValue> },
  Ind { ty: Ty, is_mut: IsMut, arg: Box<RValue> },
}

#[derive(Debug)]
pub enum RValue {
  Unit { ty: Ty },
  FuncRef { ty: Ty, id: (DefId, Vec<Ty>) },
  CStr { ty: Ty, val: Vec<u8> },
  Load { ty: Ty, arg: Box<LValue> },
  Nil { ty: Ty },
  Bool { ty: Ty, val: bool },
  Int { ty: Ty, val: usize },
  Flt { ty: Ty, val: f64 },
  Call { ty: Ty, func: Box<RValue>, args: Vec<RValue> },
  Adr { ty: Ty, arg: Box<LValue> },
  Un { ty: Ty, op: UnOp, arg: Box<RValue> },
  LNot { ty: Ty, arg: Box<RValue> },
  Cast { ty: Ty, arg: Box<RValue> },
  Bin { ty: Ty, op: BinOp, lhs: Box<RValue>, rhs: Box<RValue> },
  LAnd { ty: Ty, lhs: Box<RValue>, rhs: Box<RValue> },
  LOr { ty: Ty, lhs: Box<RValue>, rhs: Box<RValue> },
  Block { ty: Ty, body: Vec<RValue> },
  As { ty: Ty, lhs: Box<LValue>, rhs: Box<RValue> },
  Rmw { ty: Ty, op: BinOp, lhs: Box<LValue>, rhs: Box<RValue> },
  Continue { ty: Ty },
  Break { ty: Ty, arg: Box<RValue> },
  Return { ty: Ty, arg: Box<RValue> },
  Let { ty: Ty, local_id: LocalId, init: Option<Box<RValue>> },
  If { ty: Ty, cond: Box<RValue>, tbody: Box<RValue>, ebody: Box<RValue> },
  While { ty: Ty, cond: Box<RValue>, body: Box<RValue> },
  Loop { ty: Ty, body: Box<RValue> },
  Match { ty: Ty, cond: Box<RValue>, cases: Vec<((DefId, Vec<Ty>), Vec<LocalId>, RValue)>, any: Option<Box<RValue>> }
}

impl LValue {
  pub fn ty(&self) -> &Ty {
    match self {
      LValue::DataRef { ty, .. } => ty,
      LValue::ParamRef { ty, .. } => ty,
      LValue::LetRef { ty, .. } => ty,
      LValue::BindingRef { ty, .. } => ty,
      LValue::StrLit { ty, .. } => ty,
      LValue::TupleLit { ty, .. } => ty,
      LValue::ArrayLit { ty, .. } => ty,
      LValue::StructLit { ty, .. } => ty,
      LValue::UnionLit { ty, .. } => ty,
      LValue::UnitVariantLit { ty, .. } => ty,
      LValue::StructVariantLit { ty, .. } => ty,
      LValue::StruDot { ty, .. } => ty,
      LValue::UnionDot { ty, .. } => ty,
      LValue::Index { ty, .. } => ty,
      LValue::Ind { ty, .. } => ty,
    }
  }

  pub fn is_mut(&self) -> IsMut {
    match self {
      LValue::DataRef { is_mut, .. } => *is_mut,
      LValue::ParamRef { is_mut, .. } => *is_mut,
      LValue::LetRef { is_mut, .. } => *is_mut,
      LValue::BindingRef { is_mut, .. } => *is_mut,
      LValue::StrLit { is_mut, .. } => *is_mut,
      LValue::TupleLit { is_mut, .. } => *is_mut,
      LValue::ArrayLit { is_mut, .. } => *is_mut,
      LValue::StructLit { is_mut, .. } => *is_mut,
      LValue::UnionLit { is_mut, .. } => *is_mut,
      LValue::UnitVariantLit { is_mut, .. } => *is_mut,
      LValue::StructVariantLit { is_mut, .. } => *is_mut,
      LValue::StruDot { is_mut, .. } => *is_mut,
      LValue::UnionDot { is_mut, .. } => *is_mut,
      LValue::Index { is_mut, .. } => *is_mut,
      LValue::Ind { is_mut, .. } => *is_mut,
    }
  }
}

impl RValue {
  pub fn ty(&self) -> &Ty {
    match self {
      RValue::Unit { ty, .. } => ty,
      RValue::FuncRef { ty, .. } => ty,
      RValue::CStr { ty, .. } => ty,
      RValue::Load { ty, .. } => ty,
      RValue::Nil { ty, .. } => ty,
      RValue::Bool { ty, .. } => ty,
      RValue::Int { ty, .. } => ty,
      RValue::Flt { ty, .. } => ty,
      RValue::Call { ty, .. } => ty,
      RValue::Adr { ty, .. } => ty,
      RValue::Un { ty, .. } => ty,
      RValue::LNot { ty, .. } => ty,
      RValue::Cast { ty, .. } => ty,
      RValue::Bin { ty, .. } => ty,
      RValue::LAnd { ty, .. } => ty,
      RValue::LOr { ty, .. } => ty,
      RValue::Block { ty, .. } => ty,
      RValue::As { ty, .. } => ty,
      RValue::Rmw { ty, .. } => ty,
      RValue::Continue { ty, .. } => ty,
      RValue::Break { ty, .. } => ty,
      RValue::Return { ty, .. } => ty,
      RValue::Let { ty, .. } => ty,
      RValue::If { ty, .. } => ty,
      RValue::While { ty, .. } => ty,
      RValue::Loop { ty, .. } => ty,
      RValue::Match { ty, .. } => ty,
    }
  }
}

