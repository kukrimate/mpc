/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use crate::{CompileError, SourceLocation};
use super::*;

#[derive(Debug)]
pub enum ConstPtr {
  Data { ty: Ty, id: DefId },
  StrLit { ty: Ty, val: Vec<u8> },
  ArrayElement { ty: Ty, base: Box<ConstPtr>, idx: usize },
  StructField { ty: Ty, base: Box<ConstPtr>, idx: usize },
  UnionField { ty: Ty, base: Box<ConstPtr> }
}

impl ConstPtr {
  pub fn ty(&self) -> &Ty {
    match self {
      ConstPtr::Data { ty, .. } => ty,
      ConstPtr::StrLit { ty, .. } => ty,
      ConstPtr::ArrayElement { ty, .. } => ty,
      ConstPtr::StructField { ty, .. } => ty,
      ConstPtr::UnionField { ty, .. } => ty
    }
  }
}

#[derive(Debug)]
pub enum ConstVal {
  Nil { ty: Ty },
  FuncPtr { id: (DefId, Vec<Ty>) },
  DataPtr { ptr: ConstPtr },
  BoolLit { val: bool },
  IntLit { ty: Ty, val: isize },
  FltLit { ty: Ty, val: f64 },
  ArrLit { ty: Ty, vals: Vec<ConstVal> },
  StructLit { ty: Ty, vals: Vec<ConstVal> },
  UnionLit { ty: Ty, val: Box<ConstVal> },
  CStrLit { val: Vec<u8> },
}

fn eval_constptr(loc: SourceLocation, lvalue: &LValue) -> Result<ConstPtr, CompileError> {
  use ConstPtr::*;
  match lvalue {
    LValue::DataRef { ty, id, .. } => {
      Ok(Data {
        ty: ty.clone(),
        id: *id
      })
    }
    LValue::StrLit { ty, val, .. } => {
      Ok(StrLit {
        ty: ty.clone(),
        val: val.clone()
      })
    }
    LValue::StruDot { ty, arg, idx, .. } => {
      let base = eval_constptr(loc, &*arg)?;
      Ok(StructField {
        ty: ty.clone(),
        base: Box::new(base),
        idx: *idx
      })
    }
    LValue::UnionDot { ty, arg, .. } => {
      let base = eval_constptr(loc, &*arg)?;
      Ok(UnionField {
        ty: ty.clone(),
        base: Box::new(base)
      })
    }
    LValue::Index { ty, arg, idx, .. } => {
      let base = eval_constptr(loc.clone(), &*arg)?;
      let index = consteval_index(loc, idx)?;
      Ok(ArrayElement {
        ty: ty.clone(),
        base: Box::new(base),
        idx: index
      })
    }
    _ => {
      Err(CompileError::InvalidConstantExpression(loc))
    }
  }
}

pub(super) fn eval_constload(loc: SourceLocation, lvalue: &LValue) -> Result<ConstVal, CompileError> {
  match lvalue {
    LValue::ArrayLit { ty, elements, .. } => {
      let vals = elements
        .iter()
        .map(|element| consteval(loc.clone(), element))
        .monadic_collect()?;
      Ok(ConstVal::ArrLit { ty: ty.clone(), vals })
    }
    LValue::TupleLit { ty, fields, .. } |
    LValue::StructLit { ty, fields, .. } => {
      let vals = fields
        .iter()
        .map(|field| consteval(loc.clone(), field))
        .monadic_collect()?;
      Ok(ConstVal::StructLit { ty: ty.clone(), vals })
    }
    LValue::UnionLit { ty, field: val, .. } => {
      Ok(ConstVal::UnionLit { ty: ty.clone(), val: Box::new(consteval(loc, val)?) })
    }
    LValue::StruDot { arg, idx, .. } => {
      let base = eval_constload(loc.clone(), arg)?;
      match base {
        ConstVal::StructLit { vals, .. } => {
          Ok(vals.into_iter().nth(*idx).unwrap())
        }
        _ => Err(CompileError::InvalidConstantExpression(loc))
      }
    }
    LValue::UnionDot { arg, .. } => {
      let base = eval_constload(loc.clone(),arg)?;
      match base {
        ConstVal::UnionLit { .. } => {
          todo!()
        }
        _ => Err(CompileError::InvalidConstantExpression(loc))
      }
    }
    LValue::Index { arg, idx, .. } => {
      let base = eval_constload(loc.clone(), arg)?;
      let index = consteval_index(loc.clone(), idx)?;
      match base {
        ConstVal::ArrLit { vals, .. } if index < vals.len() => {
          Ok(vals.into_iter().nth(index).unwrap())
        }
        _ => Err(CompileError::InvalidConstantExpression(loc))
      }
    }
    _ => {
      Err(CompileError::InvalidConstantExpression(loc))
    }
  }
}

pub(super) fn consteval(loc: SourceLocation, rvalue: &RValue) -> Result<ConstVal, CompileError> {
  use UnOp::*;
  use BinOp::*;
  use ConstVal::*;

  match rvalue {
    RValue::Load { arg, .. } => {
      eval_constload(loc, arg)
    }
    RValue::FuncRef { id, .. } => {
      Ok(FuncPtr { id: id.clone() })
    }
    RValue::Nil { ty, .. } => {
      Ok(Nil { ty: ty.clone() })
    }
    RValue::CStr { val, .. } => {
      Ok(CStrLit { val: val.clone() })
    }
    RValue::Bool { val, .. } => {
      Ok(BoolLit { val: *val })
    }
    RValue::Int { ty, val, .. } => {
      Ok(IntLit { ty: ty.clone(), val: *val as isize })
    }
    RValue::Flt { ty, val, .. } => {
      Ok(FltLit { ty: ty.clone(), val: *val })
    }
    RValue::Adr { arg, .. } => {
      Ok(DataPtr { ptr: eval_constptr(loc, arg)? })
    }
    RValue::Un { op, arg, .. } => {
      match (op, consteval(loc.clone(), arg)?) {
        (UPlus, IntLit { ty, val, .. }) => Ok(IntLit { ty, val }),
        (UPlus, FltLit { ty, val, .. }) => Ok(FltLit { ty, val }),
        (UMinus, IntLit { ty, val, .. }) => Ok(IntLit { ty, val: -val }),
        (UMinus, FltLit { ty, val, .. }) => Ok(FltLit { ty, val: -val }),
        (Not, BoolLit { val }) => Ok(BoolLit { val: !val }),
        _ => Err(CompileError::InvalidConstantExpression(loc))
      }
    }
    RValue::LNot { arg, .. } => {
      match consteval(loc.clone(), arg)? {
        BoolLit { val } => Ok(BoolLit { val: !val }),
        _ => Err(CompileError::InvalidConstantExpression(loc))
      }
    }
    RValue::Bin { op, lhs, rhs, .. } => {
      match (op, consteval(loc.clone(), lhs)?, consteval(loc.clone(), rhs)?) {
        (Mul, IntLit { ty, val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(IntLit { ty, val: lhs * rhs }),
        (Div, IntLit { ty, val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(IntLit { ty, val: lhs / rhs }),
        (Mod, IntLit { ty, val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(IntLit { ty, val: lhs % rhs }),
        (Add, IntLit { ty, val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(IntLit { ty, val: lhs + rhs }),
        (Sub, IntLit { ty, val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(IntLit { ty, val: lhs - rhs }),
        (Lsh, IntLit { ty, val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(IntLit { ty, val: lhs << rhs }),
        (Rsh, IntLit { ty, val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(IntLit { ty, val: lhs >> rhs }),
        (And, IntLit { ty, val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(IntLit { ty, val: lhs & rhs }),
        (Xor, IntLit { ty, val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(IntLit { ty, val: lhs ^ rhs }),
        (Or, IntLit { ty, val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(IntLit { ty, val: lhs | rhs }),
        (Eq, IntLit { val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(BoolLit { val: lhs == rhs }),
        (Ne, IntLit { val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(BoolLit { val: lhs != rhs }),
        (Lt, IntLit { val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(BoolLit { val: lhs < rhs }),
        (Gt, IntLit { val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(BoolLit { val: lhs > rhs }),
        (Le, IntLit { val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(BoolLit { val: lhs <= rhs }),
        (Ge, IntLit { val: lhs, .. }, IntLit { val: rhs, .. }) => Ok(BoolLit { val: lhs >= rhs }),
        (Mul, FltLit { ty, val: lhs, .. }, FltLit { val: rhs, .. }) => Ok(FltLit { ty, val: lhs * rhs }),
        (Div, FltLit { ty, val: lhs, .. }, FltLit { val: rhs, .. }) => Ok(FltLit { ty, val: lhs / rhs }),
        (Add, FltLit { ty, val: lhs, .. }, FltLit { val: rhs, .. }) => Ok(FltLit { ty, val: lhs + rhs }),
        (Sub, FltLit { ty, val: lhs, .. }, FltLit { val: rhs, .. }) => Ok(FltLit { ty, val: lhs - rhs }),
        (Eq, FltLit { val: lhs, .. }, FltLit { val: rhs, .. }) => Ok(BoolLit { val: lhs == rhs }),
        (Ne, FltLit { val: lhs, .. }, FltLit { val: rhs, .. }) => Ok(BoolLit { val: lhs != rhs }),
        (Lt, FltLit { val: lhs, .. }, FltLit { val: rhs, .. }) => Ok(BoolLit { val: lhs < rhs }),
        (Gt, FltLit { val: lhs, .. }, FltLit { val: rhs, .. }) => Ok(BoolLit { val: lhs > rhs }),
        (Le, FltLit { val: lhs, .. }, FltLit { val: rhs, .. }) => Ok(BoolLit { val: lhs <= rhs }),
        (Ge, FltLit { val: lhs, .. }, FltLit { val: rhs, .. }) => Ok(BoolLit { val: lhs >= rhs }),
        _ => Err(CompileError::InvalidConstantExpression(loc))
      }
    }
    RValue::LAnd { lhs, rhs, .. } => {
      match consteval(loc.clone(), lhs)? {
        BoolLit { val: true } => Ok(BoolLit { val: true }),
        BoolLit { val: false } => consteval(loc.clone(), rhs),
        _ => Err(CompileError::InvalidConstantExpression(loc))
      }
    }
    RValue::LOr { lhs, rhs, .. } => {
      match consteval(loc.clone(), lhs)? {
        BoolLit { val: true } => consteval(loc.clone(), rhs),
        BoolLit { val: false } => Ok(BoolLit { val: false }),
        _ => Err(CompileError::InvalidConstantExpression(loc))
      }
    }
    RValue::If { cond, tbody, ebody, .. } => {
      match consteval(loc.clone(), cond)? {
        BoolLit { val: true } => consteval(loc.clone(), tbody),
        BoolLit { val: false } => consteval(loc.clone(), ebody),
        _ => Err(CompileError::InvalidConstantExpression(loc))
      }
    }
    _ => {
      Err(CompileError::InvalidConstantExpression(loc))
    }
  }
}

pub(super) fn consteval_index(loc: SourceLocation, rvalue: &RValue) -> Result<usize, CompileError> {
  match consteval(loc.clone(), rvalue)? {
    ConstVal::IntLit { val, .. } if val >= 0 => Ok(val as usize),
    _ => Err(CompileError::InvalidConstantExpression(loc)),
  }
}
