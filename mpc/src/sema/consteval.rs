/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use std::fmt::Formatter;
use super::*;

#[derive(Debug)]
pub(super) enum ConstPtr {
  Data(DefId),
  StrLit(Vec<u8>),
  ArrayElement(Box<ConstPtr>, usize),
  StructField(Box<ConstPtr>, usize)
}

#[derive(Debug)]
pub(super) enum ConstVal {
  FuncPtr { id: (DefId, Vec<Ty>) },
  DataPtr { ptr: ConstPtr },
  BoolLit { val: bool },
  IntLit { ty: Ty, val: isize },
  FltLit { ty: Ty, val: f64 },
  ArrLit { ty: Ty, vals: Vec<ConstVal> },
  StructLit { ty: Ty, vals: Vec<ConstVal> },
  CStrLit { val: Vec<u8> }
}

#[derive(Debug)]
struct InvalidConstantExpressionError;

impl fmt::Display for InvalidConstantExpressionError {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "Invalid constant expression")
  }
}

impl error::Error for InvalidConstantExpressionError {}

fn eval_constptr(lvalue: &LValue) -> MRes<ConstPtr> {
  use ConstPtr::*;
  match lvalue {
    LValue::DataRef { id, .. } => {
      Ok(Data(*id))
    }
    LValue::StrLit { val, .. } => {
      Ok(StrLit(val.clone()))
    }
    LValue::StruDot { arg, idx, .. } => {
      let base = eval_constptr(&*arg)?;
      Ok(StructField(Box::new(base), *idx))
    }
    LValue::Index { arg, idx, .. } => {
      let base = eval_constptr(&*arg)?;
      let index = consteval_index(idx)?;
      Ok(ArrayElement(Box::new(base), index))
    }
    _ => {
      Err(Box::new(InvalidConstantExpressionError))
    }
  }
}

pub(super) fn eval_constload(lvalue: &LValue) -> MRes<ConstVal> {
  match lvalue {
    LValue::ArrayLit { ty, elements, .. } => {
      let vals = elements
        .iter()
        .map(|element| consteval(element))
        .monadic_collect()?;
      Ok(ConstVal::ArrLit { ty: ty.clone(), vals })
    }
    LValue::StructLit { ty, fields, .. } => {
      let vals = fields
        .iter()
        .map(|field| consteval(field))
        .monadic_collect()?;
      Ok(ConstVal::StructLit { ty: ty.clone(), vals })
    }
    LValue::StruDot { arg, idx, .. } => {
      let base = eval_constload(arg)?;
      match base {
        ConstVal::StructLit { vals, .. } => {
          Ok(vals.into_iter().nth(*idx).unwrap())
        }
        _ => Err(Box::new(InvalidConstantExpressionError))
      }
    }
    LValue::Index { arg, idx, .. } => {
      let base = eval_constload(arg)?;
      let index = consteval_index(idx)?;
      match base {
        ConstVal::ArrLit { vals, .. } if index < vals.len() => {
          Ok(vals.into_iter().nth(index).unwrap())
        }
        _ => Err(Box::new(InvalidConstantExpressionError))
      }
    }
    _ => {
      Err(Box::new(InvalidConstantExpressionError))
    }
  }
}

pub(super) fn consteval(rvalue: &RValue) -> MRes<ConstVal> {
  use UnOp::*;
  use BinOp::*;
  use ConstVal::*;

  match rvalue {
    RValue::Load { arg, .. } => {
      eval_constload(arg)
    }
    RValue::FuncRef { id, .. } => {
      Ok(FuncPtr { id: id.clone() })
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
      Ok(DataPtr { ptr: eval_constptr(arg)? })
    }
    RValue::Un { op, arg, .. } => {
      match (op, consteval(arg)?) {
        (UPlus, IntLit { ty, val, .. }) => Ok(IntLit { ty, val }),
        (UPlus, FltLit { ty, val, .. }) => Ok(FltLit { ty, val }),
        (UMinus, IntLit { ty, val, .. }) => Ok(IntLit { ty, val: -val }),
        (UMinus, FltLit { ty, val, .. }) => Ok(FltLit { ty, val: -val }),
        (Not, BoolLit { val }) => Ok(BoolLit { val: !val }),
        _ => Err(Box::new(InvalidConstantExpressionError))
      }
    }
    RValue::LNot { arg, .. } => {
      match consteval(arg)? {
        BoolLit { val } => Ok(BoolLit { val: !val }),
        _ => Err(Box::new(InvalidConstantExpressionError))
      }
    }
    RValue::Bin { op, lhs, rhs, .. } => {
      match (op, consteval(lhs)?, consteval(rhs)?) {
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
        _ => Err(Box::new(InvalidConstantExpressionError))
      }
    }
    RValue::LAnd { lhs, rhs, .. } => {
      match consteval(lhs)? {
        BoolLit { val: true } => Ok(BoolLit { val: true }),
        BoolLit { val: false } => consteval(rhs),
        _ => Err(Box::new(InvalidConstantExpressionError))
      }
    }
    RValue::LOr { lhs, rhs, .. } => {
      match consteval(lhs)? {
        BoolLit { val: true } => consteval(rhs),
        BoolLit { val: false } => Ok(BoolLit { val: false }),
        _ => Err(Box::new(InvalidConstantExpressionError))
      }
    }
    RValue::If { cond, tbody, ebody, .. } => {
      match consteval(cond)? {
        BoolLit { val: true } => consteval(tbody),
        BoolLit { val: false } => consteval(ebody),
        _ => Err(Box::new(InvalidConstantExpressionError))
      }
    }
    _ => {
      Err(Box::new(InvalidConstantExpressionError))
    }
  }
}

pub(super) fn consteval_index(rvalue: &RValue) -> MRes<usize> {
  match consteval(rvalue)? {
    ConstVal::IntLit { val, .. } if val >= 0 => Ok(val as usize),
    _ => Err(Box::new(InvalidConstantExpressionError)),
  }
}