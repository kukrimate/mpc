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

use crate::*;
use crate::parse::{self,IsMut,UnOp,BinOp,DefId};
use crate::util::*;
use std::collections::HashMap;
use std::error;
use std::fmt;

mod tctx;
mod consteval;

use tctx::*;
use consteval::*;

/// Definitions

#[derive(Debug)]
enum Inst {
  Struct      { name: RefStr, params: Option<Vec<(RefStr, Ty)>> },
  Union       { name: RefStr, params: Option<Vec<(RefStr, Ty)>> },
  Enum        { name: RefStr, variants: Option<Vec<(RefStr, Variant)>> },
  Func        { name: RefStr, ty: Ty, locals: HashMap<LocalId, LocalDef>, body: Option<RValue> },
  Data        { name: RefStr, ty: Ty, is_mut: IsMut, init: ConstVal },
  ExternFunc  { name: RefStr, ty: Ty },
  ExternData  { name: RefStr, ty: Ty, is_mut: IsMut },
}

#[derive(Debug)]
enum Variant {
  Unit(RefStr),
  Struct(RefStr, Vec<(RefStr, Ty)>),
}

/// Local definition

#[derive(Clone,Copy, PartialEq, Eq, Hash)]
pub struct LocalId(usize);

impl fmt::Debug for LocalId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}

#[derive(Debug)]
enum LocalDef {
  Param {
    name: RefStr,
    ty: Ty,
    is_mut: IsMut,
    index: usize
  },
  Let {
    name: RefStr,
    ty: Ty,
    is_mut: IsMut
  }
}

impl LocalDef {
  fn name(&self) -> RefStr {
    match self {
      LocalDef::Param { name, .. } => *name,
      LocalDef::Let { name, .. } => *name
    }
  }
}

/// Types

#[derive(Clone,PartialEq,Eq,Hash)]
enum Ty {
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
  Inst(RefStr, (DefId, Vec<Ty>)),
  Ptr(IsMut, Box<Ty>),
  Func(Vec<(RefStr, Ty)>, bool, Box<Ty>),
  Arr(usize, Box<Ty>),
  Tuple(Vec<(RefStr, Ty)>),
  // Type variables
  TVar(usize),
  // Type bounds
  BoundAny,
  BoundNum,
  BoundInt,
  BoundFlt,
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
      Inst(name, ..) => write!(f, "{}", name),
      Ptr(is_mut, ty) => write!(f, "*{}{:?}", is_mut, ty),
      Func(params, _va, ty) => {
        write!(f, "Function")?;
        write_comma_separated(f,
          params.iter(), |f, (name, ty)| write!(f, "{}: {:?}", name, ty))?;
        write!(f, " -> {:?}", ty)
      },
      Arr(cnt, ty) => write!(f, "[{}]{:?}", cnt, ty),
      Tuple(params) => {
        write_comma_separated(f,
          params.iter(), |f, (name, ty)| write!(f, "{}: {:?}", name, ty))
      }
      TVar(idx) => write!(f, "'{}", idx),
      BoundAny => write!(f, "Any"),
      BoundNum => write!(f, "Num"),
      BoundInt => write!(f, "Int"),
      BoundFlt => write!(f, "Flt"),
    }
  }
}

/// Expressions

#[derive(Debug)]
enum LValue {
  DataRef   { ty: Ty, is_mut: IsMut, id: DefId },
  ParamRef  { ty: Ty, is_mut: IsMut, id: LocalId },
  LetRef    { ty: Ty, is_mut: IsMut, id: LocalId },
  StrLit    { ty: Ty, is_mut: IsMut, val: Vec<u8> },
  ArrayLit  { ty: Ty, is_mut: IsMut, elements: Vec<RValue> },
  StructLit { ty: Ty, is_mut: IsMut, name: RefStr, fields: Vec<RValue> },
  StruDot   { ty: Ty, is_mut: IsMut, arg: Box<LValue>, name: RefStr, idx: usize },
  UnionDot  { ty: Ty, is_mut: IsMut, arg: Box<LValue>, name: RefStr },
  Index     { ty: Ty, is_mut: IsMut, arg: Box<LValue>, idx: Box<RValue> },
  Ind       { ty: Ty, is_mut: IsMut, arg: Box<RValue> },
}

#[derive(Debug)]
enum RValue {
  Null      { ty: Ty },
  FuncRef   { ty: Ty, id: (DefId, Vec<Ty>) },
  CStr      { ty: Ty, val: Vec<u8> },
  Load      { ty: Ty, arg: Box<LValue> },
  Bool      { ty: Ty, val: bool },
  Int       { ty: Ty, val: usize },
  Flt       { ty: Ty, val: f64 },
  Call      { ty: Ty, arg: Box<RValue>, args: Vec<RValue> },
  Adr       { ty: Ty, arg: Box<LValue> },
  Un        { ty: Ty, op: UnOp, arg: Box<RValue> },
  LNot      { ty: Ty, arg: Box<RValue> },
  Cast      { ty: Ty, arg: Box<RValue> },
  Bin       { ty: Ty, op: BinOp, lhs: Box<RValue>, rhs: Box<RValue> },
  LAnd      { ty: Ty, lhs: Box<RValue>, rhs: Box<RValue> },
  LOr       { ty: Ty, lhs: Box<RValue>, rhs: Box<RValue> },
  Block     { ty: Ty, body: Vec<RValue> },
  As        { ty: Ty, lhs: Box<LValue>, rhs: Box<RValue> },
  Rmw       { ty: Ty, op: BinOp, lhs: Box<LValue>, rhs: Box<RValue> },
  Continue  { ty: Ty },
  Break     { ty: Ty, arg: Box<RValue> },
  Return    { ty: Ty, arg: Box<RValue> },
  Let       { ty: Ty, id: LocalId, init: Option<Box<RValue>> },
  If        { ty: Ty, cond: Box<RValue>, tbody: Box<RValue>, ebody: Box<RValue> },
  While     { ty: Ty, cond: Box<RValue>, body: Box<RValue> },
  Loop      { ty: Ty, body: Box<RValue> },
}

impl LValue {
  fn ty(&self) -> &Ty {
    match self {
      LValue::DataRef   { ty, .. } => ty,
      LValue::ParamRef  { ty, .. } => ty,
      LValue::LetRef    { ty, .. } => ty,
      LValue::StrLit    { ty, .. } => ty,
      LValue::ArrayLit  { ty, .. } => ty,
      LValue::StructLit { ty, .. } => ty,
      LValue::StruDot   { ty, .. } => ty,
      LValue::UnionDot  { ty, .. } => ty,
      LValue::Index     { ty, .. } => ty,
      LValue::Ind       { ty, .. } => ty,
    }
  }

  fn is_mut(&self) -> IsMut {
    match self {
      LValue::DataRef   { is_mut, .. }  => *is_mut,
      LValue::ParamRef  { is_mut, .. }  => *is_mut,
      LValue::LetRef    { is_mut, .. }  => *is_mut,
      LValue::StrLit    { is_mut, .. }  => *is_mut,
      LValue::ArrayLit  { is_mut, .. }  => *is_mut,
      LValue::StructLit { is_mut, .. }  => *is_mut,
      LValue::StruDot   { is_mut, .. }  => *is_mut,
      LValue::UnionDot  { is_mut, .. }  => *is_mut,
      LValue::Index     { is_mut, .. }  => *is_mut,
      LValue::Ind       { is_mut, .. }  => *is_mut,
    }
  }
}

impl RValue {
  fn ty(&self) -> &Ty {
    match self {
      RValue::Null      { ty, .. } => ty,
      RValue::FuncRef   { ty, .. } => ty,
      RValue::CStr      { ty, .. } => ty,
      RValue::Load      { ty, .. } => ty,
      RValue::Bool      { ty, .. } => ty,
      RValue::Int       { ty, .. } => ty,
      RValue::Flt       { ty, .. } => ty,
      RValue::Call      { ty, .. } => ty,
      RValue::Adr       { ty, .. } => ty,
      RValue::Un        { ty, .. } => ty,
      RValue::LNot      { ty, .. } => ty,
      RValue::Cast      { ty, .. } => ty,
      RValue::Bin       { ty, .. } => ty,
      RValue::LAnd      { ty, .. } => ty,
      RValue::LOr       { ty, .. } => ty,
      RValue::Block     { ty, .. } => ty,
      RValue::As        { ty, .. } => ty,
      RValue::Rmw       { ty, .. } => ty,
      RValue::Continue  { ty, .. } => ty,
      RValue::Break     { ty, .. } => ty,
      RValue::Return    { ty, .. } => ty,
      RValue::Let       { ty, .. } => ty,
      RValue::If        { ty, .. } => ty,
      RValue::While     { ty, .. } => ty,
      RValue::Loop      { ty, .. } => ty,
    }
  }
}

/// Type checker and lowerer live in their own files

mod infer;
mod lower;

pub fn compile(repo: &parse::Repository, output_path: &Path, compile_to: CompileTo) -> MRes<()> {
  let mut tctx = TVarCtx::new();
  let insts = infer::infer(repo, &mut tctx)?;
  if let Some(_) = option_env!("MPC_SPEW") {
    eprintln!("{:#?}", insts);
    eprintln!("{:#?}", tctx);
  }
  lower::lower_module(&mut tctx, &insts, output_path, compile_to)?;
  Ok(())
}
