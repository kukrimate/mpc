/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use super::*;

#[derive(Debug)]
pub enum ResolvedTy {
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
  TParam(usize),
  AliasRef(DefId, Vec<ResolvedTy>),
  StructRef(DefId, Vec<ResolvedTy>),
  UnionRef(DefId, Vec<ResolvedTy>),
  EnumRef(DefId, Vec<ResolvedTy>),
  Ptr(IsMut, Box<ResolvedTy>),
  Func(Vec<(RefStr, ResolvedTy)>, Box<ResolvedTy>),
  Arr(Box<ResolvedExpr>, Box<ResolvedTy>),
  Unit,
  Tuple(Vec<(RefStr, ResolvedTy)>),
}


#[derive(Debug)]
pub enum ResolvedExpr {
  // Literals
  Nil,
  Bool(bool),
  Int(usize),
  Flt(f64),
  Str(Vec<u8>),
  CStr(Vec<u8>),
  Unit,
  TupleLit(Vec<(RefStr, ResolvedExpr)>),
  ArrayLit(Vec<ResolvedExpr>),
  StructLit(DefId, Vec<(RefStr, ResolvedExpr)>),
  UnionLit(DefId, RefStr, Box<ResolvedExpr>),
  UnitVariantLit(DefId, usize),
  StructVariantLit(DefId, usize, Vec<(RefStr, ResolvedExpr)>),

  // References
  FuncRef(DefId),
  ExternFuncRef(DefId),
  ConstRef(DefId),
  DataRef(DefId),
  ExternDataRef(DefId),
  ParamRef(usize),
  LetRef(usize),
  BindingRef(usize),

  // Compound expressions
  Dot(Box<ResolvedExpr>, RefStr),
  Call(Box<ResolvedExpr>, Vec<(RefStr, ResolvedExpr)>),
  Index(Box<ResolvedExpr>, Box<ResolvedExpr>),
  Adr(Box<ResolvedExpr>),
  Ind(Box<ResolvedExpr>),
  Un(UnOp, Box<ResolvedExpr>),
  LNot(Box<ResolvedExpr>),
  Cast(Box<ResolvedExpr>, ResolvedTy),
  Bin(BinOp, Box<ResolvedExpr>, Box<ResolvedExpr>),
  LAnd(Box<ResolvedExpr>, Box<ResolvedExpr>),
  LOr(Box<ResolvedExpr>, Box<ResolvedExpr>),
  Block(Vec<ResolvedExpr>),
  As(Box<ResolvedExpr>, Box<ResolvedExpr>),
  Rmw(BinOp, Box<ResolvedExpr>, Box<ResolvedExpr>),
  Continue,
  Break(Box<ResolvedExpr>),
  Return(Box<ResolvedExpr>),
  Let(usize, Option<Box<ResolvedExpr>>),
  If(Box<ResolvedExpr>, Box<ResolvedExpr>, Box<ResolvedExpr>),
  While(Box<ResolvedExpr>, Box<ResolvedExpr>),
  Loop(Box<ResolvedExpr>),
  Match(Box<ResolvedExpr>, Vec<(Option<usize>, RefStr, ResolvedExpr)>)
}

#[derive(Debug)]
pub enum ResolvedDef {
  Type(ResolvedTypeDef),
  Struct(ResolvedStructDef),
  Union(ResolvedUnionDef),
  Enum(ResolvedEnumDef),
  Const(ResolvedConstDef),
  Data(ResolvedDataDef),
  Func(ResolvedFuncDef),
  ExternData(ResolvedExternDataDef),
  ExternFunc(ResolvedExternFuncDef),
}

impl ResolvedDef {
  pub fn unwrap_type(&self) -> &ResolvedTypeDef {
    if let ResolvedDef::Type(def) = self { def } else { unreachable!( ) }
  }

  pub fn unwrap_struct(&self) -> &ResolvedStructDef {
    if let ResolvedDef::Struct(def) = self { def } else { unreachable!( ) }
  }

  pub fn unwrap_union(&self) -> &ResolvedUnionDef {
    if let ResolvedDef::Union(def) = self { def } else { unreachable!( ) }
  }

  pub fn unwrap_enum(&self) -> &ResolvedEnumDef {
    if let ResolvedDef::Enum(def) = self { def } else { unreachable!( ) }
  }

  pub fn unwrap_const(&self) -> &ResolvedConstDef {
    if let ResolvedDef::Const(def) = self { def } else { unreachable!( ) }
  }

  pub fn unwrap_data(&self) -> &ResolvedDataDef {
    if let ResolvedDef::Data(def) = self { def } else { unreachable!( ) }
  }

  pub fn unwrap_func(&self) -> &ResolvedFuncDef {
    if let ResolvedDef::Func(def) = self { def } else { unreachable!( ) }
  }

  pub fn unwrap_extern_data(&self) -> &ResolvedExternDataDef {
    if let ResolvedDef::ExternData(def) = self { def } else { unreachable!( ) }
  }

  pub fn unwrap_extern_func(&self) -> &ResolvedExternFuncDef {
    if let ResolvedDef::ExternFunc(def) = self { def } else { unreachable!( ) }
  }
}

#[derive(Debug)]
pub struct ResolvedTypeDef {
  pub name: RefStr,
  pub ty: ResolvedTy,
}

#[derive(Debug)]
pub struct ResolvedStructDef {
  pub name: RefStr,
  pub type_params: usize,
  pub params: Vec<(RefStr, ResolvedTy)>,
}

#[derive(Debug)]
pub struct ResolvedUnionDef {
  pub name: RefStr,
  pub type_params: usize,
  pub params: Vec<(RefStr, ResolvedTy)>,
}

#[derive(Debug)]
pub struct ResolvedEnumDef {
  pub name: RefStr,
  pub type_params: usize,
  pub variants: Vec<ResolvedVariant>,
}

#[derive(Debug)]
pub enum ResolvedVariant {
  Unit(RefStr),
  Struct(RefStr, Vec<(RefStr, ResolvedTy)>),
}

#[derive(Debug)]
pub struct ResolvedConstDef {
  pub name: RefStr,
  pub ty: ResolvedTy,
  pub val: ResolvedExpr,
}

#[derive(Debug)]
pub struct ResolvedDataDef {
  pub name: RefStr,
  pub is_mut: IsMut,
  pub ty: ResolvedTy,
  pub init: ResolvedExpr,
}

#[derive(Debug)]
pub struct ResolvedFuncDef {
  pub name: RefStr,
  pub type_params: usize,
  pub params: Vec<(RefStr, IsMut, ResolvedTy)>,
  pub ret_ty: ResolvedTy,
  pub locals: Vec<(IsMut, Option<ResolvedTy>)>,
  pub body: ResolvedExpr,
}

#[derive(Debug)]
pub struct ResolvedExternDataDef {
  pub name: RefStr,
  pub is_mut: IsMut,
  pub ty: ResolvedTy,
}

#[derive(Debug)]
pub struct ResolvedExternFuncDef {
  pub name: RefStr,
  pub params: Vec<(RefStr, ResolvedTy)>,
  pub varargs: bool,
  pub ret_ty: ResolvedTy,
}
