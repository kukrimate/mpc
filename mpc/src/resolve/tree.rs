/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use super::*;

#[derive(Debug)]
pub enum ResolvedTy {
  Bool(SourceLocation),
  Uint8(SourceLocation),
  Int8(SourceLocation),
  Uint16(SourceLocation),
  Int16(SourceLocation),
  Uint32(SourceLocation),
  Int32(SourceLocation),
  Uint64(SourceLocation),
  Int64(SourceLocation),
  Uintn(SourceLocation),
  Intn(SourceLocation),
  Float(SourceLocation),
  Double(SourceLocation),
  TParam(SourceLocation, usize),
  AliasRef(SourceLocation, DefId, Vec<ResolvedTy>),
  StructRef(SourceLocation, DefId, Vec<ResolvedTy>),
  UnionRef(SourceLocation, DefId, Vec<ResolvedTy>),
  EnumRef(SourceLocation, DefId, Vec<ResolvedTy>),
  Ptr(SourceLocation, IsMut, Box<ResolvedTy>),
  Func(SourceLocation, Vec<(RefStr, ResolvedTy)>, Box<ResolvedTy>),
  Arr(SourceLocation, Box<ResolvedExpr>, Box<ResolvedTy>),
  Unit(SourceLocation),
  Tuple(SourceLocation, Vec<(RefStr, ResolvedTy)>),
}


#[derive(Debug)]
pub enum ResolvedExpr {
  // Literals
  Nil(SourceLocation),
  Bool(SourceLocation, bool),
  Int(SourceLocation, usize),
  Flt(SourceLocation, f64),
  Str(SourceLocation, Vec<u8>),
  CStr(SourceLocation, Vec<u8>),
  Unit(SourceLocation),
  TupleLit(SourceLocation, Vec<(RefStr, ResolvedExpr)>),
  ArrayLit(SourceLocation, Vec<ResolvedExpr>),
  StructLit(SourceLocation, DefId, Vec<ResolvedTy>, Vec<(RefStr, ResolvedExpr)>),
  UnionLit(SourceLocation, DefId, Vec<ResolvedTy>, RefStr, Box<ResolvedExpr>),
  UnitVariantLit(SourceLocation, DefId, Vec<ResolvedTy>, usize),
  StructVariantLit(SourceLocation, DefId, Vec<ResolvedTy>, usize, Vec<(RefStr, ResolvedExpr)>),

  // References
  FuncRef(SourceLocation, DefId, Vec<ResolvedTy>),
  ExternFuncRef(SourceLocation, DefId),
  ConstRef(SourceLocation, DefId),
  DataRef(SourceLocation, DefId),
  ExternDataRef(SourceLocation, DefId),
  ParamRef(SourceLocation, usize),
  LetRef(SourceLocation, usize),
  BindingRef(SourceLocation, usize),

  // Compound expressions
  Dot(SourceLocation, Box<ResolvedExpr>, RefStr),
  Call(SourceLocation, Box<ResolvedExpr>, Vec<(RefStr, ResolvedExpr)>),
  Index(SourceLocation, Box<ResolvedExpr>, Box<ResolvedExpr>),
  Adr(SourceLocation, Box<ResolvedExpr>),
  Ind(SourceLocation, Box<ResolvedExpr>),
  Un(SourceLocation, UnOp, Box<ResolvedExpr>),
  LNot(SourceLocation, Box<ResolvedExpr>),
  Cast(SourceLocation, Box<ResolvedExpr>, ResolvedTy),
  Bin(SourceLocation, BinOp, Box<ResolvedExpr>, Box<ResolvedExpr>),
  LAnd(SourceLocation, Box<ResolvedExpr>, Box<ResolvedExpr>),
  LOr(SourceLocation, Box<ResolvedExpr>, Box<ResolvedExpr>),
  Block(SourceLocation, Vec<ResolvedExpr>),
  As(SourceLocation, Box<ResolvedExpr>, Box<ResolvedExpr>),
  Rmw(SourceLocation, BinOp, Box<ResolvedExpr>, Box<ResolvedExpr>),
  Continue(SourceLocation),
  Break(SourceLocation, Box<ResolvedExpr>),
  Return(SourceLocation, Box<ResolvedExpr>),
  Let(SourceLocation, usize, IsMut, Option<ResolvedTy>, Option<Box<ResolvedExpr>>),
  If(SourceLocation, Box<ResolvedExpr>, Box<ResolvedExpr>, Box<ResolvedExpr>),
  While(SourceLocation, Box<ResolvedExpr>, Box<ResolvedExpr>),
  Loop(SourceLocation, Box<ResolvedExpr>),
  Match(SourceLocation, Box<ResolvedExpr>, Vec<(Option<usize>, RefStr, ResolvedExpr)>)
}

impl ResolvedExpr {
  pub fn loc(&self) -> &SourceLocation {
    match self {
      ResolvedExpr::Nil(loc) => loc,
      ResolvedExpr::Bool(loc, _) => loc,
      ResolvedExpr::Int(loc, _) => loc,
      ResolvedExpr::Flt(loc, _) => loc,
      ResolvedExpr::Str(loc, _) => loc,
      ResolvedExpr::CStr(loc, _) => loc,
      ResolvedExpr::Unit(loc) => loc,
      ResolvedExpr::Dot(loc, _, _) => loc,
      ResolvedExpr::Call(loc, _, _) => loc,
      ResolvedExpr::Index(loc, _, _) => loc,
      ResolvedExpr::Adr(loc, _) => loc,
      ResolvedExpr::Ind(loc, _) => loc,
      ResolvedExpr::Un(loc, _, _) => loc,
      ResolvedExpr::LNot(loc, _) => loc,
      ResolvedExpr::Cast(loc, _, _) => loc,
      ResolvedExpr::Bin(loc, _, _, _) => loc,
      ResolvedExpr::LAnd(loc, _, _) => loc,
      ResolvedExpr::LOr(loc, _, _) => loc,
      ResolvedExpr::Block(loc, _) => loc,
      ResolvedExpr::As(loc, _, _) => loc,
      ResolvedExpr::Rmw(loc, _, _, _) => loc,
      ResolvedExpr::Continue(loc) => loc,
      ResolvedExpr::Break(loc, _) => loc,
      ResolvedExpr::Return(loc, _) => loc,
      ResolvedExpr::If(loc, _, _, _) => loc,
      ResolvedExpr::While(loc, _, _) => loc,
      ResolvedExpr::Loop(loc, _) => loc,
      ResolvedExpr::Match(loc, _, _) => loc,
      ResolvedExpr::TupleLit(loc, _) => loc,
      ResolvedExpr::ArrayLit(loc, _) => loc,
      ResolvedExpr::StructLit(loc, _, _, _) => loc,
      ResolvedExpr::UnionLit(loc, _, _, _, _) => loc,
      ResolvedExpr::UnitVariantLit(loc, _, _, _) => loc,
      ResolvedExpr::StructVariantLit(loc, _, _, _, _) => loc,
      ResolvedExpr::FuncRef(loc, _, _) => loc,
      ResolvedExpr::ExternFuncRef(loc, _) => loc,
      ResolvedExpr::ConstRef(loc, _) => loc,
      ResolvedExpr::DataRef(loc, _) => loc,
      ResolvedExpr::ExternDataRef(loc, _) => loc,
      ResolvedExpr::ParamRef(loc, _) => loc,
      ResolvedExpr::LetRef(loc, _) => loc,
      ResolvedExpr::BindingRef(loc, _) => loc,
      ResolvedExpr::Let(loc, _, _, _, _) => loc,
    }
  }
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
  pub loc: SourceLocation,
  pub name: RefStr,
  pub ty: ResolvedTy,
}

#[derive(Debug)]
pub struct ResolvedStructDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub type_params: usize,
  pub params: Vec<(RefStr, ResolvedTy)>,
}

#[derive(Debug)]
pub struct ResolvedUnionDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub type_params: usize,
  pub params: Vec<(RefStr, ResolvedTy)>,
}

#[derive(Debug)]
pub struct ResolvedEnumDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub type_params: usize,
  pub variants: Vec<ResolvedVariant>,
}

#[derive(Debug)]
pub enum ResolvedVariant {
  Unit(SourceLocation, RefStr),
  Struct(SourceLocation, RefStr, Vec<(RefStr, ResolvedTy)>),
}

#[derive(Debug)]
pub struct ResolvedConstDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub ty: ResolvedTy,
  pub val: ResolvedExpr,
}

#[derive(Debug)]
pub struct ResolvedDataDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub is_mut: IsMut,
  pub ty: ResolvedTy,
  pub init: ResolvedExpr,
}

#[derive(Debug)]
pub struct ResolvedFuncDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub type_params: usize,
  pub params: Vec<(RefStr, IsMut, ResolvedTy)>,
  pub ret_ty: ResolvedTy,
  pub body: ResolvedExpr,
}

#[derive(Debug)]
pub struct ResolvedExternDataDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub is_mut: IsMut,
  pub ty: ResolvedTy,
}

#[derive(Debug)]
pub struct ResolvedExternFuncDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub params: Vec<(RefStr, ResolvedTy)>,
  pub varargs: bool,
  pub ret_ty: ResolvedTy,
}
