/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IsMut { Yes, No }

impl std::fmt::Display for IsMut {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      IsMut::Yes => write!(f, "mut "),
      IsMut::No => write!(f, ""),
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Path(pub Vec<RefStr>);

impl Path {
  pub fn crumbs(&self) -> &Vec<RefStr> { &self.0 }
}

impl std::fmt::Display for Path {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    // There is always at least one crumb
    self.crumbs()[0].borrow_rs().fmt(f)?;
    // Then the rest can be prefixed with ::
    for crumb in self.crumbs()[1..].iter() {
      write!(f, "::")?;
      crumb.borrow_rs().fmt(f)?;
    }
    Ok(())
  }
}

#[derive(Clone, Debug)]
pub enum Ty {
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
  Inst(SourceLocation, Path, Vec<Ty>),
  Ptr(SourceLocation, IsMut, Box<Ty>),
  Func(SourceLocation, Vec<(RefStr, Ty)>, Box<Ty>),
  Arr(SourceLocation, Box<Expr>, Box<Ty>),
  Unit(SourceLocation),
  Tuple(SourceLocation, Vec<(RefStr, Ty)>),
}

#[derive(Clone,Copy,Debug)]
pub enum UnOp {
  UPlus, UMinus, Not
}

#[derive(Clone,Copy,Debug)]
pub enum BinOp {
  Mul, Div, Mod, Add, Sub, Lsh, Rsh, And, Xor, Or, Eq, Ne, Lt, Gt, Le, Ge
}

#[derive(Clone, Debug)]
pub enum Expr {
  Inst(SourceLocation, Path, Vec<Ty>),
  Nil(SourceLocation),
  Bool(SourceLocation, bool),
  Int(SourceLocation, usize),
  Flt(SourceLocation, f64),
  Str(SourceLocation, Vec<u8>),
  CStr(SourceLocation, Vec<u8>),
  Unit(SourceLocation),
  Tuple(SourceLocation, Vec<(RefStr, Expr)>),
  Arr(SourceLocation, Vec<Expr>),
  Dot(SourceLocation, Box<Expr>, RefStr),
  Call(SourceLocation, Box<Expr>, Vec<(RefStr, Expr)>),
  Index(SourceLocation, Box<Expr>, Box<Expr>),
  Adr(SourceLocation, Box<Expr>),
  Ind(SourceLocation, Box<Expr>),
  Un(SourceLocation, UnOp, Box<Expr>),
  LNot(SourceLocation, Box<Expr>),
  Cast(SourceLocation, Box<Expr>, Ty),
  Bin(SourceLocation, BinOp, Box<Expr>, Box<Expr>),
  LAnd(SourceLocation, Box<Expr>, Box<Expr>),
  LOr(SourceLocation, Box<Expr>, Box<Expr>),
  Block(SourceLocation, Vec<Expr>),
  As(SourceLocation, Box<Expr>, Box<Expr>),
  Rmw(SourceLocation, BinOp, Box<Expr>, Box<Expr>),
  Continue(SourceLocation),
  Break(SourceLocation, Box<Expr>),
  Return(SourceLocation, Box<Expr>),
  Let(SourceLocation, RefStr, IsMut, Option<Ty>, Option<Box<Expr>>),
  If(SourceLocation, Box<Expr>, Box<Expr>, Box<Expr>),
  While(SourceLocation, Box<Expr>, Box<Expr>),
  Loop(SourceLocation, Box<Expr>),
  Match(SourceLocation, Box<Expr>, Vec<(Option<RefStr>, RefStr, Expr)>)
}

impl Expr {
  #[allow(dead_code)]
  pub fn loc(&self) -> &SourceLocation {
    match self {
      Expr::Inst(loc, _, _) => loc,
      Expr::Nil(loc) => loc,
      Expr::Bool(loc, _) => loc,
      Expr::Int(loc, _) => loc,
      Expr::Flt(loc, _) => loc,
      Expr::Str(loc, _) => loc,
      Expr::CStr(loc, _) => loc,
      Expr::Unit(loc) => loc,
      Expr::Tuple(loc, _) => loc,
      Expr::Arr(loc, _) => loc,
      Expr::Dot(loc, _, _) => loc,
      Expr::Call(loc, _, _) => loc,
      Expr::Index(loc, _, _) => loc,
      Expr::Adr(loc, _) => loc,
      Expr::Ind(loc, _) => loc,
      Expr::Un(loc, _, _) => loc,
      Expr::LNot(loc, _) => loc,
      Expr::Cast(loc, _, _) => loc,
      Expr::Bin(loc, _, _, _) => loc,
      Expr::LAnd(loc, _, _) => loc,
      Expr::LOr(loc, _, _) => loc,
      Expr::Block(loc, _) => loc,
      Expr::As(loc, _, _) => loc,
      Expr::Rmw(loc, _, _, _) => loc,
      Expr::Continue(loc) => loc,
      Expr::Break(loc, _) => loc,
      Expr::Return(loc, _) => loc,
      Expr::Let(loc, _, _, _, _) => loc,
      Expr::If(loc, _, _, _) => loc,
      Expr::While(loc, _, _) => loc,
      Expr::Loop(loc, _) => loc,
      Expr::Match(loc, _, _) => loc,
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId(pub usize);

impl std::fmt::Debug for DefId {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.0.fmt(f) }
}

#[derive(Clone, Debug)]
pub enum Def {
  Type(TypeDef),
  Struct(StructDef),
  Union(UnionDef),
  Enum(EnumDef),
  Variant(VariantDef),
  Const(ConstDef),
  Data(DataDef),
  Func(FuncDef),
  ExternData(ExternDataDef),
  ExternFunc(ExternFuncDef)
}

#[derive(Clone, Debug)]
pub struct TypeDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub ty: Ty
}

#[derive(Clone, Debug)]
pub struct StructDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub type_params: Vec<RefStr>,
  pub params: Vec<(RefStr, Ty)>
}

#[derive(Clone, Debug)]
pub struct UnionDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub type_params: Vec<RefStr>,
  pub params: Vec<(RefStr, Ty)>
}

#[derive(Clone, Debug)]
pub struct EnumDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub type_params: Vec<RefStr>,
  pub variants: Vec<Variant>
}

#[derive(Clone, Debug)]
pub struct VariantDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub parent_enum: DefId,
  pub variant_index: usize
}

#[derive(Clone, Debug)]
pub enum Variant {
  Unit(SourceLocation, RefStr),
  Struct(SourceLocation, RefStr, Vec<(RefStr, Ty)>),
}

#[derive(Clone, Debug)]
pub struct ConstDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub ty: Ty,
  pub val: Expr
}

#[derive(Clone, Debug)]
pub struct DataDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub is_mut: IsMut,
  pub ty: Ty,
  pub init: Expr
}

#[derive(Clone, Debug)]
pub struct FuncDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub type_params: Vec<RefStr>,
  pub params: Vec<(RefStr, IsMut, Ty)>,
  pub ret_ty: Ty,
  pub body: Expr
}

#[derive(Clone, Debug)]
pub struct ExternDataDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub is_mut: IsMut,
  pub ty: Ty
}

#[derive(Clone, Debug)]
pub struct ExternFuncDef {
  pub loc: SourceLocation,
  pub name: RefStr,
  pub params: Vec<(RefStr, Ty)>,
  pub varargs: bool,
  pub ret_ty: Ty
}
