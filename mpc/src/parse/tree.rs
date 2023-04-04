/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IsMut { Yes, No }

impl fmt::Display for IsMut {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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

impl fmt::Display for Path {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
  Inst(Path, Vec<Ty>),
  Ptr(IsMut, Box<Ty>),
  Func(Vec<(RefStr, Ty)>, Box<Ty>),
  Arr(Box<Expr>, Box<Ty>),
  Unit,
  Tuple(Vec<(RefStr, Ty)>),
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
  Path(Path),
  Nil,
  Bool(bool),
  Int(usize),
  Flt(f64),
  Str(Vec<u8>),
  CStr(Vec<u8>),
  Unit,
  Tuple(Vec<(RefStr, Expr)>),
  Arr(Vec<Expr>),
  Dot(Box<Expr>, RefStr),
  Call(Box<Expr>, Vec<(RefStr, Expr)>),
  Index(Box<Expr>, Box<Expr>),
  Adr(Box<Expr>),
  Ind(Box<Expr>),
  Un(UnOp, Box<Expr>),
  LNot(Box<Expr>),
  Cast(Box<Expr>, Ty),
  Bin(BinOp, Box<Expr>, Box<Expr>),
  LAnd(Box<Expr>, Box<Expr>),
  LOr(Box<Expr>, Box<Expr>),
  Block(Vec<Expr>),
  As(Box<Expr>, Box<Expr>),
  Rmw(BinOp, Box<Expr>, Box<Expr>),
  Continue,
  Break(Box<Expr>),
  Return(Box<Expr>),
  Let(RefStr, IsMut, Option<Ty>, Option<Box<Expr>>),
  If(Box<Expr>, Box<Expr>, Box<Expr>),
  While(Box<Expr>, Box<Expr>),
  Loop(Box<Expr>),
  Match(Box<Expr>, Vec<(Option<RefStr>, RefStr, Expr)>)
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId(pub usize);

impl fmt::Debug for DefId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
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
  pub name: RefStr,
  pub ty: Ty
}

#[derive(Clone, Debug)]
pub struct StructDef {
  pub name: RefStr,
  pub type_params: Vec<RefStr>,
  pub params: Vec<(RefStr, Ty)>
}

#[derive(Clone, Debug)]
pub struct UnionDef {
  pub name: RefStr,
  pub type_params: Vec<RefStr>,
  pub params: Vec<(RefStr, Ty)>
}

#[derive(Clone, Debug)]
pub struct EnumDef {
  pub name: RefStr,
  pub type_params: Vec<RefStr>,
  pub variants: Vec<Variant>
}

#[derive(Clone, Debug)]
pub struct VariantDef {
  pub name: RefStr,
  pub parent_enum: DefId,
  pub variant_index: usize
}

#[derive(Clone, Debug)]
pub enum Variant {
  Unit(RefStr),
  Struct(RefStr, Vec<(RefStr, Ty)>),
}

#[derive(Clone, Debug)]
pub struct ConstDef {
  pub name: RefStr,
  pub ty: Ty,
  pub val: Expr
}

#[derive(Clone, Debug)]
pub struct DataDef {
  pub name: RefStr,
  pub is_mut: IsMut,
  pub ty: Ty,
  pub init: Expr
}

#[derive(Clone, Debug)]
pub struct FuncDef {
  pub name: RefStr,
  pub type_params: Vec<RefStr>,
  pub params: Vec<ParamDef>,
  pub ret_ty: Ty,
  pub body: Expr
}

pub type ParamDef = (RefStr, IsMut, Ty);

#[derive(Clone, Debug)]
pub struct ExternDataDef {
  pub name: RefStr,
  pub is_mut: IsMut,
  pub ty: Ty
}

#[derive(Clone, Debug)]
pub struct ExternFuncDef {
  pub name: RefStr,
  pub params: Vec<(RefStr, Ty)>,
  pub varargs: bool,
  pub ret_ty: Ty
}
