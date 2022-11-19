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


/// Types

#[derive(Clone)]
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
  Ref(RefStr, Ptr<TyDef>),
  Ptr(IsMut, Box<Ty>),
  Func(Vec<(RefStr, Ty)>, Box<Ty>),
  Arr(usize, Box<Ty>),
  Tuple(Vec<(RefStr, Ty)>),
  // Deduction
  ClassAny,
  ClassNum,
  ClassInt,
  ClassFlt,
}

enum Variant {
  Unit(RefStr),
  Struct(RefStr, Vec<(RefStr, Ty)>),
}

struct TyDef {
  name: RefStr,
  kind: TyDefKind,
}

enum TyDefKind {
  ToBeFilled,
  Struct(Vec<(RefStr, Ty)>),
  Union(Vec<(RefStr, Ty)>),
  Enum(Vec<(RefStr, Variant)>),
}

impl TyDef {
  fn new(name: RefStr) -> Self {
    TyDef {
      name,
      kind: TyDefKind::ToBeFilled
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
      Ptr(is_mut, ty) => write!(f, "*{}{:?}", is_mut, ty),
      Func(params, ty) => {
        write!(f, "Function")?;
        write_params(f, params)?;
        write!(f, " -> {:?}", ty)
      },
      Arr(cnt, ty) => write!(f, "[{}]{:?}", cnt, ty),
      Tuple(params) => write_params(f, params),
      ClassAny => write!(f, "ClassAny"),
      ClassNum => write!(f, "ClassNum"),
      ClassInt => write!(f, "ClassInt"),
      ClassFlt => write!(f, "ClassFlt"),
    }
  }
}

/// Expressions

enum LValue {
  DataRef   { ty: Ty, def: Ptr<Def> },
  Str       { ty: Ty, val: RefStr },
  Dot       { ty: Ty, is_mut: IsMut, arg: Box<LValue>, name: RefStr, idx: usize },
  Index     { ty: Ty, is_mut: IsMut, arg: Box<LValue>, idx: Box<RValue> },
  Ind       { ty: Ty, is_mut: IsMut, arg: Box<RValue> },
}

enum RValue {
  Null      { ty: Ty },
  ConstRef  { ty: Ty, def: Ptr<Def> },
  FuncRef   { ty: Ty, def: Ptr<Def> },
  Load      { ty: Ty, arg: Box<LValue> },
  Bool      { ty: Ty, val: bool },
  Int       { ty: Ty, val: usize },
  Flt       { ty: Ty, val: f64 },
  Char      { ty: Ty, val: RefStr },
  Call      { ty: Ty, arg: Box<RValue>, args: Vec<(RefStr, RValue)> },
  Adr       { ty: Ty, arg: Box<LValue> },
  Un        { ty: Ty, op: UnOp, arg: Box<RValue> },
  LNot      { ty: Ty, arg: Box<RValue> },
  Cast      { ty: Ty, arg: Box<RValue> },
  Bin       { ty: Ty, op: BinOp, lhs: Box<RValue>, rhs: Box<RValue> },
  LAnd      { ty: Ty, lhs: Box<RValue>, rhs: Box<RValue> },
  LOr       { ty: Ty, lhs: Box<RValue>, rhs: Box<RValue> },
  Block     { ty: Ty, scope: IndexMap<RefStr, Own<Def>>, body: Vec<RValue> },
  As        { ty: Ty, lhs: Box<LValue>, rhs: Box<RValue> },
  Rmw       { ty: Ty, op: BinOp, lhs: Box<LValue>, rhs: Box<RValue> },
  Continue  { ty: Ty },
  Break     { ty: Ty, arg: Box<RValue> },
  Return    { ty: Ty, arg: Box<RValue> },
  Let       { ty: Ty, def: Ptr<Def>, init: Box<RValue> },
  If        { ty: Ty, cond: Box<RValue>, tbody: Box<RValue>, ebody: Box<RValue> },
  While     { ty: Ty, cond: Box<RValue>, body: Box<RValue> },
  Loop      { ty: Ty, body: Box<RValue> },
}

impl LValue {
  fn ty(&self) -> &Ty {
    match self {
      LValue::DataRef   { ty, .. } => ty,
      LValue::Str       { ty, .. } => ty,
      LValue::Dot       { ty, .. } => ty,
      LValue::Index     { ty, .. } => ty,
      LValue::Ind       { ty, .. } => ty,
    }
  }

  fn ty_mut(&mut self) -> &mut Ty {
    match self {
      LValue::DataRef   { ty, .. } => ty,
      LValue::Str       { ty, .. } => ty,
      LValue::Dot       { ty, .. } => ty,
      LValue::Index     { ty, .. } => ty,
      LValue::Ind       { ty, .. } => ty,
    }
  }

  fn is_mut(&self) -> IsMut {
    match self {
      LValue::DataRef   { def, .. }     => def.is_mut,
      LValue::Str       { .. }          => IsMut::No,
      LValue::Dot       { is_mut, .. }  => *is_mut,
      LValue::Index     { is_mut, .. }  => *is_mut,
      LValue::Ind       { is_mut, .. }  => *is_mut,
    }
  }
}

impl RValue {
  fn ty(&self) -> &Ty {
    match self {
      RValue::Null      { ty, .. } => ty,
      RValue::ConstRef  { ty, .. } => ty,
      RValue::FuncRef   { ty, .. } => ty,
      RValue::Load      { ty, .. } => ty,
      RValue::Bool      { ty, .. } => ty,
      RValue::Int       { ty, .. } => ty,
      RValue::Flt       { ty, .. } => ty,
      RValue::Char      { ty, .. } => ty,
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

  fn ty_mut(&mut self) -> &mut Ty {
    match self {
      RValue::Null      { ty, .. } => ty,
      RValue::ConstRef  { ty, .. } => ty,
      RValue::FuncRef   { ty, .. } => ty,
      RValue::Load      { ty, .. } => ty,
      RValue::Bool      { ty, .. } => ty,
      RValue::Int       { ty, .. } => ty,
      RValue::Flt       { ty, .. } => ty,
      RValue::Char      { ty, .. } => ty,
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

impl fmt::Debug for LValue {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      LValue::DataRef { def, .. } => {
        write!(f, "{}", def.name)
      }
      LValue::Str { val, .. } => {
        write!(f, "s{:?}", val)
      }
      LValue::Dot { arg, name, .. } => {
        write!(f, ".{} {:?}", name, arg)
      }
      LValue::Index { arg, idx, .. } => {
        write!(f, "[{:?}] {:?}", idx, arg)
      }
      LValue::Ind { arg, .. } => {
        write!(f, "Ind {:?}", arg)
      }
    }
  }
}

impl fmt::Debug for RValue {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      RValue::Null { .. } => {
        write!(f, "Null")
      }
      RValue::ConstRef { def, .. } |
      RValue::FuncRef { def, .. } => {
        write!(f, "{}", def.name)
      }
      RValue::Load { arg, .. } => {
        write!(f, "{:?}", arg)
      }
      RValue::Bool { val, .. } => {
        write!(f, "{}", val)
      }
      RValue::Int { val, .. } => {
        write!(f, "{}", val)
      }
      RValue::Flt { val, .. } => {
        write!(f, "{}", val)
      }
      RValue::Char { val, .. } => {
        write!(f, "c{:?}", val)
      }
      RValue::Call { arg, args, .. } => {
        write_comma_separated(f, args.iter(),
          |f, (name, arg)| write!(f, "{}: {:?}", name, arg))?;
        write!(f, " {:?}", arg)
      }
      RValue::Adr { arg, .. } => {
        write!(f, "Adr {:?}", arg)
      }
      RValue::Un { op, arg, .. } => {
        write!(f, "{:?} {:?}", op, arg)
      }
      RValue::LNot { arg, .. } => {
        write!(f, "LNot {:?}", arg)
      }
      RValue::Cast { ty, arg } => {
        write!(f, "Cast {:?} {:?}", arg, ty)
      }
      RValue::Bin { op, lhs, rhs, .. } => {
        write!(f, "{:?} {:?} {:?}", op, lhs, rhs)
      }
      RValue::LAnd { lhs, rhs, .. } => {
        write!(f, "LAnd {:?} {:?}", lhs, rhs)
      }
      RValue::LOr { lhs, rhs, .. } => {
        write!(f, "LOr {:?} {:?}", lhs, rhs)
      }
      RValue::Block { body, .. } => {
        write!(f, "{{\n")?;
        let mut pf = PadAdapter::wrap(f);
        for expr in body {
          write!(&mut pf, "{:?};\n", expr)?;
        }
        write!(f, "}}")
      }
      RValue::As { lhs, rhs, .. } => {
        write!(f, "As {:?} {:?}", lhs, rhs)
      }
      RValue::Rmw { op, lhs, rhs, .. } => {
        write!(f, "{:?}As {:?} {:?}", op, lhs, rhs)
      }
      RValue::Continue { .. } => {
        write!(f, "continue")
      }
      RValue::Break { arg, .. } => {
        write!(f, "break {:?}", arg)
      }
      RValue::Return { arg, .. } => {
        write!(f, "return {:?}", arg)
      }
      RValue::Let { def, init, .. } => {
        write!(f, "let {}{}: {:?} = {:?}", def.is_mut, def.name, def.ty, init)
      }
      RValue::If { cond, tbody, ebody, .. } => {
        write!(f, "if {:?} {:?} {:?}", cond, tbody, ebody)
      }
      RValue::While { cond, body, .. } => {
        write!(f, "while {:?} {:?}", cond, body)
      }
      RValue::Loop { body, .. } => {
        write!(f, "loop {:?}", body)
      }
    }
  }
}

/// Definitions

struct Def {
  name: RefStr,
  is_mut: IsMut,
  ty: Ty,
  kind: DefKind,
}

enum DefKind {
  ToBeFilled,
  Const(RValue),
  Func(IndexMap<RefStr, Own<Def>>, RValue),
  Data(RValue),
  ExternFunc,
  ExternData,
  Param(usize),
  Local,
}

impl Def {
  fn empty(name: RefStr, is_mut: IsMut, ty: Ty) -> Self {
    Def { name, is_mut, ty, kind: DefKind::ToBeFilled }
  }

  fn with_kind(name: RefStr, is_mut: IsMut, ty: Ty, kind: DefKind) -> Self {
    Def { name, is_mut, ty, kind }
  }
}

impl fmt::Debug for Def {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &self.kind {
      DefKind::ToBeFilled => unreachable!(),
      DefKind::Const(val) => {
        write!(f, "const {}: {:?} = {:#?}", self.name, self.ty, val)
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
        write!(f, ") -> {:?} {:#?}", body.ty(), body)
      }
      DefKind::Data(init) => {
        write!(f, "data {}{}: {:?} = {:#?}",
          self.is_mut, self.name, self.ty, init)
      }
      DefKind::ExternFunc => {
        write!(f, "extern fn {}: {:?}", self.name, self.ty)
      }
      DefKind::ExternData => {
        write!(f, "extern data {}{}: {:?}", self.is_mut, self.name, self.ty)
      }
      DefKind::Param(..) => {
        unreachable!()
      }
      DefKind::Local => {
        unreachable!()
      }
    }
  }
}

/// Module

#[derive(Debug)]
pub struct Module {
  // Type definitions
  ty_defs: IndexMap<RefStr, Own<TyDef>>,
  // Definitions
  defs: Vec<IndexMap<RefStr, Own<Def>>>,
}


/// Type checker and lowerer live in their own files

pub mod check;
pub mod lower;
