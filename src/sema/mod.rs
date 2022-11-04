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
  Fn(Vec<(RefStr, Ty)>, Box<Ty>),
  Ptr(IsMut, Box<Ty>),
  Arr(usize, Box<Ty>),
  Tuple(Vec<(RefStr, Ty)>),
  // Deduction
  ClassAny,
  ClassNum,
  ClassInt,
}

enum Variant {
  Unit(RefStr),
  Struct(RefStr, Vec<(RefStr, Ty)>),
}

struct TyDef {
  name: RefStr,
  kind: TyDefKind,
  l_type: LLVMTypeRef,
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

type Expr = Own<dyn lower::LowerExpr>;

trait ExprT: fmt::Debug {
  fn ty<'a>(&'a self) -> &'a Ty;
  fn ty_mut<'a>(&'a mut self) -> &'a mut Ty;
  fn is_mut_lvalue(&self) -> Option<IsMut> { None }
}

struct ExprRef { ty: Ty, def: Ptr<Def> }
struct ExprBool { ty: Ty, val: bool }
struct ExprInt { ty: Ty, val: usize }
struct ExprChar { ty: Ty, val: RefStr }
struct ExprStr { ty: Ty, val: RefStr }
struct ExprDot { ty: Ty, is_mut: IsMut, arg: Expr, name: RefStr, idx: usize }
struct ExprCall { ty: Ty, arg: Expr, args: Vec<(RefStr, Expr)> }
struct ExprIndex { ty: Ty, is_mut: IsMut, arg: Expr, idx: Expr }
struct ExprAdr { ty: Ty, arg: Expr }
struct ExprInd { ty: Ty, is_mut: IsMut, arg: Expr }
struct ExprUn { ty: Ty, op: UnOp, arg: Expr }
struct ExprLNot { ty: Ty, arg: Expr }
struct ExprCast { ty: Ty, arg: Expr }
struct ExprBin { ty: Ty, op: BinOp, lhs: Expr, rhs: Expr }
struct ExprLAnd { ty: Ty, lhs: Expr, rhs: Expr }
struct ExprLOr { ty: Ty, lhs: Expr, rhs: Expr }
struct ExprBlock { ty: Ty, scope: IndexMap<RefStr, Own<Def>>, body: Vec<Expr> }
struct ExprAs { ty: Ty, lhs: Expr, rhs: Expr }
struct ExprRmw { ty: Ty, op: BinOp, lhs: Expr, rhs: Expr }
struct ExprContinue { ty: Ty }
struct ExprBreak { ty: Ty, arg: Option<Expr> }
struct ExprReturn { ty: Ty, arg: Option<Expr> }
struct ExprLet { ty: Ty, def: Ptr<Def>, init: Expr }
struct ExprIf { ty: Ty, cond: Expr, tbody: Expr, ebody: Expr }
struct ExprWhile { ty: Ty, cond: Expr, body: Expr }
struct ExprLoop { ty: Ty, body: Expr }

impl ExprRef { fn new(ty: Ty, def: Ptr<Def>) -> Expr { Own::new(Self { ty, def }) } }
impl ExprBool { fn new(ty: Ty, val: bool) -> Expr { Own::new(Self { ty, val }) } }
impl ExprInt { fn new(ty: Ty, val: usize) -> Expr { Own::new(Self { ty, val }) } }
impl ExprChar { fn new(ty: Ty, val: RefStr) -> Expr { Own::new(Self { ty, val }) } }
impl ExprStr { fn new(ty: Ty, val: RefStr) -> Expr { Own::new(Self { ty, val }) } }
impl ExprDot { fn new(ty: Ty, is_mut: IsMut, arg: Expr, name: RefStr, idx: usize) -> Expr { Own::new(Self { ty, is_mut, arg, name, idx }) } }
impl ExprCall { fn new(ty: Ty, arg: Expr, args: Vec<(RefStr, Expr)>) -> Expr { Own::new(Self { ty, arg, args }) } }
impl ExprIndex { fn new(ty: Ty, is_mut: IsMut, arg: Expr, idx: Expr) -> Expr { Own::new(Self { ty, is_mut, arg, idx }) } }
impl ExprAdr { fn new(ty: Ty, arg: Expr) -> Expr { Own::new(Self { ty, arg }) } }
impl ExprInd { fn new(ty: Ty, is_mut: IsMut, arg: Expr) -> Expr { Own::new(Self { ty, is_mut, arg }) } }
impl ExprUn { fn new(ty: Ty, op: UnOp, arg: Expr) -> Expr { Own::new(Self { ty, op, arg }) } }
impl ExprLNot { fn new(ty: Ty, arg: Expr) -> Expr { Own::new(Self { ty, arg }) } }
impl ExprCast { fn new(ty: Ty, arg: Expr) -> Expr { Own::new(Self { ty, arg }) } }
impl ExprBin { fn new(ty: Ty, op: BinOp, lhs: Expr, rhs: Expr) -> Expr { Own::new(Self { ty, op, lhs, rhs }) } }
impl ExprLAnd { fn new(ty: Ty, lhs: Expr, rhs: Expr) -> Expr { Own::new(Self { ty, lhs, rhs }) } }
impl ExprLOr { fn new(ty: Ty, lhs: Expr, rhs: Expr) -> Expr { Own::new(Self { ty, lhs, rhs }) } }
impl ExprBlock { fn new(ty: Ty, scope: IndexMap<RefStr, Own<Def>>, body: Vec<Expr>) -> Expr { Own::new(Self { ty, scope, body }) } }
impl ExprAs { fn new(ty: Ty, lhs: Expr, rhs: Expr) -> Expr { Own::new(Self { ty, lhs, rhs }) } }
impl ExprRmw { fn new(ty: Ty, op: BinOp, lhs: Expr, rhs: Expr) -> Expr { Own::new(Self { ty, op, lhs, rhs }) } }
impl ExprContinue { fn new(ty: Ty) -> Expr { Own::new(Self { ty }) } }
impl ExprBreak { fn new(ty: Ty, arg: Option<Expr>) -> Expr { Own::new(Self { ty, arg }) } }
impl ExprReturn { fn new(ty: Ty, arg: Option<Expr>) -> Expr { Own::new(Self { ty, arg }) } }
impl ExprLet { fn new(ty: Ty, def: Ptr<Def>, init: Expr) -> Expr { Own::new(Self { ty, def, init }) } }
impl ExprIf { fn new(ty: Ty, cond: Expr, tbody: Expr, ebody: Expr) -> Expr { Own::new(Self { ty, cond, tbody, ebody }) } }
impl ExprWhile { fn new(ty: Ty, cond: Expr, body: Expr) -> Expr { Own::new(Self { ty, cond, body }) } }
impl ExprLoop { fn new(ty: Ty, body: Expr) -> Expr { Own::new(Self { ty, body }) } }

impl fmt::Debug for ExprRef {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.def.name)
  }
}
impl fmt::Debug for ExprBool {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.val)
  }
}
impl fmt::Debug for ExprInt {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.val)
  }
}
impl fmt::Debug for ExprChar {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "c{:?}", self.val)
  }
}
impl fmt::Debug for ExprStr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "s{:?}", self.val)
  }
}
impl fmt::Debug for ExprDot {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, ". {:?} {}", self.arg, self.name)
  }
}
impl fmt::Debug for ExprCall {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{:?}", self.arg)?;
    write_comma_separated(f, self.args.iter(),
      |f, (name, arg)| write!(f, "{}: {:?}", name, arg))
  }
}
impl fmt::Debug for ExprIndex {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{:?}[{:?}]", self.arg, self.idx)
  }
}
impl fmt::Debug for ExprAdr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Adr {:?}", self.arg)
  }
}
impl fmt::Debug for ExprInd {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Ind {:?}", self.arg)
  }
}
impl fmt::Debug for ExprUn {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{:?} {:?}", self.op, self.arg)
  }
}
impl fmt::Debug for ExprLNot {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "LNot {:?}", self.arg)
  }
}
impl fmt::Debug for ExprCast {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Cast {:?} {:?}", self.arg, self.ty)
  }
}
impl fmt::Debug for ExprBin {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{:?} {:?} {:?}", self.op, self.lhs, self.rhs)
  }
}
impl fmt::Debug for ExprLAnd {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "LAnd {:?} {:?}", self.lhs, self.rhs)
  }
}
impl fmt::Debug for ExprLOr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "LOr {:?} {:?}", self.lhs, self.rhs)
  }
}
impl fmt::Debug for ExprBlock {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{{\n")?;
    let mut pf = PadAdapter::wrap(f);
    for expr in &self.body {
      write!(&mut pf, "{:?};\n", expr)?;
    }
    write!(f, "}}")
  }
}
impl fmt::Debug for ExprAs {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "As {:?} {:?}", self.lhs, self.rhs)
  }
}
impl fmt::Debug for ExprRmw {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{:?}As {:?} {:?}", self.op, self.lhs, self.rhs)
  }
}
impl fmt::Debug for ExprContinue {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "continue")
  }
}
impl fmt::Debug for ExprBreak {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &self.arg {
      Some(arg) => write!(f, "break {:?}", arg),
      None => write!(f, "break")
    }
  }
}
impl fmt::Debug for ExprReturn {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &self.arg {
      Some(arg) => write!(f, "return {:?}", arg),
      None => write!(f, "return")
    }
  }
}
impl fmt::Debug for ExprLet {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "let {}{}: {:?} = {:?}",
      self.def.is_mut, self.def.name, self.def.ty, self.init)
  }
}
impl fmt::Debug for ExprIf {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "if {:?} {:?} {:?}", self.cond, self.tbody, self.ebody)
  }
}
impl fmt::Debug for ExprWhile {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "while {:?} {:?}", self.cond, self.body)
  }
}
impl fmt::Debug for ExprLoop {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "loop {:?}", self.body)
  }
}

impl ExprT for ExprRef {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
  fn is_mut_lvalue(&self) -> Option<IsMut> { Some(self.def.is_mut) }
}
impl ExprT for ExprBool {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprInt {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprChar {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprStr {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
  fn is_mut_lvalue(&self) -> Option<IsMut> { Some(IsMut::No) }
}
impl ExprT for ExprDot {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
  fn is_mut_lvalue(&self) -> Option<IsMut> { Some(self.is_mut) }
}
impl ExprT for ExprCall {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprIndex {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
  fn is_mut_lvalue(&self) -> Option<IsMut> { Some(self.is_mut) }
}
impl ExprT for ExprAdr {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprInd {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
  fn is_mut_lvalue(&self) -> Option<IsMut> { Some(self.is_mut) }
}
impl ExprT for ExprUn {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprLNot {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprCast {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprBin {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprLAnd {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprLOr {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprBlock {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprAs {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprRmw {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprContinue {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprBreak {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprReturn {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprLet {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprIf {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprWhile {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}
impl ExprT for ExprLoop {
  fn ty(&self) -> &Ty { &self.ty }
  fn ty_mut(&mut self) -> &mut Ty { &mut self.ty }
}

/// Definitions

struct Def {
  name: RefStr,
  is_mut: IsMut,
  ty: Ty,
  kind: DefKind,
  l_value: LLVMValueRef,
}

enum DefKind {
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
        todo!()
      }
      DefKind::Local => {
        todo!()
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
