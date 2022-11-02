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
  Ref(RefStr, TyDef),
  Fn(Vec<(RefStr, Ty)>, Box<Ty>),
  Ptr(IsMut, Box<Ty>),
  Arr(usize, Box<Ty>),
  Tuple(Vec<(RefStr, Ty)>),
  // Deduction
  ClassAny,
  ClassNum,
  ClassInt,
}


pub type TyDef = Ptr<TyDefS>;

pub enum TyDefS {
  ToBeFilled,
  Struct(RefStr, Vec<(RefStr, Ty)>),
  Union(RefStr, Vec<(RefStr, Ty)>),
  Enum(RefStr, Vec<(RefStr, Variant)>),
}

pub enum Variant {
  Unit(RefStr),
  Struct(RefStr, Vec<(RefStr, Ty)>),
}

fn write_comma_separated<I, T, W>(f: &mut fmt::Formatter<'_>, iter: I, wfn: W) -> fmt::Result
  where I: Iterator<Item=T>,
        W: Fn(&mut fmt::Formatter<'_>, &T) -> fmt::Result,
{
  write!(f, "(")?;
  let mut comma = false;
  for item in iter {
    if comma {
      write!(f, ", ")?;
    } else {
      comma = true;
    }
    wfn(f, &item)?;
  }
  write!(f, ")")
}

fn write_params(f: &mut fmt::Formatter<'_>, params: &Vec<(RefStr, Ty)>) -> fmt::Result {
  write_comma_separated(f, params.iter(), |f, (name, ty)| write!(f, "{}: {:?}", name, ty))
}

impl fmt::Debug for TyDefS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use TyDefS::*;
    match self {
      Struct(name, params) => {
        write!(f, "struct {} ", name)?;
        write_params(f, params)
      },
      Union(name, params) => {
        write!(f, "union {} ", name)?;
        write_params(f, params)
      },
      Enum(name, variants) => {
        write!(f, "enum {} ", name)?;
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
      _ => unreachable!(),
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

pub struct Expr(Ty, ExprKind);

pub enum ExprKind {
  Ref(Ptr<Def>),
  Bool(bool),
  Int(usize),
  Char(RefStr),
  Str(RefStr),
  Dot(IsMut, Box<Expr>, RefStr),
  Call(Box<Expr>, Vec<(RefStr, Expr)>),
  Index(IsMut, Box<Expr>, Box<Expr>),
  Adr(Box<Expr>),
  Ind(IsMut, Box<Expr>),
  Un(UnOp, Box<Expr>),
  Cast(Box<Expr>, Ty),
  Bin(BinOp, Box<Expr>, Box<Expr>),
  Rmw(BinOp, Box<Expr>, Box<Expr>),
  As(Box<Expr>, Box<Expr>),
  Block(IndexMap<RefStr, Own<Def>>, Vec<Expr>),
  Continue,
  Break(Option<Box<Expr>>),
  Return(Option<Box<Expr>>),
  Let(Ptr<Def>, Box<Expr>),
  If(Box<Expr>, Box<Expr>, Box<Expr>),
  While(Box<Expr>, Box<Expr>),
  Loop(Box<Expr>),
}

impl fmt::Debug for Expr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use ExprKind::*;
    match &self.1 {
      Ref(def) => write!(f, "{}", def.name),
      Bool(val) => write!(f, "{}", val),
      Int(val) => write!(f, "{}", val),
      Char(val) => write!(f, "c{:?}", val),
      Str(val) => write!(f, "s{:?}", val),
      Dot(_, arg, name) => write!(f, ". {:?} {}", arg, name),
      Call(arg, args) => {
        write!(f, "{:?}", arg)?;
        write_comma_separated(f, args.iter(),
          |f, (name, arg)| write!(f, "{}: {:?}", name, arg))
      }
      Index(_, arg, idx) => write!(f, "{:?}[{:?}]", arg, idx),
      Adr(arg) => write!(f, "Adr {:?}", arg),
      Ind(_, arg) => write!(f, "Ind {:?}", arg),
      Un(op, arg) => write!(f, "{:?} {:?}", op, arg),
      Cast(arg, ty) => write!(f, "Cast {:?} {:?}", arg, ty),
      Bin(op, lhs, rhs) => write!(f, "{:?} {:?} {:?}", op, lhs, rhs),
      Rmw(op, lhs, rhs) => write!(f, "{:?}As {:?} {:?}", op, lhs, rhs),
      As(dst, src) => write!(f, "As {:?} {:?}", dst, src),
      Block(_, body) => {
        write!(f, "{{\n")?;
        let mut pf = PadAdapter::wrap(f);
        for expr in body {
          write!(&mut pf, "{:?};\n", expr)?;
        }
        write!(f, "}}")
      },
      Continue => write!(f, "continue"),
      Break(None) => write!(f, "break"),
      Break(Some(arg)) => write!(f, "break {:?}", arg),
      Return(None) => write!(f, "return"),
      Return(Some(arg)) => write!(f, "return {:?}", arg),
      Let(def, init) => write!(f, "let {}{}: {:?} = {:?}",
                                def.is_mut, def.name, def.ty, init),
      If(cond, tbody, ebody) => write!(f, "if {:?} {:?} {:?}",
                                        cond, tbody, ebody),
      While(cond, body) => write!(f, "while {:?} {:?}", cond, body),
      Loop(body) => write!(f, "loop {:?}", body),
    }
  }
}

/// Definitions

pub struct Def {
  name: RefStr,
  is_mut: IsMut,
  ty: Ty,
  kind: DefKind,
}

pub enum DefKind {
  ToBeFilled,
  Const(Expr),
  Func(IndexMap<RefStr, Own<Def>>, Expr),
  Data(Expr),
  ExternFunc,
  ExternData,
  Param(usize),
  Local,
}

impl fmt::Debug for Def {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &self.kind {
      DefKind::ToBeFilled => unreachable!(),
      DefKind::Const(val) => {
        todo!()
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
        write!(f, ") -> {:?} {:#?}", body.0, body)
      }
      DefKind::Data(init) => {
        write!(f, "data {}{}: {:?} = {:#?}",
          self.is_mut, self.name, init.0, init)
      }
      DefKind::ExternFunc => {
        write!(f, "extern fn {}: {:?}", self.name, self.ty)
      }
      DefKind::ExternData => {
        write!(f, "extern data {}{}: {:?}", self.is_mut, self.name, self.ty)
      }
      DefKind::Param(index) => {
        todo!()
      }
      DefKind::Local => {
        todo!()
      }
    }
  }
}

/// Module

pub struct Module {
  // Type definitions
  pub ty_defs: IndexMap<RefStr, Own<TyDefS>>,
  // Definitions
  pub defs: Vec<IndexMap<RefStr, Own<Def>>>,
}

/// Type checker and lowerer live in their own files

pub mod check;
pub mod lower;
