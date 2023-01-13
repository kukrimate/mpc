/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use crate::util::*;
use crate::parse::{self, Repository, DefId, UnOp, BinOp, IsMut};
use std::collections::HashMap;
use std::fmt::{self,Debug,Formatter};

pub fn resolve_def(repo: &Repository, def_id: DefId) -> MRes<ResolvedDef> {
  Ok(match repo.def_by_id(def_id) {
    parse::Def::Type(def) => {
      let mut ctx = ResolveCtx::new(repo, repo.parent(def_id));
      ResolvedDef::Type(ResolvedTypeDef {
        name: def.name,
        ty: ctx.resolve_ty(&def.ty)?
      })
    }
    parse::Def::Struct(def) => {
      let mut ctx = ResolveCtx::new_generic(repo, repo.parent(def_id), &def.type_params);
      ResolvedDef::Struct(ResolvedStructDef {
        name: def.name,
        type_params: def.type_params.len(),
        params: ctx.resolve_params(&def.params)?
      })
    }
    parse::Def::Union(def) => {
      let mut ctx = ResolveCtx::new_generic(repo, repo.parent(def_id), &def.type_params);
      ResolvedDef::Union(ResolvedUnionDef {
        name: def.name,
        type_params: def.type_params.len(),
        params: ctx.resolve_params(&def.params)?
      })
    }
    parse::Def::Enum(def) => {
      let mut ctx = ResolveCtx::new_generic(repo, repo.parent(def_id), &def.type_params);
      ResolvedDef::Enum(ResolvedEnumDef {
        name: def.name,
        type_params: def.type_params.len(),
        variants: def.variants
          .iter()
          .map(|variant| Ok(match variant {
            parse::Variant::Unit(name) => ResolvedVariant::Unit(*name),
            parse::Variant::Struct(name, params) => ResolvedVariant::Struct(*name,ctx.resolve_params(params)?)
          }))
          .monadic_collect()?
      })
    }
    parse::Def::Const(def) => {
      let mut ctx = ResolveCtx::new(repo, repo.parent(def_id));
      ResolvedDef::Const(ResolvedConstDef {
        name: def.name,
        ty: ctx.resolve_ty(&def.ty)?,
        val: ctx.resolve_expr(&def.val)?
      })
    }
    parse::Def::Data(def) => {
      let mut ctx = ResolveCtx::new(repo, repo.parent(def_id));
      ResolvedDef::Data(ResolvedDataDef {
        name: def.name,
        is_mut: def.is_mut,
        ty: ctx.resolve_ty(&def.ty)?,
        init: ctx.resolve_expr(&def.init)?,
      })
    }
    parse::Def::Func(def) => {
      let mut ctx = ResolveCtx::new_func(repo, repo.parent(def_id),
                                                    &def.type_params, &def.params);
      ResolvedDef::Func(ResolvedFuncDef {
        name: def.name,
        type_params: def.type_params.len(),
        params: def.params
          .iter()
          .map(|(_, is_mut, ty)|
            Ok((*is_mut, ctx.resolve_ty(ty)?)))
          .monadic_collect()?,
        ret_ty: ctx.resolve_ty(&def.ret_ty)?,
        body: ctx.resolve_expr(&def.body)?,
        locals: ctx.locals,
      })
    }
    parse::Def::ExternData(def) => {
      let mut ctx = ResolveCtx::new(repo, repo.parent(def_id));
      ResolvedDef::ExternData(ResolvedExternDataDef {
        name: def.name,
        is_mut: def.is_mut,
        ty: ctx.resolve_ty(&def.ty)?
      })
    }
    parse::Def::ExternFunc(def) => {
      let mut ctx = ResolveCtx::new(repo, repo.parent(def_id));
      ResolvedDef::ExternFunc(ResolvedExternFuncDef {
        name: def.name,
        varargs: def.varargs,
        params: ctx.resolve_params(&def.params)?,
        ret_ty: ctx.resolve_ty(&def.ret_ty)?
      })
    }
  })
}

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
  Inst(DefId, Vec<ResolvedTy>),
  Ptr(IsMut, Box<ResolvedTy>),
  Func(Vec<(RefStr, ResolvedTy)>, Box<ResolvedTy>),
  Arr(Box<ResolvedExpr>, Box<ResolvedTy>),
  Tuple(Vec<(RefStr, ResolvedTy)>)
}


#[derive(Debug)]
pub enum ResolvedExpr {
  // Empty expression
  Empty,

  // Literals
  Nil,
  Bool(bool),
  Int(usize),
  Flt(f64),
  Str(Vec<u8>),
  CStr(Vec<u8>),
  ArrayLit(Vec<ResolvedExpr>),
  StructLit(DefId, Vec<(RefStr, ResolvedExpr)>),

  // References
  FuncRef(DefId),
  ConstRef(DefId),
  DataRef(DefId),
  ParamRef(usize),
  LetRef(usize),

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
  ExternFunc(ResolvedExternFuncDef)
}

#[derive(Debug)]
pub struct ResolvedTypeDef {
  pub name: RefStr,
  pub ty: ResolvedTy
}

#[derive(Debug)]
pub struct ResolvedStructDef {
  pub name: RefStr,
  pub type_params: usize,
  pub params: Vec<(RefStr, ResolvedTy)>
}

#[derive(Debug)]
pub struct ResolvedUnionDef {
  pub name: RefStr,
  pub type_params: usize,
  pub params: Vec<(RefStr, ResolvedTy)>
}

#[derive(Debug)]
pub struct ResolvedEnumDef {
  pub name: RefStr,
  pub type_params: usize,
  pub variants: Vec<ResolvedVariant>
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
  pub val: ResolvedExpr
}

#[derive(Debug)]
pub struct ResolvedDataDef {
  pub name: RefStr,
  pub is_mut: IsMut,
  pub ty: ResolvedTy,
  pub init: ResolvedExpr
}

#[derive(Debug)]
pub struct ResolvedFuncDef {
  pub name: RefStr,
  pub type_params: usize,
  pub params: Vec<(IsMut, ResolvedTy)>,
  pub ret_ty: ResolvedTy,
  pub locals: Vec<(IsMut, Option<ResolvedTy>)>,
  pub body: ResolvedExpr
}

#[derive(Debug)]
pub struct ResolvedExternDataDef {
  pub name: RefStr,
  pub is_mut: IsMut,
  pub ty: ResolvedTy
}

#[derive(Debug)]
pub struct ResolvedExternFuncDef {
  pub name: RefStr,
  pub params: Vec<(RefStr, ResolvedTy)>,
  pub varargs: bool,
  pub ret_ty: ResolvedTy
}

struct ResolveCtx<'a> {
  repo: &'a Repository,

  // Parent scope
  parent_id: DefId,

  // Local variables
  locals: Vec<(IsMut, Option<ResolvedTy>)>,

  // Symbol table
  scopes: Vec<HashMap<RefStr, Sym>>,
}

#[derive(Clone)]
enum Sym {
  Def(DefId),
  Param(usize),
  Local(usize),
  TParam(usize)
}

impl<'a> ResolveCtx<'a> {
  fn new(repo: &'a Repository, parent_id: DefId) -> Self {
    ResolveCtx { repo, parent_id, locals: Vec::new(), scopes: Vec::new() }
  }

  fn new_generic(repo: &'a Repository,
                 parent_id: DefId,
                 type_params: &Vec<RefStr>) -> Self {
    let mut ctx = ResolveCtx::new(repo, parent_id);
    ctx.newscope();
    for (index, name) in type_params.iter().enumerate() {
      ctx.define(*name, Sym::TParam(index));
    }
    ctx
  }

  fn new_func(repo: &'a Repository,
              parent_id: DefId,
              type_params: &Vec<RefStr>,
              params: &Vec<parse::ParamDef>) -> Self {
    let mut ctx = ResolveCtx::new(repo, parent_id);
    ctx.newscope();
    for (index, name) in type_params.iter().enumerate() {
      ctx.define(*name, Sym::TParam(index));
    }
    for (index, (name, _, _)) in params.iter().enumerate() {
      ctx.define(*name, Sym::Param(index));
    }
    ctx
  }

  /// Create scope
  fn newscope(&mut self) {
    self.scopes.push(HashMap::new());
  }

  /// Exit scope
  fn popscope(&mut self) {
    self.scopes.pop().unwrap();
  }

  /// Introduce symbol with a new name
  fn define(&mut self, name: RefStr, sym: Sym) {
    self.scopes.last_mut().unwrap().insert(name, sym);
  }

  /// Resolve symbol by name
  fn lookup(&self, path: &parse::Path) -> Result<Sym, ResolveError> {
    // Single crumb paths can refer to locals
    if path.crumbs().len() == 1 {
      for scope in self.scopes.iter().rev() {
        if let Some(sym) = scope.get(&path.crumbs()[0]) {
          return Ok(sym.clone());
        }
      }
    }

    // Otherwise check the global symbol table
    if let Some(def_id) = self.repo.locate(self.parent_id, path) {
      return Ok(Sym::Def(def_id))
    }

    Err(ResolveError::UnresolvedPath(path.clone()))
  }

  fn resolve_ty(&mut self, ty: &parse::Ty) -> Result<ResolvedTy, ResolveError> {
    use parse::Ty::*;
    Ok(match ty {
      Bool => ResolvedTy::Bool,
      Uint8 => ResolvedTy::Uint8,
      Int8 => ResolvedTy::Int8,
      Uint16 => ResolvedTy::Uint16,
      Int16 => ResolvedTy::Int16,
      Uint32 => ResolvedTy::Uint32,
      Int32 => ResolvedTy::Int32,
      Uint64 => ResolvedTy::Uint64,
      Int64 => ResolvedTy::Int64,
      Uintn => ResolvedTy::Uintn,
      Intn => ResolvedTy::Intn,
      Float => ResolvedTy::Float,
      Double => ResolvedTy::Double,
      Inst(path, type_args) => {
        // Resolve type arguments
        let type_args = type_args
          .iter()
          .map(|ty| self.resolve_ty(ty))
          .monadic_collect2()?;

        // Resolve path
        match self.lookup(path)? {
          Sym::Def(def_id) => {
            match self.repo.def_by_id(def_id) {
              parse::Def::Type(..) |
              parse::Def::Struct(..) |
              parse::Def::Union(..) |
              parse::Def::Enum(..) => {
                ResolvedTy::Inst(def_id, type_args)
              }
              _ => Err(ResolveError::ValueInTypeContext(path.clone()))?
            }
          }
          Sym::Local(..) | Sym::Param(..) => Err(ResolveError::ValueInTypeContext(path.clone()))?,
          Sym::TParam(index) => ResolvedTy::TParam(index)
        }
      }
      Ptr(is_mut, base_ty) => {
        ResolvedTy::Ptr(*is_mut, Box::new(self.resolve_ty(base_ty)?))
      },
      Func(params, ret_ty) => {
        let params = self.resolve_params(params)?;
        let ret_ty = self.resolve_ty(ret_ty)?;
        ResolvedTy::Func(params, Box::new(ret_ty))
      },
      Arr(elem_cnt, elem_ty) => {
        let elem_cnt = self.resolve_expr(elem_cnt)?;
        let elem_ty = self.resolve_ty(elem_ty)?;
        ResolvedTy::Arr(Box::new(elem_cnt), Box::new(elem_ty))
      },
      Tuple(params) => {
        let params = self.resolve_params(params)?;
        ResolvedTy::Tuple(params)
      }
    })
  }

  fn resolve_params(&mut self, params: &Vec<(RefStr, parse::Ty)>) -> Result<Vec<(RefStr, ResolvedTy)>, ResolveError> {
    params
      .iter()
      .map(|(name, ty)| Ok((*name, self.resolve_ty(ty)?)))
      .monadic_collect2()
  }

  fn resolve_expr(&mut self, expr: &parse::Expr) -> Result<ResolvedExpr, ResolveError> {
    use parse::Expr::*;

    Ok(match expr {
      Empty => ResolvedExpr::Empty,
      Path(path) => {
        match self.lookup(path)? {
          Sym::Def(def_id) => match self.repo.def_by_id(def_id) {
            parse::Def::Const(..) => ResolvedExpr::ConstRef(def_id),
            parse::Def::ExternData(..) | parse::Def::Data(..) => ResolvedExpr::DataRef(def_id),
            parse::Def::ExternFunc(..) | parse::Def::Func(..) => ResolvedExpr::FuncRef(def_id),
            _ => Err(ResolveError::TypeInValueContext(path.clone()))?
          }
          Sym::Local(index) => ResolvedExpr::LetRef(index),
          Sym::Param(index) => ResolvedExpr::ParamRef(index),
          Sym::TParam(..) => Err(ResolveError::TypeInValueContext(path.clone()))?
        }
      }
      Nil => ResolvedExpr::Nil,
      Bool(val) => ResolvedExpr::Bool(*val),
      Int(val) => ResolvedExpr::Int(*val),
      Flt(val) => ResolvedExpr::Flt(*val),
      Str(val) => ResolvedExpr::Str(val.clone()),
      CStr(val) => ResolvedExpr::CStr(val.clone()),
      Arr(elements) => {
        let elements = elements
          .iter()
          .map(|x| self.resolve_expr(x))
          .monadic_collect2()?;
        ResolvedExpr::ArrayLit(elements)
      }
      Dot(base, field) => {
        let base = self.resolve_expr(base)?;
        ResolvedExpr::Dot(Box::new(base), *field)
      }
      Index(base, index) => {
        let base = self.resolve_expr(base)?;
        let index = self.resolve_expr(index)?;
        ResolvedExpr::Index(Box::new(base),
                            Box::new(index))
      }
      Ind(ptr) => {
        let ptr = self.resolve_expr(ptr)?;
        ResolvedExpr::Ind(Box::new(ptr))
      }
      Call(called, args) => {
        // Resolve arguments
        let args = args
          .iter()
          .map(|(name, arg)| Ok((*name, self.resolve_expr(arg)?)))
          .monadic_collect2()?;

        loop {
          // Check for aggregate constructor
          if let Path(path) = &**called {
            match self.lookup(path)? {
              Sym::Def(def_id) => match self.repo.def_by_id(def_id) {
                parse::Def::Type(..) => todo!(),
                parse::Def::Struct(..) => break ResolvedExpr::StructLit(def_id, args),
                parse::Def::Union(..) => todo!(),
                parse::Def::Enum(..) => todo!(),
                _ => ()
              }
              _ => ()
            }
          }

          // Regular call expression
          let called = self.resolve_expr(called)?;
          break ResolvedExpr::Call(Box::new(called),
                                   args)
        }
      }
      Adr(arg) => {
        let arg = self.resolve_expr(arg)?;
        ResolvedExpr::Adr(Box::new(arg))
      }
      Un(op, arg) => {
        let arg = self.resolve_expr(arg)?;
        ResolvedExpr::Un(*op, Box::new(arg))
      }
      LNot(arg) => {
        let arg = self.resolve_expr(arg)?;
        ResolvedExpr::LNot(Box::new(arg))
      }
      Cast(arg, ty) => {
        let arg = self.resolve_expr(arg)?;
        let ty = self.resolve_ty(ty)?;
        ResolvedExpr::Cast(Box::new(arg), ty)
      }
      Bin(op, lhs, rhs) => {
        let lhs = self.resolve_expr(lhs)?;
        let rhs = self.resolve_expr(rhs)?;
        ResolvedExpr::Bin(*op, Box::new(lhs), Box::new(rhs))
      }
      LAnd(lhs, rhs) => {
        let lhs = self.resolve_expr(lhs)?;
        let rhs = self.resolve_expr(rhs)?;
        ResolvedExpr::LAnd(Box::new(lhs), Box::new(rhs))
      }
      LOr(lhs, rhs) => {
        let lhs = self.resolve_expr(lhs)?;
        let rhs = self.resolve_expr(rhs)?;
        ResolvedExpr::LOr(Box::new(lhs), Box::new(rhs))
      }
      Block(body) => {
        self.newscope();
        let body = body
          .iter()
          .map(|expr| self.resolve_expr(expr))
          .monadic_collect2();
        self.popscope();

        ResolvedExpr::Block(body?)
      }
      As(lhs, rhs) => {
        let lhs = self.resolve_expr(lhs)?;
        let rhs = self.resolve_expr(rhs)?;
        ResolvedExpr::As(Box::new(lhs), Box::new(rhs))
      }
      Rmw(op, lhs, rhs) => {
        let lhs = self.resolve_expr(lhs)?;
        let rhs = self.resolve_expr(rhs)?;
        ResolvedExpr::Rmw(*op, Box::new(lhs), Box::new(rhs))
      }
      Continue => ResolvedExpr::Continue,
      Break(arg) => {
        let arg = self.resolve_expr(&*arg)?;
        ResolvedExpr::Break(Box::new(arg))
      }
      Return(arg) => {
        let arg = self.resolve_expr(&*arg)?;
        ResolvedExpr::Return(Box::new(arg))
      }
      Let(name, is_mut, ty, init) => {
        let ty = if let Some(ty) = ty {
          Some(self.resolve_ty(ty)?)
        } else {
          None
        };
        let init = if let Some(init) = init {
          Some(Box::new(self.resolve_expr(init)?))
        } else {
          None
        };

        let index = self.locals.len();
        self.locals.push((*is_mut, ty));
        self.define(*name, Sym::Local(index));

        ResolvedExpr::Let(index, init)
      }
      If(cond, tbody, ebody) => {
        let cond = self.resolve_expr(cond)?;
        let tbody = self.resolve_expr(tbody)?;
        let ebody = self.resolve_expr(ebody)?;
        ResolvedExpr::If(Box::new(cond),
                         Box::new(tbody),
                         Box::new(ebody))
      }
      While(cond, body) => {
        let cond = self.resolve_expr(cond)?;
        let body = self.resolve_expr(body)?;
        ResolvedExpr::While(Box::new(cond),
                            Box::new(body))
      }
      Loop(body) => {
        let body = self.resolve_expr(body)?;
        ResolvedExpr::Loop(Box::new(body))
      }
    })
  }
}

/// Errors

#[derive(Debug)]
enum ResolveError {
  UnresolvedPath(parse::Path),
  TypeInValueContext(parse::Path),
  ValueInTypeContext(parse::Path)
}

impl fmt::Display for ResolveError {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      ResolveError::UnresolvedPath(path) => write!(f, "Unresolved path {}", path),
      ResolveError::TypeInValueContext(path)  => write!(f, "Type {} used in value context", path),
      ResolveError::ValueInTypeContext(path) => write!(f, "Value {} used in type context", path)
    }
  }
}

impl std::error::Error for ResolveError {}
