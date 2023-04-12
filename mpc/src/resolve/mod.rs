/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use crate::*;
use crate::util::*;
use crate::parse::{self, Repository, DefId, UnOp, BinOp, IsMut};
use std::collections::HashMap;

mod tree;

pub use tree::*;

struct ResolveCtx<'a> {
  repo: &'a Repository,

  // Parent scope
  parent_id: DefId,

  // Local variables
  locals: usize,

  // Match bindings
  bindings: usize,

  // Symbol table
  scopes: Vec<HashMap<RefStr, Sym>>,
}

#[derive(Clone)]
enum Sym {
  Def(DefId),
  Param(usize),
  Local(usize),
  Binding(usize),
  TParam(usize)
}

impl<'a> ResolveCtx<'a> {
  fn new(repo: &'a Repository, parent_id: DefId) -> Self {
    ResolveCtx { repo, parent_id, locals: 0, bindings: 0, scopes: Vec::new() }
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
              receiver: &Option<(RefStr, IsMut, parse::Ty)>,
              params: &Vec<(RefStr, IsMut, parse::Ty)>) -> Self {
    let mut ctx = ResolveCtx::new(repo, parent_id);
    ctx.newscope();
    for (index, name) in type_params.iter().enumerate() {
      ctx.define(*name, Sym::TParam(index));
    }
    let base = if let Some((name, ..)) = receiver {
      ctx.define(*name, Sym::Param(0));
      1
    } else {
      0
    };
    for (index, (name, _, _)) in params.iter().enumerate() {
      ctx.define(*name, Sym::Param(base + index));
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
  fn lookup(&self, loc: SourceLocation, path: &parse::Path) -> Result<Sym, CompileError> {
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
      return Ok(Sym::Def(def_id));
    }

    Err(CompileError::UnresolvedPath(loc, path.clone()))
  }

  fn resolve_ty(&mut self, ty: &parse::Ty) -> Result<ResolvedTy, CompileError> {
    use parse::Ty::*;
    Ok(match ty {
      Bool(loc) => ResolvedTy::Bool(loc.clone()),
      Uint8(loc) => ResolvedTy::Uint8(loc.clone()),
      Int8(loc) => ResolvedTy::Int8(loc.clone()),
      Uint16(loc) => ResolvedTy::Uint16(loc.clone()),
      Int16(loc) => ResolvedTy::Int16(loc.clone()),
      Uint32(loc) => ResolvedTy::Uint32(loc.clone()),
      Int32(loc) => ResolvedTy::Int32(loc.clone()),
      Uint64(loc) => ResolvedTy::Uint64(loc.clone()),
      Int64(loc) => ResolvedTy::Int64(loc.clone()),
      Uintn(loc) => ResolvedTy::Uintn(loc.clone()),
      Intn(loc) => ResolvedTy::Intn(loc.clone()),
      Float(loc) => ResolvedTy::Float(loc.clone()),
      Double(loc) => ResolvedTy::Double(loc.clone()),
      Inst(loc, path, type_args) => {
        // Resolve type arguments
        let type_args = self.resolve_ty_args(type_args)?;

        // Resolve path
        match self.lookup(loc.clone(), path)? {
          Sym::Def(def_id) => {
            match self.repo.parsed_by_id(def_id) {
              parse::Def::Type(..) => ResolvedTy::AliasRef(loc.clone(), def_id, type_args),
              parse::Def::Struct(..) => ResolvedTy::StructRef(loc.clone(), def_id, type_args),
              parse::Def::Union(..) => ResolvedTy::UnionRef(loc.clone(), def_id, type_args),
              parse::Def::Enum(..) => ResolvedTy::EnumRef(loc.clone(), def_id, type_args),
              _ => Err(CompileError::InvalidTypeName(loc.clone(), path.clone()))?
            }
          }
          Sym::TParam(index) => ResolvedTy::TParam(loc.clone(), index),
          Sym::Local(..) |
          Sym::Binding(..) |
          Sym::Param(..) => Err(CompileError::InvalidTypeName(loc.clone(), path.clone()))?,
        }
      }
      Ptr(loc, is_mut, base_ty) => {
        ResolvedTy::Ptr(loc.clone(), *is_mut, Box::new(self.resolve_ty(base_ty)?))
      }
      Func(loc, params, ret_ty) => {
        let params = self.resolve_params(params)?;
        let ret_ty = self.resolve_ty(ret_ty)?;
        ResolvedTy::Func(loc.clone(), params, Box::new(ret_ty))
      }
      Arr(loc, elem_cnt, elem_ty) => {
        let elem_cnt = self.resolve_expr(elem_cnt)?;
        let elem_ty = self.resolve_ty(elem_ty)?;
        ResolvedTy::Arr(loc.clone(), Box::new(elem_cnt), Box::new(elem_ty))
      }
      Unit(loc) => {
        ResolvedTy::Unit(loc.clone())
      }
      Tuple(loc, params) => {
        let params = self.resolve_params(params)?;
        ResolvedTy::Tuple(loc.clone(), params)
      }
    })
  }

  fn resolve_ty_args(&mut self, ty_args: &Vec<parse::Ty>) -> Result<Vec<ResolvedTy>, CompileError> {
    ty_args
      .iter()
      .map(|ty| self.resolve_ty(ty))
      .monadic_collect()
  }

  fn resolve_params(&mut self, params: &Vec<(RefStr, parse::Ty)>) -> Result<Vec<(RefStr, ResolvedTy)>, CompileError> {
    params
      .iter()
      .map(|(name, ty)| Ok((*name, self.resolve_ty(ty)?)))
      .monadic_collect()
  }

  fn resolve_expr(&mut self, expr: &parse::Expr) -> Result<ResolvedExpr, CompileError> {
    use parse::Expr::*;

    Ok(match expr {
      Inst(loc, path, type_args) => {
        match self.lookup(loc.clone(), path)? {
          Sym::Def(def_id) => match self.repo.parsed_by_id(def_id) {
            parse::Def::Const(..) => {
              ResolvedExpr::ConstRef(loc.clone(), def_id)
            }
            parse::Def::ExternData(..) => {
              ResolvedExpr::ExternDataRef(loc.clone(), def_id)
            }
            parse::Def::Data(..) => {
              ResolvedExpr::DataRef(loc.clone(), def_id)
            }
            parse::Def::ExternFunc(..) => {
              ResolvedExpr::ExternFuncRef(loc.clone(), def_id)
            }
            parse::Def::Func(..) => {
              ResolvedExpr::FuncRef(loc.clone(),
                                    def_id,
                                    self.resolve_ty_args(type_args)?)
            }
            parse::Def::Variant(def) => {
              ResolvedExpr::UnitVariantLit(loc.clone(),
                                           def.parent_enum,
                                           self.resolve_ty_args(type_args)?,
                                           def.variant_index)
            }
            _ => Err(CompileError::InvalidValueName(loc.clone(), path.clone()))?
          }
          Sym::Local(index) => ResolvedExpr::LetRef(loc.clone(), index),
          Sym::Param(index) => ResolvedExpr::ParamRef(loc.clone(), index),
          Sym::Binding(index) => ResolvedExpr::BindingRef(loc.clone(), index),
          Sym::TParam(..) => Err(CompileError::InvalidValueName(loc.clone(), path.clone()))?
        }
      }
      Nil(loc) => ResolvedExpr::Nil(loc.clone()),
      Bool(loc, val) => ResolvedExpr::Bool(loc.clone(), *val),
      Int(loc, val) => ResolvedExpr::Int(loc.clone(), *val),
      Flt(loc, val) => ResolvedExpr::Flt(loc.clone(), *val),
      Str(loc, val) => ResolvedExpr::Str(loc.clone(), val.clone()),
      CStr(loc, val) => ResolvedExpr::CStr(loc.clone(), val.clone()),
      Unit(loc) => ResolvedExpr::Unit(loc.clone()),
      Tuple(loc, fields) => {
        let fields = fields
          .iter()
          .map(|(name, val)| Ok((*name, self.resolve_expr(val)?)))
          .monadic_collect()?;
        ResolvedExpr::TupleLit(loc.clone(), fields)
      }
      Arr(loc, elements) => {
        let elements = elements
          .iter()
          .map(|x| self.resolve_expr(x))
          .monadic_collect()?;
        ResolvedExpr::ArrayLit(loc.clone(), elements)
      }
      Dot(loc, base, field) => {
        let base = self.resolve_expr(base)?;
        ResolvedExpr::Dot(loc.clone(), Box::new(base), *field)
      }
      Index(loc, base, index) => {
        let base = self.resolve_expr(base)?;
        let index = self.resolve_expr(index)?;
        ResolvedExpr::Index(loc.clone(),
                            Box::new(base),
                            Box::new(index))
      }
      Ind(loc, ptr) => {
        let ptr = self.resolve_expr(ptr)?;
        ResolvedExpr::Ind(loc.clone(), Box::new(ptr))
      }
      Call(loc, called, args) => {
        // Resolve arguments
        let args = args
          .iter()
          .map(|(name, arg)| Ok((*name, self.resolve_expr(arg)?)))
          .monadic_collect()?;

        loop {
          // Check for aggregate constructor
          if let Inst(_, path, type_args) = &**called {
            match self.lookup(loc.clone(), path)? {
              Sym::Def(def_id) => match self.repo.parsed_by_id(def_id) {
                parse::Def::Type(..) => { todo!() }
                parse::Def::Struct(..) => {
                  break ResolvedExpr::StructLit(loc.clone(),
                                                def_id,
                                                self.resolve_ty_args(type_args)?,
                                                args);
                }
                parse::Def::Union(..) if args.len() == 1 => {
                  let (name, val) = args.into_iter().nth(0).unwrap();
                  break ResolvedExpr::UnionLit(loc.clone(),
                                               def_id,
                                               self.resolve_ty_args(type_args)?,
                                               name,
                                               Box::new(val));
                }
                parse::Def::Union(..) => {
                  Err(CompileError::InvalidUnionLiteral(loc.clone()))?
                }
                parse::Def::Variant(def) => {
                  break ResolvedExpr::StructVariantLit(loc.clone(),
                                                       def.parent_enum,
                                                       self.resolve_ty_args(type_args)?,
                                                       def.variant_index,
                                                       args);
                }
                _ => ()
              }
              _ => ()
            }
          }

          // Regular call expression
          let called = self.resolve_expr(called)?;
          break ResolvedExpr::Call(loc.clone(),
                                   Box::new(called),
                                   args);
        }
      }
      Adr(loc, arg) => {
        let arg = self.resolve_expr(arg)?;
        ResolvedExpr::Adr(loc.clone(), Box::new(arg))
      }
      Un(loc, op, arg) => {
        let arg = self.resolve_expr(arg)?;
        ResolvedExpr::Un(loc.clone(), *op, Box::new(arg))
      }
      LNot(loc, arg) => {
        let arg = self.resolve_expr(arg)?;
        ResolvedExpr::LNot(loc.clone(), Box::new(arg))
      }
      Cast(loc, arg, ty) => {
        let arg = self.resolve_expr(arg)?;
        let ty = self.resolve_ty(ty)?;
        ResolvedExpr::Cast(loc.clone(), Box::new(arg), ty)
      }
      Bin(loc, op, lhs, rhs) => {
        let lhs = self.resolve_expr(lhs)?;
        let rhs = self.resolve_expr(rhs)?;
        ResolvedExpr::Bin(loc.clone(), *op, Box::new(lhs), Box::new(rhs))
      }
      LAnd(loc, lhs, rhs) => {
        let lhs = self.resolve_expr(lhs)?;
        let rhs = self.resolve_expr(rhs)?;
        ResolvedExpr::LAnd(loc.clone(), Box::new(lhs), Box::new(rhs))
      }
      LOr(loc, lhs, rhs) => {
        let lhs = self.resolve_expr(lhs)?;
        let rhs = self.resolve_expr(rhs)?;
        ResolvedExpr::LOr(loc.clone(), Box::new(lhs), Box::new(rhs))
      }
      Block(loc, body) => {
        self.newscope();
        let body = body
          .iter()
          .map(|expr| self.resolve_expr(expr))
          .monadic_collect();
        self.popscope();

        ResolvedExpr::Block(loc.clone(), body?)
      }
      As(loc, lhs, rhs) => {
        let lhs = self.resolve_expr(lhs)?;
        let rhs = self.resolve_expr(rhs)?;
        ResolvedExpr::As(loc.clone(), Box::new(lhs), Box::new(rhs))
      }
      Rmw(loc, op, lhs, rhs) => {
        let lhs = self.resolve_expr(lhs)?;
        let rhs = self.resolve_expr(rhs)?;
        ResolvedExpr::Rmw(loc.clone(), *op, Box::new(lhs), Box::new(rhs))
      }
      Continue(loc) => ResolvedExpr::Continue(loc.clone()),
      Break(loc, arg) => {
        let arg = self.resolve_expr(&*arg)?;
        ResolvedExpr::Break(loc.clone(), Box::new(arg))
      }
      Return(loc, arg) => {
        let arg = self.resolve_expr(&*arg)?;
        ResolvedExpr::Return(loc.clone(), Box::new(arg))
      }
      Let(loc, name, is_mut, ty, init) => {
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

        let index = self.locals;
        self.define(*name, Sym::Local(index));
        self.locals += 1;

        ResolvedExpr::Let(loc.clone(), index, is_mut.clone(), ty, init)
      }
      If(loc, cond, tbody, ebody) => {
        let cond = self.resolve_expr(cond)?;
        let tbody = self.resolve_expr(tbody)?;
        let ebody = self.resolve_expr(ebody)?;
        ResolvedExpr::If(loc.clone(),
                         Box::new(cond),
                         Box::new(tbody),
                         Box::new(ebody))
      }
      While(loc, cond, body) => {
        let cond = self.resolve_expr(cond)?;
        let body = self.resolve_expr(body)?;
        ResolvedExpr::While(loc.clone(),
                            Box::new(cond),
                            Box::new(body))
      }
      Loop(loc, body) => {
        let body = self.resolve_expr(body)?;
        ResolvedExpr::Loop(loc.clone(), Box::new(body))
      }
      Match(loc, cond, cases) => {
        let cond = self.resolve_expr(cond)?;
        let mut resolved_cases = Vec::new();

        for (name, variant, val) in cases.iter() {
          self.newscope();
          let index = name.map(|name| {
            let index = self.bindings;
            self.define(name, Sym::Binding(index));
            self.bindings += 1;
            index
          });
          let result = self.resolve_expr(val);
          self.popscope();
          resolved_cases.push((index, *variant, result?));
        }

        ResolvedExpr::Match(loc.clone(),
                            Box::new(cond),
                            resolved_cases)
      }
    })
  }
}

fn receiver_id(loc: SourceLocation, ty: &ResolvedTy) -> Result<DefId, CompileError> {
  match ty {
    ResolvedTy::StructRef(_, def_id, _) |
    ResolvedTy::UnionRef(_, def_id, _) |
    ResolvedTy::EnumRef(_, def_id, _) => Ok(*def_id),
    ResolvedTy::Ptr(_, _, base_ty) => match &**base_ty {
      ResolvedTy::StructRef(_, def_id, _) |
      ResolvedTy::UnionRef(_, def_id, _) |
      ResolvedTy::EnumRef(_, def_id, _) => Ok(*def_id),
      _ => Err(CompileError::InvalidMethodReceiverType(loc, ty.clone()))
    }
    _ => Err(CompileError::InvalidMethodReceiverType(loc, ty.clone()))
  }
}

pub fn resolve_defs(repo: &mut Repository) -> Result<(), CompileError> {
  for (def_id, def) in repo.parsed_defs.iter() {
    match def {
      parse::Def::Type(def) => {
        let mut ctx = ResolveCtx::new(repo, repo.parent(*def_id));
        repo.resolved_defs.insert(*def_id,
                                  ResolvedDef::Type(ResolvedTypeDef {
                                    loc: def.loc.clone(),
                                    name: def.name,
                                    ty: ctx.resolve_ty(&def.ty)?,
                                  }),
        );
      }
      parse::Def::Struct(def) => {
        let mut ctx = ResolveCtx::new_generic(repo, repo.parent(*def_id), &def.type_params);
        repo.resolved_defs.insert(*def_id,
                                  ResolvedDef::Struct(ResolvedStructDef {
                                    loc: def.loc.clone(),
                                    name: def.name,
                                    type_params: def.type_params.len(),
                                    params: ctx.resolve_params(&def.params)?,
                                  }));
      }
      parse::Def::Union(def) => {
        let mut ctx = ResolveCtx::new_generic(repo, repo.parent(*def_id), &def.type_params);
        repo.resolved_defs.insert(*def_id,
                                  ResolvedDef::Union(ResolvedUnionDef {
                                    loc: def.loc.clone(),
                                    name: def.name,
                                    type_params: def.type_params.len(),
                                    params: ctx.resolve_params(&def.params)?,
                                  }));
      }
      parse::Def::Enum(def) => {
        let mut ctx = ResolveCtx::new_generic(repo, repo.parent(*def_id), &def.type_params);
        repo.resolved_defs.insert(*def_id,
                                  ResolvedDef::Enum(ResolvedEnumDef {
                                    loc: def.loc.clone(),
                                    name: def.name,
                                    type_params: def.type_params.len(),
                                    variants: def.variants
                                      .iter()
                                      .map(|variant| Ok(match variant {
                                        parse::Variant::Unit(loc, name) => {
                                          ResolvedVariant::Unit(loc.clone(), *name)
                                        },
                                        parse::Variant::Struct(loc, name, params) => {
                                          ResolvedVariant::Struct(loc.clone(),
                                                                  *name,
                                                                  ctx.resolve_params(params)?)
                                        }
                                      }))
                                      .monadic_collect()?,
                                  }));
      }
      parse::Def::Variant(..) => {
        // NOTE: this does not exist in resolved form
      }
      parse::Def::Const(def) => {
        let mut ctx = ResolveCtx::new(repo, repo.parent(*def_id));
        repo.resolved_defs.insert(*def_id,
                                  ResolvedDef::Const(ResolvedConstDef {
                                    loc: def.loc.clone(),
                                    name: def.name,
                                    ty: ctx.resolve_ty(&def.ty)?,
                                    val: ctx.resolve_expr(&def.val)?,
                                  }));
      }
      parse::Def::Data(def) => {
        let mut ctx = ResolveCtx::new(repo, repo.parent(*def_id));
        repo.resolved_defs.insert(*def_id,
                                  ResolvedDef::Data(ResolvedDataDef {
                                    loc: def.loc.clone(),
                                    name: def.name,
                                    is_mut: def.is_mut,
                                    ty: ctx.resolve_ty(&def.ty)?,
                                    init: ctx.resolve_expr(&def.init)?,
                                  }));
      }
      parse::Def::Func(def) => {
        let mut ctx = ResolveCtx::new_func(repo, repo.parent(*def_id),
                                           &def.type_params, &def.receiver, &def.params);

        // Parameters
        let mut params = Vec::new();
        let receiver_id = if let Some((name, is_mut, ty)) = &def.receiver {
          let ty = ctx.resolve_ty(ty)?;
          let receiver_id = receiver_id(def.loc.clone(), &ty)?;
          // Re-write receiver as a parameter
          params.push((*name, *is_mut, ty));
          // Save receiver ID for later
          Some(receiver_id)
        } else {
          None
        };
        for (name, is_mut, ty) in def.params.iter() {
          // Process regular parameters
          params.push((*name, *is_mut, ctx.resolve_ty(ty)?));
        }

        // Add definition
        repo.resolved_defs.insert(*def_id,
                                  ResolvedDef::Func(ResolvedFuncDef {
                                    loc: def.loc.clone(),
                                    name: def.name,
                                    type_params: def.type_params.len(),
                                    params,
                                    ret_ty: ctx.resolve_ty(&def.ret_ty)?,
                                    body: ctx.resolve_expr(&def.body)?
                                  }));

        // Add method to receiver's method table
        if let Some(receiver_id) = receiver_id {
          match repo.methods
            .entry(receiver_id)
            .or_insert_with(|| HashMap::new())
            .insert(def.name, *def_id) {
            Some(..) => Err(CompileError::Redefinition(def.loc.clone(), def.name))?,
            None => ()
          }
        }
      }
      parse::Def::ExternData(def) => {
        let mut ctx = ResolveCtx::new(repo, repo.parent(*def_id));
        repo.resolved_defs.insert(*def_id,
                                  ResolvedDef::ExternData(ResolvedExternDataDef {
                                    loc: def.loc.clone(),
                                    name: def.name,
                                    is_mut: def.is_mut,
                                    ty: ctx.resolve_ty(&def.ty)?,
                                  }));
      }
      parse::Def::ExternFunc(def) => {
        let mut ctx = ResolveCtx::new(repo, repo.parent(*def_id));
        repo.resolved_defs.insert(*def_id,
                                  ResolvedDef::ExternFunc(ResolvedExternFuncDef {
                                    loc: def.loc.clone(),
                                    name: def.name,
                                    varargs: def.varargs,
                                    params: ctx.resolve_params(&def.params)?,
                                    ret_ty: ctx.resolve_ty(&def.ret_ty)?,
                                  }));
      }
    }
  }
  Ok(())
}
