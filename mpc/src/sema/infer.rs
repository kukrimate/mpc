/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use crate::{CompileError, SourceLocation};
use crate::parse::Def;
use super::*;

pub(super) struct DefCtx<'global, 'repo, 'tctx> {
  // Global context
  pub global: &'global mut GlobalCtx<'repo, 'tctx>,
  // Parent scope id
  pub parent_id: DefId,
  // Symbol table
  pub scopes: Vec<HashMap<RefStr, Sym>>,
  // Local definitions
  pub local_cnt: usize,
  pub locals: HashMap<LocalId, (IsMut, Ty)>,
  // Function return type
  pub ret_ty: Option<Ty>,
  // Loop break type
  pub loop_ty: Vec<Ty>,
}

#[derive(Clone)]
pub enum Sym {
  Def(DefId),
  Param(LocalId),
  Local(LocalId),
  Binding(LocalId),
  TParam(Ty)
}

impl<'global, 'repo, 'tctx> DefCtx<'global, 'repo, 'tctx> {
  pub fn new(global: &'global mut GlobalCtx<'repo, 'tctx>, parent_id: DefId) -> Self {
    DefCtx {
      global,
      parent_id,
      scopes: Vec::new(),
      local_cnt: 0,
      locals: HashMap::new(),
      ret_ty: None,
      loop_ty: Vec::new(),
    }
  }

  /// Create a new local ID
  pub fn new_local_id(&mut self) -> LocalId {
    let local_id = LocalId(self.local_cnt);
    self.local_cnt += 1;
    local_id
  }

  /// Create scope
  pub fn newscope(&mut self) {
    self.scopes.push(HashMap::new());
  }

  /// Exit scope
  pub fn popscope(&mut self) {
    self.scopes.pop().unwrap();
  }

  /// Introduce symbol with a new name
  pub fn define(&mut self, name: RefStr, sym: Sym) {
    self.scopes.last_mut().unwrap().insert(name, sym);
  }

  /// Resolve symbol by name
  pub fn lookup(&self, loc: SourceLocation, path: &parse::Path) -> Result<Sym, CompileError> {
    // Single crumb paths can refer to locals
    if path.crumbs().len() == 1 {
      for scope in self.scopes.iter().rev() {
        if let Some(sym) = scope.get(&path.crumbs()[0]) {
          return Ok(sym.clone());
        }
      }
    }

    // Otherwise check the global symbol table
    if let Some(def_id) = self.global.repo.locate_path(self.parent_id, path) {
      return Ok(Sym::Def(def_id));
    }

    Err(CompileError::UnresolvedPath(loc, path.clone()))
  }

  /// Infer the semantic form of a type expression
  pub fn infer_ty(&mut self, ty: &parse::Ty) -> Result<Ty, CompileError> {
    use parse::Ty::*;
    Ok(match ty {
      Bool(_loc) => Ty::Bool,
      Uint8(_loc) => Ty::Uint8,
      Int8(_loc) => Ty::Int8,
      Uint16(_loc) => Ty::Uint16,
      Int16(_loc) => Ty::Int16,
      Uint32(_loc) => Ty::Uint32,
      Int32(_loc) => Ty::Int32,
      Uint64(_loc) => Ty::Uint64,
      Int64(_loc) => Ty::Int64,
      Uintn(_loc) => Ty::Uintn,
      Intn(_loc) => Ty::Intn,
      Float(_loc) => Ty::Float,
      Double(_loc) => Ty::Double,
      Inst(loc, path, type_args) => match self.lookup(loc.clone(), path)? {
        Sym::Def(def_id) => match self.global.parsed_def(def_id) {
          Def::Type(def) => {
            let type_args = self.infer_type_args(type_args)?;
            self.global.inst_alias(loc.clone(), (def_id, type_args), def)?
          }
          Def::Struct(def) => {
            let type_args = self.infer_type_args(type_args)?;
            self.global.inst_struct(loc.clone(), (def_id, type_args), def)?
          }
          Def::Union(def) => {
            let type_args = self.infer_type_args(type_args)?;
            self.global.inst_union(loc.clone(), (def_id, type_args), def)?
          }
          Def::Enum(def) => {
            let type_args = self.infer_type_args(type_args)?;
            self.global.inst_enum(loc.clone(), (def_id, type_args), def)?
          }
          _ => Err(CompileError::InvalidTypeName(loc.clone(), path.clone()))?
        }
        Sym::TParam(ty) => ty,
        _ => Err(CompileError::InvalidTypeName(loc.clone(), path.clone()))?
      }
      Ptr(_loc, is_mut, base_ty) => {
        Ty::Ptr(*is_mut, Box::new(self.infer_ty(base_ty)?))
      }
      Func(_loc, params, ret_ty) => {
        Ty::Func(self.infer_params(params)?,
                 false, Box::new(self.infer_ty(ret_ty)?))
      }
      Arr(_loc, elem_cnt_expr, elem_ty) => {
        let elem_cnt = self.infer_rvalue(elem_cnt_expr)
          .and_then(|rvalue| consteval_index(elem_cnt_expr.loc().clone(), &rvalue))?;
        Ty::Arr(elem_cnt, Box::new(self.infer_ty(elem_ty)?))
      }
      Unit(_loc, ) => {
        Ty::Unit
      }
      Tuple(_loc, params) => {
        Ty::Tuple(self.infer_params(params)?)
      }
    })
  }

  pub fn infer_params(&mut self, params: &Vec<(RefStr, parse::Ty)>) -> Result<Vec<(RefStr, Ty)>, CompileError> {
    let mut result = vec![];
    for (name, ty) in params {
      result.push((*name, self.infer_ty(ty)?));
    }
    Ok(result)
  }

  pub fn infer_type_args(&mut self, type_args: &Vec<parse::Ty>) -> Result<Vec<Ty>, CompileError> {
    type_args
      .iter()
      .map(|ty| self.infer_ty(ty))
      .monadic_collect()
  }

  pub fn infer_lvalue(&mut self, expr: &parse::Expr) -> Result<LValue, CompileError> {
    use parse::Expr::*;

    Ok(match expr {
      // NOTE: do something with type_args here
      Inst(loc, path, type_args) => match self.lookup(loc.clone(), path)? {
        Sym::Def(def_id) => match self.global.parsed_def(def_id) {
          Def::Const(def) => {
            self.global.inst_lvalue_const(loc.clone(), def_id, def)?
          }
          Def::Data(def) => {
            self.global.inst_data(loc.clone(), def_id, def)?
          }
          Def::ExternData(def) => {
            self.global.inst_extern_data(def_id, def)?
          }
          Def::UnitVariant(def) => {
            let enum_def = self.global.parsed_def(def.parent_enum).unwrap_enum();
            let type_args: Vec<Ty> = if type_args.len() > 0 {
              self.infer_type_args(type_args)?
            } else {
              (0..enum_def.type_params.len())
                .map(|_| self.global.tctx.new_var(Bound::Any))
                .collect()
            };
            let ty = self.global.inst_enum(loc.clone(), (def.parent_enum, type_args.clone()), enum_def)?;
            LValue::UnitVariantLit { ty, is_mut: IsMut::No, id: (def_id, type_args) }
          }
          _ => Err(CompileError::InvalidLvalueExpression(loc.clone()))?
        }
        Sym::Param(local_id) => {
          let (is_mut, ty) = self.locals.get(&local_id).unwrap();
          LValue::ParamRef {
            ty: ty.clone(),
            is_mut: *is_mut,
            local_id
          }
        }
        Sym::Local(local_id) => {
          let (is_mut, ty) = self.locals.get(&local_id).unwrap();
          LValue::LetRef {
            ty: ty.clone(),
            is_mut: *is_mut,
            local_id
          }
        }
        Sym::Binding(local_id) => {
          let (is_mut, ty) = self.locals.get(&local_id).unwrap();
          LValue::BindingRef {
            ty: ty.clone(),
            is_mut: *is_mut,
            local_id
          }
        }
        _ => Err(CompileError::InvalidLvalueExpression(expr.loc().clone()))?
      }
      Tuple(_loc, parsed_fields) => {
        let mut params = Vec::new();
        let mut fields = Vec::new();
        for (name, val) in parsed_fields.iter() {
          let val = self.infer_rvalue(val)?;
          params.push((*name, val.ty().clone()));
          fields.push(val);
        }
        LValue::TupleLit {
          ty: Ty::Tuple(params),
          is_mut: IsMut::No,
          fields
        }
      }
      Arr(loc, elements) => {
        let elem_ty = self.global.tctx.new_var(Bound::Any);
        let elements = elements.iter()
          .map(|element| self.infer_rvalue(element))
          .monadic_collect()?;
        for element in elements.iter() {
          self.global.tctx.unify(loc.clone(), &elem_ty, element.ty())?;
        }
        LValue::ArrayLit {
          ty: Ty::Arr(elements.len(), Box::new(elem_ty)),
          is_mut: IsMut::No,
          elements
        }
      }
      Call(loc, base, args) => {
        match &**base {
          Inst(_, path, type_args) => match self.lookup(loc.clone(), path)? {
            Sym::Def(def_id) => match self.global.parsed_def(def_id) {
              Def::Struct(struct_def) => {
                let type_args: Vec<Ty> = if type_args.len() > 0 {
                  self.infer_type_args(type_args)?
                } else {
                  (0..struct_def.type_params.len())
                    .map(|_| self.global.tctx.new_var(Bound::Any))
                    .collect()
                };
                let ty = self.global.inst_struct(loc.clone(), (def_id, type_args.clone()), struct_def)?;
                let (_, params) = self.global.find_inst(&(def_id, type_args)).unwrap_struct();
                let params = params.clone();
                let inferred_args = args
                  .iter()
                  .map(|(name, arg)| Ok((*name, self.infer_rvalue(arg)?)))
                  .monadic_collect()?;
                LValue::StructLit {
                  ty,
                  is_mut: IsMut::No,
                  fields: self.typecheck_args(loc.clone(), &params, false, inferred_args)?
                }
              }
              Def::Union(union_def) => {
                if args.len() != 1 {
                  Err(CompileError::InvalidUnionLiteral(loc.clone()))?
                }

                let (name, val) = (args[0].0, self.infer_rvalue(&args[0].1)?);

                // Instantiate union type
                let type_args: Vec<Ty> = if type_args.len() > 0 {
                  self.infer_type_args(type_args)?
                } else {
                  (0..union_def.type_params.len())
                    .map(|_| self.global.tctx.new_var(Bound::Any))
                    .collect()
                };
                let ty = self.global.inst_union(loc.clone(), (def_id, type_args.clone()), union_def)?;
                let (_, params) = self.global.find_inst(&(def_id, type_args)).unwrap_union();
                let params = params.clone();
                // Find which field the value belongs to
                if name.borrow_rs() == "" && params.len() > 0 {
                  self.global.tctx.unify(loc.clone(), val.ty(), &params[0].1)?;
                } else if let Some((_, param_ty)) = lin_search(&params, &name) {
                  self.global.tctx.unify(loc.clone(), val.ty(), param_ty)?;
                } else {
                  Err(CompileError::TypeHasNoField(loc.clone(), ty.clone(), name))?
                }

                LValue::UnionLit {
                  ty,
                  is_mut: IsMut::No,
                  field: val
                }
              }
              Def::StructVariant(variant_def) => {
                let enum_def = self.global.parsed_def(variant_def.parent_enum).unwrap_enum();
                let type_args: Vec<Ty> = if type_args.len() > 0 {
                  self.infer_type_args(type_args)?
                } else {
                  (0..enum_def.type_params.len())
                    .map(|_| self.global.tctx.new_var(Bound::Any))
                    .collect()
                };

                let ty = self.global.inst_enum(loc.clone(), (variant_def.parent_enum, type_args.clone()), enum_def)?;
                let inferred_args = args
                  .iter()
                  .map(|(name, arg)| Ok((*name, self.infer_rvalue(arg)?)))
                  .monadic_collect()?;

                let params = self.global.find_inst(&(def_id, type_args.clone())).unwrap_struct_variant().clone();

                LValue::StructVariantLit {
                  ty,
                  is_mut: IsMut::No,
                  id: (def_id, type_args),
                  fields: self.typecheck_args(loc.clone(), &params, false, inferred_args)?
                }
              }
              _ => Err(CompileError::InvalidLvalueExpression(loc.clone()))?
            }
            _ => Err(CompileError::InvalidLvalueExpression(loc.clone()))?
          }
          _ => Err(CompileError::InvalidLvalueExpression(loc.clone()))?
        }
      }
      Str(_loc, val) => {
        let ty = Ty::Arr(val.len(), Box::new(self.global.tctx.new_var(Bound::Int)));
        LValue::StrLit { ty, is_mut: IsMut::No, val: val.clone() }
      }
      Dot(loc, arg, name) => {
        let arg = self.infer_lvalue(arg)?;
        self.infer_dot(loc.clone(), arg, *name)?
      }
      Index(loc, arg, idx) => {
        self.infer_index(loc.clone(), arg, idx)?
      }
      Ind(loc, arg) => {
        self.infer_ind(loc.clone(), arg)?
      }
      expr => Err(CompileError::InvalidLvalueExpression(expr.loc().clone()))?
    })
  }

  pub fn infer_dot(&mut self, loc: SourceLocation, arg: LValue, name: RefStr) -> Result<LValue, CompileError> {
    // Find parameter list
    let ty = self.global.tctx.canonical_ty(arg.ty());

    let (is_struct, params) = match &ty {
      Ty::StructRef(_, id) => {
        let (_, params) = self.global.find_inst(id).unwrap_struct();
        (true, params)
      }
      Ty::UnionRef(_, id) => {
        let (_, params) = self.global.find_inst(id).unwrap_union();
        (false, params)
      }
      Ty::Tuple(params) => (true, params),
      _ => return Err(CompileError::TypeHasNoField(loc, arg.ty().clone(), name))
    };

    // Find parameter
    let (idx, param_ty) = match lin_search(params, &name) {
      Some(val) => val,
      None => return Err(CompileError::TypeHasNoField(loc, arg.ty().clone(), name))
    };

    if is_struct {
      Ok(LValue::StruDot {
        ty: param_ty.clone(),
        is_mut: arg.is_mut(),
        arg: Box::new(arg),
        idx,
      })
    } else {
      Ok(LValue::UnionDot {
        ty: param_ty.clone(),
        is_mut: arg.is_mut(),
        arg: Box::new(arg),
      })
    }
  }

  pub fn infer_index(&mut self, loc: SourceLocation, arg: &parse::Expr, idx: &parse::Expr) -> Result<LValue, CompileError> {
    // Infer array type
    let arg = self.infer_lvalue(arg)?;

    // Find element type
    let ty = self.global.tctx.canonical_ty(arg.ty());
    let elem_ty = match &ty {
      Ty::Arr(_, elem_ty) => &**elem_ty,
      _ => return Err(CompileError::CannotIndexType(loc, arg.ty().clone()))
    };

    // Check index type
    let idx = self.infer_rvalue(idx)?;
    self.global.tctx.unify(loc.clone(), &Ty::Uintn, idx.ty())?;

    Ok(LValue::Index {
      ty: elem_ty.clone(),
      is_mut: arg.is_mut(),
      arg: Box::new(arg),
      idx: Box::new(idx),
    })
  }

  pub fn infer_ind(&mut self, loc: SourceLocation, arg: &parse::Expr) -> Result<LValue, CompileError> {
    // Infer pointer type
    let arg = self.infer_rvalue(arg)?;

    // Find base type
    let ty = self.global.tctx.canonical_ty(arg.ty());
    let (is_mut, base_ty) = match &ty {
      Ty::Ptr(is_mut, base_ty) => (*is_mut, &**base_ty),
      _ => return Err(CompileError::CannotDereferenceType(loc, arg.ty().clone()))
    };

    Ok(LValue::Ind {
      ty: base_ty.clone(),
      is_mut,
      arg: Box::new(arg),
    })
  }

  pub fn infer_rvalue(&mut self, expr: &parse::Expr) -> Result<RValue, CompileError> {
    use parse::Expr::*;

    Ok(match expr {
      Inst(loc, path, type_args) => match self.lookup(loc.clone(), path)? {
        Sym::Def(def_id) => match self.global.parsed_def(def_id) {
          Def::Const(def) => {
            self.global.inst_rvalue_const(loc.clone(), def_id, def)?
          }
          Def::Func(def) => {
            let type_args: Vec<Ty> = if type_args.len() > 0 {
              self.infer_type_args(type_args)?
            } else {
              (0..def.type_params.len())
                .map(|_| self.global.tctx.new_var(Bound::Any))
                .collect()
            };
            self.global.inst_func_sig(loc.clone(), (def_id, type_args), def)?
          }
          Def::ExternFunc(def) => {
            self.global.inst_extern_func(def_id, def)?
          }
          Def::UnitVariant(..) | Def::Data(_) | Def::ExternData(..) => {
            let arg = self.infer_lvalue(expr)?;
            RValue::Load {
              ty: arg.ty().clone(),
              arg: Box::new(arg),
            }
          }
          _ => Err(CompileError::InvalidRValueExpression(loc.clone(), path.clone()))?
        }
        Sym::Param(..) | Sym::Local(..) | Sym::Binding(..) => {
          let arg = self.infer_lvalue(expr)?;
          RValue::Load {
            ty: arg.ty().clone(),
            arg: Box::new(arg),
          }
        }
        _ => Err(CompileError::InvalidRValueExpression(loc.clone(), path.clone()))?
      }
      Str(..) | Dot(..) | Index(..) | Tuple(..) | Arr(..) | Ind(..) => {
        let arg = self.infer_lvalue(expr)?;
        RValue::Load {
          ty: arg.ty().clone(),
          arg: Box::new(arg),
        }
      }
      CStr(_loc, val) => {
        RValue::CStr { ty: Ty::Ptr(IsMut::No, Box::new(Ty::Int8)), val: val.clone() }
      }
      Nil(_loc) => {
        RValue::Nil { ty: Ty::Ptr(IsMut::Yes, Box::new(self.global.tctx.new_var(Bound::Any))) }
      }
      Bool(_loc, val) => {
        RValue::Bool { ty: Ty::Bool, val: *val }
      }
      Int(_loc, val) => {
        RValue::Int { ty: self.global.tctx.new_var(Bound::Int), val: *val }
      }
      Flt(_loc, val) => {
        RValue::Flt { ty: self.global.tctx.new_var(Bound::Flt), val: *val }
      }
      Unit(_loc) => {
        RValue::Unit { ty: Ty::Unit }
      }
      Call(loc, called, args) => {
        match &**called {
          Inst(_, path, _) => {
            match self.lookup(loc.clone(), path)? {
              Sym::Def(def_id) => match self.global.parsed_def(def_id) {
                Def::Struct(..) |
                Def::Union(..) |
                Def::StructVariant(..) => {
                  let arg = self.infer_lvalue(expr)?;
                  RValue::Load {
                    ty: arg.ty().clone(),
                    arg: Box::new(arg),
                  }
                }
                _ => self.infer_call(loc.clone(), called, args)?
              }
              _ => self.infer_call(loc.clone(), called, args)?
            }
          }
          Dot(_, base, name) => {
            let receiver = self.infer_rvalue(&**base)?;
            let receiver_id = match self.global.tctx.canonical_ty(receiver.ty()) {
              Ty::StructRef(_, (def_id, _)) |
              Ty::UnionRef(_, (def_id, _)) |
              Ty::EnumRef(_, (def_id, _)) => def_id,
              Ty::Ptr(_, base_ty) => match *base_ty {
                Ty::StructRef(_, (def_id, _)) |
                Ty::UnionRef(_, (def_id, _)) |
                Ty::EnumRef(_, (def_id, _)) => def_id,
                // FIXME: handle fallback here
                _ => todo!()
              }
              _ => todo!()
            };
            let method_id = self.global.repo.locate_name(receiver_id, *name).unwrap();
            self.infer_method_call(loc.clone(), receiver, method_id, args)?
          }
          _ => self.infer_call(loc.clone(), called, args)?
        }
      }
      Adr(_loc, arg) => {
        let arg = self.infer_lvalue(arg)?;
        RValue::Adr {
          ty: Ty::Ptr(arg.is_mut(), Box::new(arg.ty().clone())),
          arg: Box::new(arg),
        }
      }
      Un(loc, op, arg) => {
        let arg = self.infer_rvalue(arg)?;
        RValue::Un {
          ty: self.infer_un(loc.clone(), *op, arg.ty())?,
          op: *op,
          arg: Box::new(arg),
        }
      }
      LNot(loc, arg) => {
        let arg = self.infer_rvalue(arg)?;
        self.global.tctx.unify(loc.clone(), &Ty::Bool, arg.ty())?;
        RValue::LNot { ty: Ty::Bool, arg: Box::new(arg) }
      }
      Cast(_loc, arg, ty) => {
        let arg = self.infer_rvalue(arg)?;
        let ty = self.infer_ty(ty)?;
        // FIXME: actually check if the type conversion is valid or not
        RValue::Cast { ty, arg: Box::new(arg) }
      }
      Bin(loc, op, lhs, rhs) => {
        let lhs = self.infer_rvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        let ty = self.infer_bin(loc.clone(), *op, lhs.ty(), rhs.ty())?;
        RValue::Bin { ty, op: *op, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      LAnd(loc, lhs, rhs) => {
        let lhs = self.infer_rvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        self.global.tctx.unify(loc.clone(), &Ty::Bool, lhs.ty())?;
        self.global.tctx.unify(loc.clone(), &Ty::Bool, rhs.ty())?;
        RValue::LAnd { ty: Ty::Bool, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      LOr(loc, lhs, rhs) => {
        let lhs = self.infer_rvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        self.global.tctx.unify(loc.clone(), &Ty::Bool, lhs.ty())?;
        self.global.tctx.unify(loc.clone(), &Ty::Bool, rhs.ty())?;
        RValue::LOr { ty: Ty::Bool, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Block(_loc, parsed_body) => {
        self.newscope();
        let body = parsed_body
          .iter()
          .map(|expr| self.infer_rvalue(expr))
          .monadic_collect();
        self.popscope();

        let body = body?;
        let ty = if let Some(last) = body.last() {
          last.ty().clone()
        } else {
          Ty::Unit
        };

        RValue::Block { ty, body }
      }
      As(loc, lhs, rhs) => {
        // Infer argument types
        let lhs = self.infer_lvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        self.global.tctx.unify(loc.clone(), lhs.ty(), rhs.ty())?;

        // Make sure lhs is mutable
        match lhs.is_mut() {
          IsMut::Yes => (),
          _ => return Err(CompileError::CannotAssignImmutable(loc.clone())),
        };

        RValue::As { ty: Ty::Unit, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Rmw(loc, op, lhs, rhs) => {
        // Infer and check argument types
        let lhs = self.infer_lvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        self.infer_bin(loc.clone(), *op, lhs.ty(), rhs.ty())?;

        // Make sure lhs is mutable
        match lhs.is_mut() {
          IsMut::Yes => (),
          _ => return Err(CompileError::CannotAssignImmutable(loc.clone())),
        };

        RValue::Rmw { ty: Ty::Unit, op: *op, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Continue(loc) => {
        // Can only have continue inside a loop
        match self.loop_ty.last() {
          Some(..) => (),
          None => return Err(CompileError::ContinueOutsideLoop(loc.clone())),
        };

        RValue::Continue { ty: self.global.tctx.new_var(Bound::Any) }
      }
      Break(loc, arg) => {
        let arg = self.infer_rvalue(&*arg)?;

        // Can only have break inside a loop
        let loop_ty = match self.loop_ty.last() {
          Some(loop_ty) => loop_ty.clone(),
          None => return Err(CompileError::BreakOutsideLoop(loc.clone())),
        };

        // Unify function return type with the returned value's type
        self.global.tctx.unify(loc.clone(), &loop_ty, arg.ty())?;

        RValue::Break { ty: self.global.tctx.new_var(Bound::Any), arg: Box::new(arg) }
      }
      Return(loc, arg) => {
        let arg = self.infer_rvalue(&*arg)?;

        // Can only have return inside a function
        let ret_ty = match self.ret_ty.as_ref() {
          Some(ret_ty) => ret_ty.clone(),
          None => return Err(CompileError::ReturnOutsideFunction(loc.clone())),
        };

        // Unify function return type with the returned value's type
        self.global.tctx.unify(loc.clone(), &ret_ty, arg.ty())?;

        RValue::Return { ty: self.global.tctx.new_var(Bound::Any), arg: Box::new(arg) }
      }
      Let(loc, name, is_mut, ty, init) => {
        let ty = if let Some(ty) = ty {
          self.infer_ty(ty)?
        } else {
          self.global.tctx.new_var(Bound::Any)
        };

        let init = if let Some(init) = init {
          let init = self.infer_rvalue(init)?;
          self.global.tctx.unify(loc.clone(), &ty, init.ty())?;
          Some(Box::new(init))
        } else {
          None
        };

        // Create local definition
        let local_id = self.new_local_id();
        self.define(*name, Sym::Local(local_id));
        self.locals.insert(local_id, (*is_mut, ty));
        RValue::Let { ty: Ty::Unit, local_id, init }
      }
      If(loc, cond, tbody, ebody) => {
        let cond = self.infer_rvalue(cond)?;
        self.global.tctx.unify(loc.clone(), &Ty::Bool, cond.ty())?;

        let tbody = self.infer_rvalue(tbody)?;
        let ebody = self.infer_rvalue(ebody)?;
        self.global.tctx.unify(loc.clone(), tbody.ty(), ebody.ty())?;

        RValue::If {
          ty: tbody.ty().clone(),
          cond: Box::new(cond),
          tbody: Box::new(tbody),
          ebody: Box::new(ebody),
        }
      }
      While(loc, cond, body) => {
        let cond = self.infer_rvalue(cond)?;
        self.global.tctx.unify(loc.clone(), &Ty::Bool, cond.ty())?;

        self.loop_ty.push(Ty::Unit);
        let body = self.infer_rvalue(body)?;
        let ty = self.loop_ty.pop().unwrap();

        RValue::While {
          ty,
          cond: Box::new(cond),
          body: Box::new(body),
        }
      }
      Loop(_loc, body) => {
        self.loop_ty.push(self.global.tctx.new_var(Bound::Any));
        let body = self.infer_rvalue(body)?;
        let ty = self.loop_ty.pop().unwrap();

        RValue::Loop {
          ty,
          body: Box::new(body),
        }
      }
      Match(loc, cond, cases) => {
        self.infer_match(loc.clone(), cond, cases)?
      }
    })
  }

  pub fn infer_method_call(&mut self, loc: SourceLocation, receiver: RValue, method_id: DefId, args: &Vec<(RefStr, parse::Expr)>) -> Result<RValue, CompileError> {

    // Return method reference as call target
    let def = self.global.parsed_def(method_id).unwrap_func();
    let type_args: Vec<Ty> = (0..def.type_params.len())
      .map(|_| self.global.tctx.new_var(Bound::Any))
      .collect();
    let called = self.global.inst_func_sig(loc.clone(), (method_id, type_args), def)?;

    // Infer arguments
    let mut inferred_args = Vec::new();
    inferred_args.push((RefStr::new(""), receiver));
    for (name, arg) in args.iter() {
      inferred_args.push((*name, self.infer_rvalue(arg)?));
    }

    // Find parameter list and return type
    match self.global.tctx.canonical_ty(called.ty()) {
      Ty::Func(params, va, ret_ty) => {
        Ok(RValue::Call {
          ty: *ret_ty,
          func: Box::new(called),
          args: self.typecheck_args(loc, &params, va, inferred_args)?
        })
      },
      _ => {
        Err(CompileError::CannotCallType(loc.clone(), called.ty().clone()))
      }
    }
  }

  pub fn infer_call(&mut self, loc: SourceLocation, called: &parse::Expr, args: &Vec<(RefStr, parse::Expr)>) -> Result<RValue, CompileError> {
    let called =  self.infer_rvalue(called)?;
    let args = args.iter()
      .map(|(name, arg)| Ok((*name, self.infer_rvalue(arg)?)))
      .monadic_collect()?;

    // Find parameter list and return type
    match self.global.tctx.canonical_ty(called.ty()) {
      Ty::Func(params, va, ret_ty) => {
        Ok(RValue::Call {
          ty: *ret_ty,
          func: Box::new(called),
          args: self.typecheck_args(loc, &params, va, args)?
        })
      },
      _ => {
        Err(CompileError::CannotCallType(loc.clone(), called.ty().clone()))
      }
    }
  }

  pub fn typecheck_args(&mut self, loc: SourceLocation, params: &[(RefStr, Ty)], va: bool, args: Vec<(RefStr, RValue)>) -> Result<Vec<RValue>, CompileError> {
    // Validate argument count
    if args.len() < params.len() {
      Err(CompileError::IncorrectNumberOfArguments(loc.clone()))?
    }
    if va == false && args.len() > params.len() {
      Err(CompileError::IncorrectNumberOfArguments(loc.clone()))?
    }

    let mut nargs = vec![];
    let mut params_iter = params.iter();

    for (arg_name, arg_val) in args.into_iter() {
      // If there is a corresponding parameter name and type, check it
      if let Some((param_name, param_ty)) = params_iter.next() {
        if arg_name != RefStr::new("") && arg_name != *param_name {
          return Err(CompileError::IncorrectArgumentLabel(loc, arg_name))
        }
        self.global.tctx.unify(loc.clone(), arg_val.ty(), param_ty)?;
      }
      // Append checked argument
      nargs.push(arg_val);
    }

    Ok(nargs)
  }

  pub fn infer_un(&mut self, loc: SourceLocation, op: UnOp, arg: &Ty) -> Result<Ty, CompileError> {
    // Check argument type
    match op {
      UnOp::UPlus | UnOp::UMinus => {
        self.global.tctx.bound(loc, arg, &Bound::Num)
      }
      UnOp::Not => {
        self.global.tctx.bound(loc, arg, &Bound::Int)
      }
    }
  }

  pub fn infer_bin(&mut self, loc: SourceLocation, op: BinOp, lhs: &Ty, rhs: &Ty) -> Result<Ty, CompileError> {
    // Check argument types and infer result type
    match op {
      // Both arguments must have matching numeric types
      // Result has the same type as the arguments
      BinOp::Mul | BinOp::Div | BinOp::Add | BinOp::Sub => {
        self.global.tctx.bound(loc.clone(), lhs, &Bound::Num)?;
        self.global.tctx.unify(loc, lhs, rhs)
      }

      // Both arguments must have matching integer types
      // Result has the same type as the arguments
      BinOp::Mod | BinOp::And | BinOp::Xor | BinOp::Or => {
        self.global.tctx.bound(loc.clone(), lhs, &Bound::Int)?;
        self.global.tctx.unify(loc, lhs, rhs)
      }

      // Both arguments must have integer types
      // Result has the left argument's type
      BinOp::Lsh | BinOp::Rsh => {
        self.global.tctx.bound(loc.clone(), rhs, &Bound::Int)?;
        self.global.tctx.bound(loc, lhs, &Bound::Int)
      }

      BinOp::Eq | BinOp::Ne => {
        self.global.tctx.bound(loc.clone(), lhs, &Bound::Eq)?;
        self.global.tctx.unify(loc, lhs, rhs)?;
        Ok(Ty::Bool)
      }

      BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
        self.global.tctx.bound(loc.clone(), lhs, &Bound::Num)?;
        self.global.tctx.unify(loc, lhs, rhs)?;
        Ok(Ty::Bool)
      }
    }
  }

  pub fn infer_match(&mut self, loc: SourceLocation, cond: &parse::Expr, patterns: &[(parse::Pattern, parse::Expr)]) -> Result<RValue, CompileError> {
    // FIXME: struct variant binding semantics on rvalue enums are hacky at best :(
    //
    // Enums are **always** lvalues at the LLVM level (even when semantically they were rvalues).
    // Thus we can cheat, and create non-mut lvalue bindings for fields of struct variants when
    // matched on enum rvalues.
    //
    // There are no good cleaner solutions in the current corner. What Rust does is to always
    // copy/move when doing matches on non-references, and only allow assignable bindings
    // through reference based matches.
    // I really, really do not want matches to be aware of pointers in Maple, thus this is not
    // a good solution.
    //
    // The cleanest solution would probably be to eliminate the existence of aggregate lvalues,
    // and aggregate loads (which are no-ops anyways) at the semantic level from MPC, but
    // this would require more work then I have time for at the moment.

    // Infer condition + find enum variants
    let cond = self.infer_rvalue(cond)?;

    // Figure out matched enum type
    let (def_id, type_args) = match self.global.tctx.canonical_ty(cond.ty()) {
      Ty::EnumRef(_, id) => id,
      _ => { return Err(CompileError::CannotMatchType(loc.clone(), cond.ty().clone())) }
    };

    // Figure out if the pattern bindings should be mutable
    let binding_mut = match &cond {
      RValue::Load { arg, .. } => arg.is_mut(),
      _ => IsMut::No
    };

    // Create mapping from enum variants to patterns
    let mut variant_to_value = HashMap::new();

    for (pattern, val) in patterns.iter() {
      // Find variant corresponding to pattern
      let variant_id = if let Some(variant_id) = self.global.repo.locate_path(def_id, &parse::Path(vec![ pattern.name() ])) {
        variant_id
      } else {
        return Err(CompileError::IncorrectMatchCase(loc.clone()));
      };
      // Save value into variant to value mp
      if let Some(..) = variant_to_value.insert(variant_id, (pattern, val)) {
        return Err(CompileError::DuplicateMatchCase(loc.clone()))
      }
    }

    // Verify that no variants are missing
    let (_, variants) = self.global.find_inst(&(def_id, type_args.clone())).unwrap_enum();
    if variant_to_value.len() != variants.len() {
      return Err(CompileError::MissingMatchCase(loc.clone()))?
    }

    // Iterate the variants of the matched enum
    let mut cases = Vec::new();

    for (variant_id, (pattern, value)) in variant_to_value.into_iter() {
      let id = (variant_id, type_args.clone());
      let inst = self.global.find_inst(&id);
      match (inst, pattern) {
        (Inst::UnitVariant { .. }, parse::Pattern::Unit(..)) => {
          cases.push((id.clone(), Vec::new(), self.infer_rvalue(value)?));
        }
        (Inst::StructVariant { params, .. }, parse::Pattern::Struct(_, bindings))
            if params.len() == bindings.len() => {
          let params = params.clone();
          self.newscope();
          let mut binding_ids = Vec::new();
          for (index, name) in bindings.iter().enumerate() {
            let local_id = self.new_local_id();
            self.define(*name, Sym::Binding(local_id));
            binding_ids.push(local_id);
            let (_, ty) = params.get(index).unwrap();
            self.locals.insert(local_id, (binding_mut, ty.clone()));
          }
          let val = self.infer_rvalue(value);
          self.popscope();
          cases.push((id.clone(), binding_ids, val?));
        }
        _ => return Err(CompileError::IncorrectMatchCase(loc.clone()))
      };
    }

    // Unify case types
    let ty = if cases.len() > 0 {
      cases[1..]
        .iter()
        .map(|(_, _, val)| val.ty())
        .try_fold(cases[0].2.ty().clone(),
                  |a, b| self.global.tctx.unify(loc.clone(), &a, b))?
    } else {
      Ty::Unit
    };

    Ok(RValue::Match {
      ty,
      cond: Box::new(cond),
      cases
    })
  }
}
