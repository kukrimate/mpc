/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use crate::{CompileError, SourceLocation};
use crate::parse::Repository;
use crate::resolve::*;
use super::*;

pub(super) fn infer(repo: &Repository, tctx: &mut TVarCtx) -> Result<HashMap<(DefId, Vec<Ty>), Inst>, CompileError> {
  let mut ctx = GlobalCtx {
    repo,
    tctx,
    insts: HashMap::new(),
  };

  // Instantiate signatures for non-generic functions
  for (id, def) in repo.resolved_defs.iter() {
    match def {
      ResolvedDef::Func(def) if def.type_params == 0 => {
        ctx.inst_func_sig(def.loc.clone(), (*id, Vec::new()))?;
      }
      _ => ()
    }
  }

  loop {
    // De-duplicate signatures after each pass
    for ((def_id, type_args), inst) in std::mem::replace(&mut ctx.insts, HashMap::new()).into_iter() {
      ctx.insts.insert((def_id, ctx.tctx.canonical_type_args(&type_args)), inst);
    }

    // Collect function signatures whose bodies need to be instantiated
    let mut queue = vec![];
    for ((def_id, type_args), inst) in ctx.insts.iter() {
      if let Inst::Func { body: None, .. } = inst {
        queue.push((*def_id, type_args.clone()));
      }
    }

    if queue.len() == 0 { break; }

    for (def_id, type_args) in queue.into_iter() {
      let def = ctx.resolved_def(def_id).unwrap_func();
      ctx.inst_func_body(def.loc.clone(), (def_id, type_args))?;
    }
  }

  // Final de-duplication pass to get rid of type variables in instance IDs
  for ((def_id, type_args), inst) in std::mem::replace(&mut ctx.insts, HashMap::new()).into_iter() {
    ctx.insts.insert((def_id, ctx.tctx.final_type_args(&type_args)), inst);
  }

  Ok(ctx.insts)
}

struct GlobalCtx<'repo, 'tctx> {
  // Parsed repository
  repo: &'repo Repository,
  // Type variable context
  tctx: &'tctx mut TVarCtx,
  // Checked definitions
  insts: HashMap<(DefId, Vec<Ty>), Inst>,
}

impl<'repo, 'tctx> GlobalCtx<'repo, 'tctx> {
  /// Lookup a parsed definition by its id
  fn resolved_def(&self, id: DefId) -> &'repo ResolvedDef {
    self.repo.resolved_defs.get(&id).unwrap()
  }

  /// Lookup an instance by its id
  fn find_inst(&mut self, id: &(DefId, Vec<Ty>)) -> &Inst {
    for ((def_id, type_args), inst) in std::mem::replace(&mut self.insts, HashMap::new()).into_iter() {
      self.insts.insert((def_id, self.tctx.canonical_type_args(&type_args)), inst);
    }
    self.insts.get(id).unwrap()
  }

  fn inst_alias(&mut self, id: (DefId, Vec<Ty>)) -> Result<Ty, CompileError> {
    let def = self.resolved_def(id.0).unwrap_type();

    DefCtx::new(self, id.1).infer_ty(&def.ty)
  }

  fn inst_struct(&mut self, loc: SourceLocation, id: (DefId, Vec<Ty>)) -> Result<Ty, CompileError> {
    let def = self.resolved_def(id.0).unwrap_struct();
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::StructRef(def.name, id)); }

    self.insts.insert(id.clone(), Inst::Struct { name: def.name, params: None });
    if def.type_params != id.1.len() {
      return Err(CompileError::IncorrectNumberOfTypeArguments(loc))
    }
    let mut def_ctx = DefCtx::new(self, id.1.clone());
    let params = def_ctx.infer_params(&def.params)?;
    self.insts.insert(id.clone(), Inst::Struct { name: def.name, params: Some(params) });

    Ok(Ty::StructRef(def.name, id))
  }

  fn inst_union(&mut self, loc: SourceLocation, id: (DefId, Vec<Ty>)) -> Result<Ty, CompileError> {
    let def = self.resolved_def(id.0).unwrap_union();
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::UnionRef(def.name, id)); }

    self.insts.insert(id.clone(), Inst::Union { name: def.name, params: None });
    if def.type_params != id.1.len() {
      return Err(CompileError::IncorrectNumberOfTypeArguments(loc))
    }
    let mut def_ctx = DefCtx::new(self, id.1.clone());
    let params = def_ctx.infer_params(&def.params)?;
    self.insts.insert(id.clone(), Inst::Union { name: def.name, params: Some(params) });

    Ok(Ty::UnionRef(def.name, id))
  }

  fn inst_enum(&mut self, loc: SourceLocation, id: (DefId, Vec<Ty>)) -> Result<Ty, CompileError> {
    let def = self.resolved_def(id.0).unwrap_enum();
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::EnumRef(def.name, id)); }

    self.insts.insert(id.clone(), Inst::Enum { name: def.name, variants: None });
    if def.type_params != id.1.len() {
      return Err(CompileError::IncorrectNumberOfTypeArguments(loc))
    }

    let mut def_ctx = DefCtx::new(self, id.1.clone());
    let variants = def_ctx.infer_variants(&def.variants)?;
    self.insts.insert(id.clone(), Inst::Enum { name: def.name, variants: Some(variants) });

    Ok(Ty::EnumRef(def.name, id))
  }

  fn inst_data(&mut self, loc: SourceLocation, id: DefId) -> Result<LValue, CompileError> {
    let def = self.resolved_def(id).unwrap_data();

    let mut def_ctx = DefCtx::new(self, Vec::new());

    let ty = def_ctx.infer_ty(&def.ty)?;
    let init = def_ctx.infer_rvalue(&def.init)?;
    self.tctx.unify(loc, &ty, init.ty())?;

    self.insts.insert((id, vec![]), Inst::Data {
      name: def.name,
      ty: ty.clone(),
      is_mut: def.is_mut,
      init: consteval(def.init.loc().clone(), &init)?,
    });

    Ok(LValue::DataRef { ty, is_mut: def.is_mut, id })
  }

  fn inst_func_sig(&mut self, loc: SourceLocation, id: (DefId, Vec<Ty>)) -> Result<RValue, CompileError> {
    let def = self.resolved_def(id.0).unwrap_func();

    // Check type argument count
    if def.type_params != id.1.len() {
      return Err(CompileError::IncorrectNumberOfTypeArguments(loc))
    }

    // Crate context
    let mut def_ctx = DefCtx::new(self, id.1.clone());

    // Parameters
    let mut param_tys = vec![];
    for (name, _, ty) in def.params.iter() {
      let ty = def_ctx.infer_ty(ty)?;
      param_tys.push((*name, ty.clone()));
    }

    // Return type
    let ret_ty = def_ctx.infer_ty(&def.ret_ty)?;

    // Insert signature record
    if let None = self.insts.get(&id) {
      self.insts.insert(id.clone(), Inst::Func {
        name: def.name,
        ty: Ty::Func(param_tys.clone(), false, Box::new(ret_ty.clone())),
        params: Vec::new(),
        locals: Vec::new(),
        bindings: HashMap::new(),
        body: None,
      });
    }

    // Return reference to signature
    Ok(RValue::FuncRef {
      ty: Ty::Func(param_tys.clone(), false, Box::new(ret_ty.clone())),
      id
    })
  }

  fn inst_func_body(&mut self, loc: SourceLocation, id: (DefId, Vec<Ty>)) -> Result<(), CompileError> {
    let def = self.resolved_def(id.0).unwrap_func();

    // Check type argument count
    if def.type_params != id.1.len() {
      return Err(CompileError::IncorrectNumberOfTypeArguments(loc))
    }

    // Setup context
    let mut def_ctx = DefCtx::new(self, id.1.clone());

    // Type parameters
    def_ctx.type_args = id.1.clone();

    // Function parameters
    let mut param_tys = vec![];
    for (name, is_mut, ty) in def.params.iter() {
      let ty = def_ctx.infer_ty(ty)?;
      param_tys.push((*name, ty.clone()));
      def_ctx.params.push((*is_mut, ty));
    }

    // Return type
    let ret_ty = def_ctx.infer_ty(&def.ret_ty)?;
    def_ctx.ret_ty = Some(ret_ty.clone());

    // Body
    let body = def_ctx.infer_rvalue(&def.body)?;
    def_ctx.global.tctx.unify(def.loc.clone(), &ret_ty, body.ty())?;

    // Insert body
    let inst = Inst::Func {
      name: def.name,
      ty: Ty::Func(param_tys.clone(), false, Box::new(ret_ty.clone())),
      params: def_ctx.params,
      locals: def_ctx.locals,
      bindings: def_ctx.bindings,
      body: Some(body),
    };
    self.insts.insert(id.clone(), inst);

    Ok(())
  }

  fn inst_extern_data(&mut self, id: DefId) -> Result<LValue, CompileError> {
    let def = self.resolved_def(id).unwrap_extern_data();

    let ty = DefCtx::new(self, Vec::new()).infer_ty(&def.ty)?;
    self.insts.insert((id, vec![]), Inst::ExternData { name: def.name, ty: ty.clone(), is_mut: def.is_mut });

    Ok(LValue::DataRef { ty, is_mut: def.is_mut, id })
  }

  fn inst_extern_func(&mut self, id: DefId) -> Result<RValue, CompileError> {
    let def = self.resolved_def(id).unwrap_extern_func();

    let mut def_ctx = DefCtx::new(self, Vec::new());
    let ty = Ty::Func(def_ctx.infer_params(&def.params)?,
                      def.varargs,
                      Box::new(def_ctx.infer_ty(&def.ret_ty)?));
    self.insts.insert((id, vec![]), Inst::ExternFunc { name: def.name, ty: ty.clone() });

    Ok(RValue::FuncRef { ty, id: (id, vec![]) })
  }
}

struct DefCtx<'global, 'repo, 'tctx> {
  // Global context
  global: &'global mut GlobalCtx<'repo, 'tctx>,
  // Values of type parameters in scope
  type_args: Vec<Ty>,
  // Function parameters
  params: Vec<(IsMut, Ty)>,
  // Let bindings
  locals: Vec<(IsMut, Ty)>,
  // Enum variant bindings
  bindings: HashMap<usize, (IsMut, Ty)>,
  // Function return type
  ret_ty: Option<Ty>,
  // Loop break type
  loop_ty: Vec<Ty>,
}

impl<'global, 'repo, 'tctx> DefCtx<'global, 'repo, 'tctx> {
  fn new(global: &'global mut GlobalCtx<'repo, 'tctx>, type_args: Vec<Ty>) -> Self {
    DefCtx {
      global,
      type_args,
      params: Vec::new(),
      locals: Vec::new(),
      bindings: HashMap::new(),
      ret_ty: None,
      loop_ty: Vec::new(),
    }
  }


  /// Infer the semantic form of a type expression
  fn infer_ty(&mut self, ty: &ResolvedTy) -> Result<Ty, CompileError> {
    use ResolvedTy::*;
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
      TParam(_loc, index) => {
        self.type_args[*index].clone()
      }
      AliasRef(_loc, def_id, type_args) => {
        let type_args = self.infer_type_args(type_args)?;
        self.global.inst_alias((*def_id, type_args))?
      }
      StructRef(loc, def_id, type_args) => {
        let type_args = self.infer_type_args(type_args)?;
        self.global.inst_struct(loc.clone(), (*def_id, type_args))?
      }
      UnionRef(loc, def_id, type_args) => {
        let type_args = self.infer_type_args(type_args)?;
        self.global.inst_union(loc.clone(), (*def_id, type_args))?
      }
      EnumRef(loc, def_id, type_args) => {
        let type_args = self.infer_type_args(type_args)?;
        self.global.inst_enum(loc.clone(), (*def_id, type_args))?
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

  fn infer_params(&mut self, params: &Vec<(RefStr, ResolvedTy)>) -> Result<Vec<(RefStr, Ty)>, CompileError> {
    let mut result = vec![];
    for (name, ty) in params {
      result.push((*name, self.infer_ty(ty)?));
    }
    Ok(result)
  }

  fn infer_variants(&mut self, variants: &Vec<ResolvedVariant>) -> Result<Vec<Variant>, CompileError> {
    let mut result = vec![];
    for variant in variants.iter() {
      result.push(match variant {
        ResolvedVariant::Unit(_loc, name) => {
          Variant::Unit(*name)
        }
        ResolvedVariant::Struct(_loc, name, params) => {
          Variant::Struct(*name, self.infer_params(params)?)
        }
      })
    }
    Ok(result)
  }

  fn infer_type_args(&mut self, type_args: &Vec<ResolvedTy>) -> Result<Vec<Ty>, CompileError> {
    type_args
      .iter()
      .map(|ty| self.infer_ty(ty))
      .monadic_collect()
  }

  /// Infer the semantic form of an expression in an lvalue context
  fn infer_lvalue(&mut self, expr: &ResolvedExpr) -> Result<LValue, CompileError> {
    use ResolvedExpr::*;

    Ok(match expr {
      ConstRef(_loc, def_id) => {
        let def = self.global.resolved_def(*def_id).unwrap_const();
        self.infer_lvalue(&def.val)?
      }
      DataRef(loc, def_id) => self.global.inst_data(loc.clone(), *def_id)?,
      ExternDataRef(_loc, def_id) => self.global.inst_extern_data(*def_id)?,
      ParamRef(_loc, index) => LValue::ParamRef {
        ty: self.params[*index].1.clone(),
        is_mut: self.params[*index].0,
        index: *index
      },
      LetRef(_loc, index) => LValue::LetRef {
        ty: self.locals[*index].1.clone(),
        is_mut: self.locals[*index].0,
        index: *index
      },
      BindingRef(_loc, index) => {
        let (is_mut, ty) = self.bindings.get(index).unwrap();
        LValue::BindingRef {
          ty: ty.clone(),
          is_mut: *is_mut,
          index: *index
        }
      },
      TupleLit(_loc, resolved_fields) => {
        let mut params = Vec::new();
        let mut fields = Vec::new();
        for (name, val) in resolved_fields.iter() {
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
      ArrayLit(loc, elements) => {
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
      StructLit(loc, def_id, type_args, fields) => {
        let def = self.global.resolved_def(*def_id).unwrap_struct();
        let type_args: Vec<Ty> = if type_args.len() > 0 {
          self.infer_type_args(type_args)?
        } else {
          (0..def.type_params)
            .map(|_| self.global.tctx.new_var(Bound::Any))
            .collect()
        };
        let ty = self.global.inst_struct(loc.clone(), (*def_id, type_args.clone()))?;
        let (_, params) = self.global.find_inst(&(*def_id, type_args)).unwrap_struct();
        let params = params.clone();
        let inferred_args = fields
          .iter()
          .map(|(name, arg)| Ok((*name, self.infer_rvalue(arg)?)))
          .monadic_collect()?;
        LValue::StructLit {
          ty,
          is_mut: IsMut::No,
          fields: self.typecheck_args(loc.clone(), &params, false, inferred_args)?
        }
      }
      UnionLit(loc, def_id, type_args, name, val) => {
        let val = self.infer_rvalue(val)?;

        // Instantiate union type
        let def = self.global.resolved_def(*def_id).unwrap_union();
        let type_args: Vec<Ty> = if type_args.len() > 0 {
          self.infer_type_args(type_args)?
        } else {
          (0..def.type_params)
            .map(|_| self.global.tctx.new_var(Bound::Any))
            .collect()
        };
        let ty = self.global.inst_union(loc.clone(), (*def_id, type_args.clone()))?;
        let (_, params) = self.global.find_inst(&(*def_id, type_args)).unwrap_union();
        let params = params.clone();
        // Find which field the value belongs to
        if name.borrow_rs() == "" && params.len() > 0 {
          self.global.tctx.unify(loc.clone(), val.ty(), &params[0].1)?;
        } else if let Some((_, param_ty)) = lin_search(&params, name) {
          self.global.tctx.unify(loc.clone(), val.ty(), param_ty)?;
        } else {
          Err(CompileError::TypeHasNoField(loc.clone(), ty.clone(), *name))?
        }

        LValue::UnionLit {
          ty,
          is_mut: IsMut::No,
          field: val
        }
      }
      UnitVariantLit(loc, def_id, type_args, index) => {
        let def = self.global.resolved_def(*def_id).unwrap_enum();
        let type_args: Vec<Ty> = if type_args.len() > 0 {
          self.infer_type_args(type_args)?
        } else {
          (0..def.type_params)
            .map(|_| self.global.tctx.new_var(Bound::Any))
            .collect()
        };
        let ty = self.global.inst_enum(loc.clone(), (*def_id, type_args.clone()))?;
        let (_, variants) = self.global.find_inst(&(*def_id, type_args)).unwrap_enum();
        match &variants[*index] {
          Variant::Unit(..) => (),
          Variant::Struct(..) => Err(CompileError::StructVariantExpectedArguments(loc.clone()))?
        }
        LValue::UnitVariantLit { ty, is_mut: IsMut::No, index: *index }
      }
      StructVariantLit(loc, def_id, type_args, index, fields) => {
        let def = self.global.resolved_def(*def_id).unwrap_enum();
        let type_args: Vec<Ty> = if type_args.len() > 0 {
          self.infer_type_args(type_args)?
        } else {
          (0..def.type_params)
            .map(|_| self.global.tctx.new_var(Bound::Any))
            .collect()
        };
        let ty = self.global.inst_enum(loc.clone(), (*def_id, type_args.clone()))?;
        let (_, variants) = self.global.find_inst(&(*def_id, type_args)).unwrap_enum();
        let variant = variants[*index].clone();
        let inferred_args = fields
          .iter()
          .map(|(name, arg)| Ok((*name, self.infer_rvalue(arg)?)))
          .monadic_collect()?;
        match variant {
          Variant::Unit(..) => Err(CompileError::UnitVariantUnexpectedArguments(loc.clone()))?,
          Variant::Struct(_, params) => {
            LValue::StructVariantLit {
              ty,
              is_mut: IsMut::No,
              index: *index,
              fields: self.typecheck_args(loc.clone(), &params.clone(), false, inferred_args)?
            }
          }
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

  /// Infer the type of a member access expression
  fn infer_dot(&mut self, loc: SourceLocation, arg: LValue, name: RefStr) -> Result<LValue, CompileError> {
    'error: loop {
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
        _ => break 'error
      };

      // Find parameter
      let (idx, param_ty) = match lin_search(params, &name) {
        Some(val) => val,
        None => break 'error
      };

      return if is_struct {
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
      };
    }

    Err(CompileError::TypeHasNoField(loc, arg.ty().clone(), name))
  }

  /// Infer the type of an array index expression
  fn infer_index(&mut self, loc: SourceLocation, arg: &ResolvedExpr, idx: &ResolvedExpr) -> Result<LValue, CompileError> {
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

  /// Infer the type of a pointer indirection expression
  fn infer_ind(&mut self, loc: SourceLocation, arg: &ResolvedExpr) -> Result<LValue, CompileError> {
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

  /// Infer the semantic form of an expression in an rvalue context
  fn infer_rvalue(&mut self, expr: &ResolvedExpr) -> Result<RValue, CompileError> {
    use ResolvedExpr::*;

    Ok(match expr {
      ConstRef(_loc, def_id) => {
        let def = self.global.resolved_def(*def_id).unwrap_const();
        self.infer_rvalue(&def.val)?
      }
      FuncRef(loc, def_id, type_args) => {
        let def = self.global.resolved_def(*def_id).unwrap_func();
        let type_args: Vec<Ty> = if type_args.len() > 0 {
          self.infer_type_args(type_args)?
        } else {
          (0..def.type_params)
            .map(|_| self.global.tctx.new_var(Bound::Any))
            .collect()
        };
        self.global.inst_func_sig(loc.clone(), (*def_id, type_args))?
      },
      ExternFuncRef(_loc, def_id) => self.global.inst_extern_func(*def_id)?,
      DataRef(..) |
      ExternDataRef(..) |
      ParamRef(..) |
      LetRef(..) |
      BindingRef(..) |
      TupleLit(..) |
      ArrayLit(..) |
      StructLit(..) |
      UnionLit(..) |
      UnitVariantLit(..) |
      StructVariantLit(..) |
      Str(..) |
      Dot(..) |
      Index(..) |
      Ind(..) => {
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
        self.infer_call(loc.clone(), called, args)?
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
        let mut body = vec![];
        for expr in parsed_body {
          body.push(self.infer_rvalue(expr)?);
        }

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
      Let(loc, index, is_mut, ty, init) => {
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

        assert_eq!(self.locals.len(), *index);
        self.locals.push((*is_mut, ty));

        RValue::Let { ty: Ty::Unit, index: *index, init }
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

  fn infer_call(&mut self, loc: SourceLocation, called: &ResolvedExpr, args: &Vec<(RefStr, ResolvedExpr)>) -> Result<RValue, CompileError> {
    let mut inferred_args = Vec::new();

    // Infer function type
    let called_expr = match called {
      ResolvedExpr::Dot(loc, base, name) => {
        let receiver = self.infer_rvalue(&**base)?;
        let receiver_id = match self.global.tctx.canonical_ty(receiver.ty()) {
          Ty::StructRef(_, (def_id, _)) |
          Ty::UnionRef(_, (def_id, _)) |
          Ty::EnumRef(_, (def_id, _)) => def_id,
          Ty::Ptr(_, base_ty) => match *base_ty {
            Ty::StructRef(_, (def_id, _)) |
            Ty::UnionRef(_, (def_id, _)) |
            Ty::EnumRef(_, (def_id, _)) => def_id,
            _ => todo!()
          }
          _ => todo!()
        };
        // FIXME: handle fallback here
        let method_id = self.global.repo.locate_method(receiver_id, *name).unwrap();
        // Add receiver instance as argument
        inferred_args.push((RefStr::new(""), receiver));
        // Return method reference as call target
        let def = self.global.resolved_def(method_id).unwrap_func();
        let type_args: Vec<Ty> = (0..def.type_params)
          .map(|_| self.global.tctx.new_var(Bound::Any))
          .collect();
        self.global.inst_func_sig(loc.clone(), (method_id, type_args))?
      }
      called => self.infer_rvalue(called)?
    };

    // Infer non-receiver arguments
    for (name, arg) in args.iter() {
      inferred_args.push((*name, self.infer_rvalue(arg)?));
    }

    // Find parameter list and return type
    match self.global.tctx.canonical_ty(called_expr.ty()) {
      Ty::Func(params, va, ret_ty) => {
        Ok(RValue::Call {
          ty: *ret_ty,
          func: Box::new(called_expr),
          args: self.typecheck_args(loc, &params, va, inferred_args)?
        })
      },
      _ => {
        Err(CompileError::CannotCallType(loc.clone(), called_expr.ty().clone()))
      }
    }
  }

  fn typecheck_args(&mut self, loc: SourceLocation, params: &[(RefStr, Ty)], va: bool, args: Vec<(RefStr, RValue)>) -> Result<Vec<RValue>, CompileError> {
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

  fn infer_un(&mut self, loc: SourceLocation, op: UnOp, arg: &Ty) -> Result<Ty, CompileError> {
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

  fn infer_bin(&mut self, loc: SourceLocation, op: BinOp, lhs: &Ty, rhs: &Ty) -> Result<Ty, CompileError> {
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

  fn infer_match(&mut self, loc: SourceLocation, cond: &ResolvedExpr, patterns: &[(ResolvedPattern, ResolvedExpr)]) -> Result<RValue, CompileError> {
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

    // Figure out if the pattern bindings should be mutable
    let binding_mut = match &cond {
      RValue::Load { arg, .. } => arg.is_mut(),
      _ => IsMut::No
    };

    // Collect list of patterns
    let mut pattern_map = HashMap::new();
    for (pattern, val) in patterns.iter() {
      if let Some(..) = pattern_map.insert(pattern.name(), (pattern, val)) {
        return Err(CompileError::DuplicateMatchCase(loc))
      }
    }

    // Iterate the variants of the matched enum
    let mut inferred_cases = Vec::new();

    let variants = match self.global.tctx.canonical_ty(cond.ty()) {
      Ty::EnumRef(_, id) => { self.global.find_inst(&id).unwrap_enum().1.clone() },
      _ => { return Err(CompileError::CannotMatchType(loc.clone(), cond.ty().clone())) }
    };

    for variant in variants.iter() {
      let (pattern, val) = pattern_map
        .remove(&variant.name())
        .ok_or_else(|| CompileError::MissingMatchCase(loc.clone()))?;
      match (variant, pattern) {
        (Variant::Unit(..), ResolvedPattern::Unit(..)) => {
          inferred_cases.push((Vec::new(), self.infer_rvalue(val)?));
        }
        (Variant::Struct(_, params), ResolvedPattern::Struct(_, bindings))
            if params.len() == bindings.len() => {
          for (index, binding) in bindings.iter().enumerate() {
            let (_, ty) = params.get(index).unwrap();
            self.bindings.insert(*binding, (binding_mut, ty.clone()));
          }
          inferred_cases.push((bindings.clone(), self.infer_rvalue(val)?));
        }
        _ => return Err(CompileError::IncorrectMatchCase(loc.clone()))
      };
    }

    // Make sure there are no cases left over
    if pattern_map.len() > 0 { return Err(CompileError::IncorrectMatchCase(loc.clone())) }

    // Unify case types
    let ty = if inferred_cases.len() > 0 {
      inferred_cases[1..]
        .iter()
        .map(|(_, val)| val.ty())
        .try_fold(inferred_cases[0].1.ty().clone(),
                  |a, b| self.global.tctx.unify(loc.clone(), &a, b))?
    } else {
      Ty::Unit
    };

    Ok(RValue::Match {
      ty,
      cond: Box::new(cond),
      cases: inferred_cases
    })
  }
}
