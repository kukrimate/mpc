/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use std::fmt::Debug;
use crate::parse::Repository;
use crate::resolve::*;
use super::*;

pub(super) fn infer(repo: &Repository, tctx: &mut TVarCtx) -> MRes<HashMap<(DefId, Vec<Ty>), Inst>> {
  let mut ctx = GlobalCtx {
    repo,
    tctx,
    insts: HashMap::new(),
  };

  // Instantiate signatures for non-generic functions
  for (id, def) in repo.resolved_defs.iter() {
    match def {
      ResolvedDef::Func(def) if def.type_params == 0 => {
        ctx.inst_func_sig((*id, Vec::new()))?;
      }
      _ => ()
    }
  }

  loop {
    // De-duplicate signatures after each pass
    // TODO: investigate if self can manage to overwrite an instantiated function
    // with just a signature
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
      ctx.inst_func_body((def_id, type_args))?;
    }
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

  fn inst_alias(&mut self, id: (DefId, Vec<Ty>)) -> MRes<Ty> {
    let def = self.resolved_def(id.0).unwrap_type();

    DefCtx::new(self, id.1).infer_ty(&def.ty)
  }

  fn inst_struct(&mut self, id: (DefId, Vec<Ty>)) -> MRes<Ty> {
    let def = self.resolved_def(id.0).unwrap_struct();
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::StructRef(def.name, id)); }

    self.insts.insert(id.clone(), Inst::Struct { name: def.name, params: None });
    if def.type_params != id.1.len() {
      return Err(Box::new(TypeError(format!("Incorrect number of type parameters"))))
    }
    let mut def_ctx = DefCtx::new(self, id.1.clone());
    let params = def_ctx.infer_params(&def.params)?;
    self.insts.insert(id.clone(), Inst::Struct { name: def.name, params: Some(params) });

    Ok(Ty::StructRef(def.name, id))
  }

  fn inst_union(&mut self, id: (DefId, Vec<Ty>)) -> MRes<Ty> {
    let def = self.resolved_def(id.0).unwrap_union();
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::UnionRef(def.name, id)); }

    self.insts.insert(id.clone(), Inst::Union { name: def.name, params: None });
    if def.type_params != id.1.len() {
      return Err(Box::new(TypeError(format!("Incorrect number of type parameters"))))
    }
    let mut def_ctx = DefCtx::new(self, id.1.clone());
    let params = def_ctx.infer_params(&def.params)?;
    self.insts.insert(id.clone(), Inst::Union { name: def.name, params: Some(params) });

    Ok(Ty::UnionRef(def.name, id))
  }

  fn inst_enum(&mut self, id: (DefId, Vec<Ty>)) -> MRes<Ty> {
    let def = self.resolved_def(id.0).unwrap_enum();
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::EnumRef(def.name, id)); }

    self.insts.insert(id.clone(), Inst::Enum { name: def.name, variants: None });
    if def.type_params != id.1.len() {
      return Err(Box::new(TypeError(format!("Incorrect number of type parameters"))))
    }

    let mut def_ctx = DefCtx::new(self, id.1.clone());
    let variants = def_ctx.infer_variants(&def.variants)?;
    self.insts.insert(id.clone(), Inst::Enum { name: def.name, variants: Some(variants) });

    Ok(Ty::EnumRef(def.name, id))
  }

  fn inst_data(&mut self, id: DefId) -> MRes<LValue> {
    let def = self.resolved_def(id).unwrap_data();

    let mut def_ctx = DefCtx::new(self, Vec::new());

    let ty = def_ctx.infer_ty(&def.ty)?;
    let init = def_ctx.infer_rvalue(&def.init)?;
    self.tctx.unify(&ty, init.ty())?;

    self.insts.insert((id, vec![]), Inst::Data {
      name: def.name,
      ty: ty.clone(),
      is_mut: def.is_mut,
      init: consteval(&init)?,
    });

    Ok(LValue::DataRef { ty, is_mut: def.is_mut, id })
  }

  fn inst_func_sig(&mut self, id: (DefId, Vec<Ty>)) -> MRes<RValue> {
    let def = self.resolved_def(id.0).unwrap_func();

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
    self.insts.insert(id.clone(), Inst::Func {
      name: def.name,
      ty: Ty::Func(param_tys.clone(), false, Box::new(ret_ty.clone())),
      params: Vec::new(),
      locals: Vec::new(),
      bindings: Vec::new(),
      body: None,
    });

    // Return reference to signature
    Ok(RValue::FuncRef {
      ty: Ty::Func(param_tys.clone(), false, Box::new(ret_ty.clone())),
      id
    })
  }

  fn inst_func_body(&mut self, id: (DefId, Vec<Ty>)) -> MRes<()> {
    let def = self.resolved_def(id.0).unwrap_func();

    // check type argument count
    if def.type_params != id.1.len() {
      return Err(Box::new(TypeError(format!("Incorrect number of type parameters"))));
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

    // Local variables
    for (is_mut, ty) in def.locals.iter() {
      let ty = if let Some(ty) = ty {
        def_ctx.infer_ty(ty)?
      } else {
        def_ctx.global.tctx.tvar(Ty::BoundAny)
      };
      def_ctx.locals.push((*is_mut, ty));
    }

    // Return type
    let ret_ty = def_ctx.infer_ty(&def.ret_ty)?;
    def_ctx.ret_ty = Some(ret_ty.clone());

    // Body
    let body = def_ctx.infer_rvalue(&def.body)?;
    def_ctx.global.tctx.unify(&ret_ty, body.ty())?;

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

  fn inst_extern_data(&mut self, id: DefId) -> MRes<LValue> {
    let def = self.resolved_def(id).unwrap_extern_data();

    let ty = DefCtx::new(self, Vec::new()).infer_ty(&def.ty)?;
    self.insts.insert((id, vec![]), Inst::ExternData { name: def.name, ty: ty.clone(), is_mut: def.is_mut });

    Ok(LValue::DataRef { ty, is_mut: def.is_mut, id })
  }

  fn inst_extern_func(&mut self, id: DefId) -> MRes<RValue> {
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
  bindings: Vec<(IsMut, Ty)>,
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
      bindings: Vec::new(),
      ret_ty: None,
      loop_ty: Vec::new(),
    }
  }


  /// Infer the semantic form of a type expression
  fn infer_ty(&mut self, ty: &ResolvedTy) -> MRes<Ty> {
    use ResolvedTy::*;
    Ok(match ty {
      Bool => Ty::Bool,
      Uint8 => Ty::Uint8,
      Int8 => Ty::Int8,
      Uint16 => Ty::Uint16,
      Int16 => Ty::Int16,
      Uint32 => Ty::Uint32,
      Int32 => Ty::Int32,
      Uint64 => Ty::Uint64,
      Int64 => Ty::Int64,
      Uintn => Ty::Uintn,
      Intn => Ty::Intn,
      Float => Ty::Float,
      Double => Ty::Double,
      TParam(index) => {
        self.type_args[*index].clone()
      }
      AliasRef(def_id, type_args) => {
        let type_args = self.infer_type_args(type_args)?;
        self.global.inst_alias((*def_id, type_args))?
      }
      StructRef(def_id, type_args) => {
        let type_args = self.infer_type_args(type_args)?;
        self.global.inst_struct((*def_id, type_args))?
      }
      UnionRef(def_id, type_args) => {
        let type_args = self.infer_type_args(type_args)?;
        self.global.inst_union((*def_id, type_args))?
      }
      EnumRef(def_id, type_args) => {
        let type_args = self.infer_type_args(type_args)?;
        self.global.inst_enum((*def_id, type_args))?
      }
      Ptr(is_mut, base_ty) => {
        Ty::Ptr(*is_mut, Box::new(self.infer_ty(base_ty)?))
      }
      Func(params, ret_ty) => {
        Ty::Func(self.infer_params(params)?,
                 false, Box::new(self.infer_ty(ret_ty)?))
      }
      Arr(elem_cnt_expr, elem_ty) => {
        let elem_cnt = self.infer_rvalue(elem_cnt_expr)
          .and_then(|rvalue| consteval_index(&rvalue))?;
        Ty::Arr(elem_cnt, Box::new(self.infer_ty(elem_ty)?))
      }
      Unit => {
        Ty::Unit
      }
      Tuple(params) => {
        Ty::Tuple(self.infer_params(params)?)
      }
    })
  }

  fn infer_params(&mut self, params: &Vec<(RefStr, ResolvedTy)>) -> MRes<Vec<(RefStr, Ty)>> {
    let mut result = vec![];
    for (name, ty) in params {
      result.push((*name, self.infer_ty(ty)?));
    }
    Ok(result)
  }

  fn infer_variants(&mut self, variants: &Vec<ResolvedVariant>) -> MRes<Vec<Variant>> {
    let mut result = vec![];
    for variant in variants.iter() {
      result.push(match variant {
        ResolvedVariant::Unit(name) => {
          Variant::Unit(*name)
        }
        ResolvedVariant::Struct(name, params) => {
          Variant::Struct(*name, self.infer_params(params)?)
        }
      })
    }
    Ok(result)
  }

  fn infer_type_args(&mut self, type_args:&Vec<ResolvedTy>) -> MRes<Vec<Ty>> {
    type_args
      .iter()
      .map(|ty| self.infer_ty(ty))
      .monadic_collect()
  }

  /// Infer the semantic form of an expression in an lvalue context
  fn infer_lvalue(&mut self, expr: &ResolvedExpr) -> MRes<LValue> {
    use ResolvedExpr::*;

    Ok(match expr {
      ConstRef(def_id) => {
        let def = self.global.resolved_def(*def_id).unwrap_const();
        self.infer_lvalue(&def.val)?
      }
      DataRef(def_id) => self.global.inst_data(*def_id)?,
      ExternDataRef(def_id) => self.global.inst_extern_data(*def_id)?,
      ParamRef(index) => LValue::ParamRef {
        ty: self.params[*index].1.clone(),
        is_mut: self.params[*index].0,
        index: *index
      },
      LetRef(index) => LValue::LetRef {
        ty: self.locals[*index].1.clone(),
        is_mut: self.locals[*index].0,
        index: *index
      },
      BindingRef(index) => LValue::BindingRef {
        ty: self.bindings[*index].1.clone(),
        is_mut: self.bindings[*index].0,
        index: *index
      },
      TupleLit(resolved_fields) => {
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
      ArrayLit(elements) => {
        let elem_ty = self.global.tctx.tvar(Ty::BoundAny);
        let elements = elements.iter()
          .map(|element| self.infer_rvalue(element))
          .monadic_collect()?;
        for element in elements.iter() {
          self.global.tctx.unify(&elem_ty, element.ty())?;
        }
        LValue::ArrayLit {
          ty: Ty::Arr(elements.len(), Box::new(elem_ty)),
          is_mut: IsMut::No,
          elements
        }
      }
      StructLit(def_id, fields) => {
        let def = self.global.resolved_def(*def_id).unwrap_struct();
        let type_args: Vec<Ty> = (0..def.type_params)
          .map(|_| self.global.tctx.tvar(Ty::BoundAny))
          .collect();
        let ty = self.global.inst_struct((*def_id, type_args.clone()))?;
        let (_, params) = self.global.insts.get(&(*def_id, type_args)).unwrap().unwrap_struct();
        LValue::StructLit {
          ty,
          is_mut: IsMut::No,
          fields: self.infer_args(&params.clone(), fields)?
        }
      }
      UnionLit(def_id, name, val) => {
        let val = self.infer_rvalue(val)?;

        // Instantiate union type
        let def = self.global.resolved_def(*def_id).unwrap_union();
        let type_args: Vec<Ty> = (0..def.type_params)
          .map(|_| self.global.tctx.tvar(Ty::BoundAny))
          .collect();
        let ty = self.global.inst_union((*def_id, type_args.clone()))?;
        let (_, params) = self.global.insts.get(&(*def_id, type_args)).unwrap().unwrap_union();

        // Find which field the value belongs to
        if name.borrow_rs() == "" && params.len() > 0 {
          self.global.tctx.unify(val.ty(), &params[0].1)?;
        } else if let Some((_, param_ty)) = lin_search(&params, name) {
          self.global.tctx.unify(val.ty(), param_ty)?;
        } else {
          Err(Box::new(TypeError(format!("Unknown union field {}", name))))?
        }

        LValue::UnionLit {
          ty,
          is_mut: IsMut::No,
          field: val
        }
      }
      UnitVariantLit(def_id, index) => {
        let def = self.global.resolved_def(*def_id).unwrap_enum();
        let type_args: Vec<Ty> = (0..def.type_params)
          .map(|_| self.global.tctx.tvar(Ty::BoundAny))
          .collect();
        let ty = self.global.inst_enum((*def_id, type_args.clone()))?;
        let (_, variants) = self.global.insts.get(&(*def_id, type_args)).unwrap().unwrap_enum();
        match &variants[*index] {
          Variant::Unit(..) => (),
          Variant::Struct(..) => Err(Box::new(TypeError(format!("Expected arguments for struct variant"))))?
        }
        LValue::UnitVariantLit { ty, is_mut: IsMut::No, index: *index }
      }
      StructVariantLit(def_id, index, fields) => {
        let def = self.global.resolved_def(*def_id).unwrap_enum();
        let type_args: Vec<Ty> = (0..def.type_params)
          .map(|_| self.global.tctx.tvar(Ty::BoundAny))
          .collect();
        let ty = self.global.inst_enum((*def_id, type_args.clone()))?;
        let (_, variants) = self.global.insts.get(&(*def_id, type_args)).unwrap().unwrap_enum();
        match &variants[*index] {
          Variant::Unit(..) => Err(Box::new(TypeError(format!("Unexpected arguments for unit variant"))))?,
          Variant::Struct(_, params) => {
            LValue::StructVariantLit {
              ty,
              is_mut: IsMut::No,
              index: *index,
              fields: self.infer_args(&params.clone(), fields)?
            }
          }
        }
      }
      Str(val) => {
        let ty = Ty::Arr(val.len(), Box::new(self.global.tctx.tvar(Ty::BoundInt)));
        LValue::StrLit { ty, is_mut: IsMut::No, val: val.clone() }
      }
      Dot(arg, name) => {
        self.infer_dot(arg, *name)?
      }
      Index(arg, idx) => {
        self.infer_index(arg, idx)?
      }
      Ind(arg) => {
        self.infer_ind(arg)?
      }
      expr => return Err(Box::new(TypeError(format!("Expected lvalue instead of {:?}", expr))))
    })
  }

  /// Infer the type of a member access expression
  fn infer_dot(&mut self, arg: &ResolvedExpr, name: RefStr) -> MRes<LValue> {
    // Infer argument type
    let arg = self.infer_lvalue(arg)?;

    'error: loop {
      // Find parameter list
      let ty = self.global.tctx.cur_bound(arg.ty());

      let (is_stru, params) = match &ty {
        Ty::StructRef(_, id) => {
          if let Inst::Struct { params: Some(params), .. }
            = self.global.insts.get(id).unwrap() { (true, params) } else { unreachable!() }
        }
        Ty::UnionRef(_, id) => {
          if let Inst::Union { params: Some(params), .. }
            = self.global.insts.get(id).unwrap() { (false, params) } else { unreachable!() }
        }
        Ty::Tuple(params) => (true, params),
        _ => break 'error
      };

      // Find parameter
      let (idx, param_ty) = match lin_search(params, &name) {
        Some(val) => val,
        None => break 'error
      };

      return if is_stru {
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

    Err(Box::new(TypeError(format!("Type {:?} has no field named {}", arg.ty(), name))))
  }

  /// Infer the type of an array index expression
  fn infer_index(&mut self, arg: &ResolvedExpr, idx: &ResolvedExpr) -> MRes<LValue> {
    // Infer array type
    let arg = self.infer_lvalue(arg)?;

    // Find element type
    let ty = self.global.tctx.cur_bound(arg.ty());
    let elem_ty = match &ty {
      Ty::Arr(_, elem_ty) => &**elem_ty,
      _ => return Err(Box::new(TypeError(format!("Cannot index type {:?}", arg.ty()))))
    };

    // Check index type
    let idx = self.infer_rvalue(idx)?;
    self.global.tctx.unify(&Ty::Uintn, idx.ty())?;

    Ok(LValue::Index {
      ty: elem_ty.clone(),
      is_mut: arg.is_mut(),
      arg: Box::new(arg),
      idx: Box::new(idx),
    })
  }

  /// Infer the type of a pointer indirection expression
  fn infer_ind(&mut self, arg: &ResolvedExpr) -> MRes<LValue> {
    // Infer pointer type
    let arg = self.infer_rvalue(arg)?;

    // Find base type
    let ty = self.global.tctx.cur_bound(arg.ty());
    let (is_mut, base_ty) = match &ty {
      Ty::Ptr(is_mut, base_ty) => (*is_mut, &**base_ty),
      _ => return Err(Box::new(
        TypeError(format!("Cannot dereference type {:?}", arg.ty()))))
    };

    Ok(LValue::Ind {
      ty: base_ty.clone(),
      is_mut,
      arg: Box::new(arg),
    })
  }

  /// Infer the semantic form of an expression in an rvalue context
  fn infer_rvalue(&mut self, expr: &ResolvedExpr) -> MRes<RValue> {
    use ResolvedExpr::*;

    Ok(match expr {
      ConstRef(def_id) => {
        let def = self.global.resolved_def(*def_id).unwrap_const();
        self.infer_rvalue(&def.val)?
      }
      FuncRef(def_id) => {
        let def = self.global.resolved_def(*def_id).unwrap_func();
        let type_args: Vec<Ty> = (0..def.type_params)
          .map(|_| self.global.tctx.tvar(Ty::BoundAny))
          .collect();
        self.global.inst_func_sig((*def_id, type_args))?
      },
      ExternFuncRef(def_id) => self.global.inst_extern_func(*def_id)?,
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
      CStr(val) => {
        RValue::CStr { ty: Ty::Ptr(IsMut::No, Box::new(Ty::Int8)), val: val.clone() }
      }
      Nil => {
        RValue::Nil { ty: Ty::Ptr(IsMut::Yes, Box::new(self.global.tctx.tvar(Ty::BoundAny))) }
      }
      Bool(val) => {
        RValue::Bool { ty: Ty::Bool, val: *val }
      }
      Int(val) => {
        RValue::Int { ty: self.global.tctx.tvar(Ty::BoundInt), val: *val }
      }
      Flt(val) => {
        RValue::Flt { ty: self.global.tctx.tvar(Ty::BoundFlt), val: *val }
      }
      Unit => {
        RValue::Unit { ty: Ty::Unit }
      }
      Call(called, args) => {
        self.infer_call(called, args)?
      }
      Adr(arg) => {
        let arg = self.infer_lvalue(arg)?;
        RValue::Adr {
          ty: Ty::Ptr(arg.is_mut(), Box::new(arg.ty().clone())),
          arg: Box::new(arg),
        }
      }
      Un(op, arg) => {
        let arg = self.infer_rvalue(arg)?;
        RValue::Un {
          ty: self.infer_un(*op, arg.ty())?,
          op: *op,
          arg: Box::new(arg),
        }
      }
      LNot(arg) => {
        let arg = self.infer_rvalue(arg)?;
        self.global.tctx.unify(&Ty::Bool, arg.ty())?;
        RValue::LNot { ty: Ty::Bool, arg: Box::new(arg) }
      }
      Cast(arg, ty) => {
        let arg = self.infer_rvalue(arg)?;
        let ty = self.infer_ty(ty)?;
        // FIXME: actually check if the type conversion is valid or not
        RValue::Cast { ty, arg: Box::new(arg) }
      }
      Bin(op, lhs, rhs) => {
        let lhs = self.infer_rvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        let ty = self.infer_bin(*op, lhs.ty(), rhs.ty())?;
        RValue::Bin { ty, op: *op, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      LAnd(lhs, rhs) => {
        let lhs = self.infer_rvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        self.global.tctx.unify(&Ty::Bool, lhs.ty())?;
        self.global.tctx.unify(&Ty::Bool, rhs.ty())?;
        RValue::LAnd { ty: Ty::Bool, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      LOr(lhs, rhs) => {
        let lhs = self.infer_rvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        self.global.tctx.unify(&Ty::Bool, lhs.ty())?;
        self.global.tctx.unify(&Ty::Bool, rhs.ty())?;
        RValue::LOr { ty: Ty::Bool, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Block(parsed_body) => {
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
      As(lhs, rhs) => {
        // Infer argument types
        let lhs = self.infer_lvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        self.global.tctx.unify(lhs.ty(), rhs.ty())?;

        // Make sure lhs is mutable
        match lhs.is_mut() {
          IsMut::Yes => (),
          _ => return Err(Box::new(
            TypeError(format!("Cannot assign to immutable location {:?}", lhs)))),
        };

        RValue::As { ty: Ty::Unit, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Rmw(op, lhs, rhs) => {
        // Infer and check argument types
        let lhs = self.infer_lvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        self.infer_bin(*op, lhs.ty(), rhs.ty())?;

        // Make sure lhs is mutable
        match lhs.is_mut() {
          IsMut::Yes => (),
          _ => return Err(Box::new(
            TypeError(format!("Cannot assign to immutable location {:?}", lhs)))),
        };

        RValue::Rmw { ty: Ty::Unit, op: *op, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Continue => {
        // Can only have continue inside a loop
        match self.loop_ty.last() {
          Some(..) => (),
          None => return Err(Box::new(
            TypeError(format!("Continue outside loop")))),
        };

        RValue::Continue { ty: self.global.tctx.tvar(Ty::BoundAny) }
      }
      Break(arg) => {
        let arg = self.infer_rvalue(&*arg)?;

        // Can only have break inside a loop
        let loop_ty = match self.loop_ty.last() {
          Some(loop_ty) => loop_ty.clone(),
          None => return Err(Box::new(
            TypeError(format!("Break outside loop")))),
        };

        // Unify function return type with the returned value's type
        self.global.tctx.unify(&loop_ty, arg.ty())?;

        RValue::Break { ty: self.global.tctx.tvar(Ty::BoundAny), arg: Box::new(arg) }
      }
      Return(arg) => {
        let arg = self.infer_rvalue(&*arg)?;

        // Can only have return inside a function
        let ret_ty = match self.ret_ty.as_ref() {
          Some(ret_ty) => ret_ty.clone(),
          None => return Err(Box::new(TypeError(format!("Return outside function")))),
        };

        // Unify function return type with the returned value's type
        self.global.tctx.unify(&ret_ty, arg.ty())?;

        RValue::Return { ty: self.global.tctx.tvar(Ty::BoundAny), arg: Box::new(arg) }
      }
      Let(index, init) => {
        let init = if let Some(init) = init {
          let init = self.infer_rvalue(init)?;
          self.global.tctx.unify(&self.locals[*index].1, init.ty())?;
          Some(Box::new(init))
        } else {
          None
        };

        RValue::Let { ty: Ty::Unit, index: *index, init }
      }
      If(cond, tbody, ebody) => {
        let cond = self.infer_rvalue(cond)?;
        self.global.tctx.unify(&Ty::Bool, cond.ty())?;

        let tbody = self.infer_rvalue(tbody)?;
        let ebody = self.infer_rvalue(ebody)?;
        self.global.tctx.unify(tbody.ty(), ebody.ty())?;

        RValue::If {
          ty: tbody.ty().clone(),
          cond: Box::new(cond),
          tbody: Box::new(tbody),
          ebody: Box::new(ebody),
        }
      }
      While(cond, body) => {
        let cond = self.infer_rvalue(cond)?;
        self.global.tctx.unify(&Ty::Bool, cond.ty())?;

        self.loop_ty.push(Ty::Unit);
        let body = self.infer_rvalue(body)?;
        let ty = self.loop_ty.pop().unwrap();

        RValue::While {
          ty,
          cond: Box::new(cond),
          body: Box::new(body),
        }
      }
      Loop(body) => {
        self.loop_ty.push(self.global.tctx.tvar(Ty::BoundAny));
        let body = self.infer_rvalue(body)?;
        let ty = self.loop_ty.pop().unwrap();

        RValue::Loop {
          ty,
          body: Box::new(body),
        }
      }
      Match(cond, cases) => {
        self.infer_match(cond, cases)?
      }
    })
  }

  fn infer_call(&mut self, called: &ResolvedExpr, args: &Vec<(RefStr, ResolvedExpr)>) -> MRes<RValue> {
    // Infer function type
    let called_expr = self.infer_rvalue(called)?;

    // Find parameter list and return type
    let called_ty = self.global.tctx.cur_bound(called_expr.ty());
    let (params, va, ret_ty) = match &called_ty {
      Ty::Func(params, va, ret_ty) => (params, *va, &**ret_ty),
      _ => return Err(Box::new(TypeError(format!("Cannot call type {:?}", called_expr.ty()))))
    };

    // Validate argument count
    if args.len() < params.len() {
      return Err(Box::new(TypeError(format!("Not enough arguments for {:?}", called_expr.ty()))));
    }
    if va == false && args.len() > params.len() {
      return Err(Box::new(TypeError(format!("Too many arguments for {:?}", called_expr.ty()))));
    }

    let args = self.infer_args(params, args)?;

    Ok(RValue::Call {
      ty: ret_ty.clone(),
      func: Box::new(called_expr),
      args,
    })
  }

  fn infer_args(&mut self, params: &[(RefStr, Ty)], args: &[(RefStr, ResolvedExpr)]) -> MRes<Vec<RValue>> {
    let mut nargs = vec![];
    let mut params_iter = params.iter();

    for (arg_name, arg_val) in args.iter() {
      // Infer type of argument value
      let arg_val = self.infer_rvalue(arg_val)?;
      // If there is a corresponding parameter name and type, check it
      if let Some((param_name, param_ty)) = params_iter.next() {
        if *arg_name != RefStr::new("") && arg_name != param_name {
          return Err(Box::new(TypeError(format!("Incorrect argument label {}", arg_name))));
        }
        self.global.tctx.unify(arg_val.ty(), param_ty)?;
      }
      // Append checked argument
      nargs.push(arg_val);
    }

    Ok(nargs)
  }

  fn infer_un(&mut self, op: UnOp, arg: &Ty) -> MRes<Ty> {
    // Check argument type
    match op {
      UnOp::UPlus | UnOp::UMinus => {
        self.global.tctx.unify(arg, &Ty::BoundNum)
      }
      UnOp::Not => {
        self.global.tctx.unify(arg, &Ty::BoundInt)
      }
    }
  }

  fn infer_bin(&mut self, op: BinOp, lhs: &Ty, rhs: &Ty) -> MRes<Ty> {
    // Check argument types and infer result type
    match op {
      // Both arguments must have matching numeric types
      // Result has the same type as the arguments
      BinOp::Mul | BinOp::Div | BinOp::Add | BinOp::Sub => {
        self.global.tctx.unify(lhs, &Ty::BoundNum)?;
        self.global.tctx.unify(lhs, rhs)
      }

      // Both arguments must have matching integer types
      // Result has the same type as the arguments
      BinOp::Mod | BinOp::And | BinOp::Xor | BinOp::Or => {
        self.global.tctx.unify(lhs, &Ty::BoundInt)?;
        self.global.tctx.unify(lhs, rhs)
      }

      // Both arguments must have integer types
      // Result has the left argument's type
      BinOp::Lsh | BinOp::Rsh => {
        self.global.tctx.unify(rhs, &Ty::BoundInt)?;
        self.global.tctx.unify(lhs, &Ty::BoundInt)
      }

      BinOp::Eq | BinOp::Ne => {
        self.global.tctx.unify(lhs, &Ty::BoundEq)?;
        self.global.tctx.unify(lhs, rhs)?;
        Ok(Ty::Bool)
      }

      BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
        self.global.tctx.unify(lhs, &Ty::BoundNum)?;
        self.global.tctx.unify(lhs, rhs)?;
        Ok(Ty::Bool)
      }
    }
  }

  fn infer_match(&mut self, cond: &ResolvedExpr, cases: &[(Option<usize>, RefStr, ResolvedExpr)]) -> MRes<RValue> {
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
    // NOTE: the match below accomplishes the hack described above
    let binding_mut = match &cond {
      RValue::Load { arg, .. } => arg.is_mut(),
      _ => IsMut::No
    };
    let variants = match self.global.tctx.cur_bound(cond.ty()) {
      Ty::EnumRef(_, id) => {
        if let Inst::Enum { variants: Some(variants), .. }
          = self.global.insts.get(&id).unwrap() { variants.clone() } else { unreachable!() }
      },
      _ => Err(Box::new(TypeError(format!("Cannot match on non-enum type {:?}", cond.ty()))))?
    };

    // Create lookup table for cases
    let mut case_lookup: HashMap<RefStr, (Option<usize>, &ResolvedExpr)> = HashMap::new();

    for (binding, variant, val) in cases.iter() {
      // Check for duplicate case
      if case_lookup.contains_key(variant) {
        Err(Box::new(TypeError(format!("Duplicate match case"))))?
      }
      // Insert case
      case_lookup.insert(*variant, (*binding, val));
    }

    // Infer case for each variant
    let mut inferred_cases = Vec::new();

    for variant in variants.into_iter() {
      let (name, ty) = match variant {
        Variant::Unit(name) => (name, Ty::Unit),
        Variant::Struct(name, params) => (name, Ty::Tuple(params)),
      };

      let (binding, val) = case_lookup
        .remove(&name)
        .ok_or_else(|| TypeError(format!("Missing match case for variant {}", name)))?;

      if let Some(binding) = binding {
        assert_eq!(self.bindings.len(), binding);
        self.bindings.push((binding_mut, ty));
      }

      inferred_cases.push((binding, self.infer_rvalue(val)?));
    }

    // Make sure there are no cases left over
    if case_lookup.len() > 0 {
      Err(Box::new(TypeError(format!("Match case for unknown variant"))))?
    }

    // Unify case types
    let ty = if inferred_cases.len() > 0 {
      inferred_cases[1..]
        .iter()
        .map(|(_, val)| val.ty())
        .try_fold(inferred_cases[0].1.ty().clone(),
                  |a, b| self.global.tctx.unify(&a, b))?
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

/// Errors
#[derive(Debug)]
struct TypeError(String);

impl fmt::Display for TypeError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.0)
  }
}

impl error::Error for TypeError {}
