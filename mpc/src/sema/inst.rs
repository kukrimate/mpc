/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use crate::{CompileError, SourceLocation, parse::Repository};
use super::*;

pub(super) struct GlobalCtx<'repo, 'tctx> {
  // Parsed repository
  pub repo: &'repo Repository,
  // Type variable context
  pub tctx: &'tctx mut TVarCtx,
  // Checked definitions
  pub insts: HashMap<(DefId, Vec<Ty>), Inst>,
}

impl<'repo, 'tctx> GlobalCtx<'repo, 'tctx> {
  /// Lookup a parsed definition by its id
  pub fn parsed_def(&self, id: DefId) -> &'repo parse::Def {
    self.repo.parsed_def(id)
  }

  /// Lookup an instance by its id
  pub fn find_inst(&mut self, id: &(DefId, Vec<Ty>)) -> &Inst {
    for ((def_id, type_args), inst) in std::mem::replace(&mut self.insts, HashMap::new()).into_iter() {
      self.insts.insert((def_id, self.tctx.canonical_type_args(&type_args)), inst);
    }
    self.insts.get(id).unwrap()
  }

  pub fn inst_alias(&mut self, loc: SourceLocation, id: (DefId, Vec<Ty>), def: &parse::TypeDef) -> Result<Ty, CompileError> {
    // Verify type argument count
    if def.type_params.len() != id.1.len() {
      return Err(CompileError::IncorrectNumberOfTypeArguments(loc))
    }

    let mut def_ctx = DefCtx::new(self, def.parent_id);
    def_ctx.newscope();

    // Type parameters
    for (name, ty) in def.type_params.iter().zip(id.1.iter()) {
      def_ctx.define(*name, Sym::TParam(ty.clone()));
    }

    def_ctx.infer_ty(&def.ty)
  }

  pub fn inst_struct(&mut self, loc: SourceLocation, id: (DefId, Vec<Ty>), def: &parse::StructDef) -> Result<Ty, CompileError> {
    // Use existing definition if present
    if let Some(..) = self.insts.get(&id) {
      return Ok(Ty::StructRef(def.name, id));
    }

    // Verify type argument count
    if def.type_params.len() != id.1.len() {
      return Err(CompileError::IncorrectNumberOfTypeArguments(loc))
    }

    // Insert signature record
    self.insts.insert(id.clone(), Inst::Struct { name: def.name, params: None });

    // Instantiate body
    let mut def_ctx = DefCtx::new(self, def.parent_id);
    def_ctx.newscope();

    // Type parameters
    for (name, ty) in def.type_params.iter().zip(id.1.iter()) {
      def_ctx.define(*name, Sym::TParam(ty.clone()));
    }

    let params = def_ctx.infer_params(&def.params)?;
    self.insts.insert(id.clone(), Inst::Struct { name: def.name, params: Some(params) });

    Ok(Ty::StructRef(def.name, id))
  }

  pub fn inst_union(&mut self, loc: SourceLocation, id: (DefId, Vec<Ty>), def: &parse::UnionDef) -> Result<Ty, CompileError> {
    if let Some(..) = self.insts.get(&id) {
      return Ok(Ty::UnionRef(def.name, id));
    }

    if def.type_params.len() != id.1.len() {
      return Err(CompileError::IncorrectNumberOfTypeArguments(loc))
    }

    self.insts.insert(id.clone(), Inst::Union { name: def.name, params: None });

    let mut def_ctx = DefCtx::new(self, def.parent_id);
    def_ctx.newscope();

    // Type parameters
    for (name, ty) in def.type_params.iter().zip(id.1.iter()) {
      def_ctx.define(*name, Sym::TParam(ty.clone()));
    }

    let params = def_ctx.infer_params(&def.params)?;
    self.insts.insert(id.clone(), Inst::Union { name: def.name, params: Some(params) });

    Ok(Ty::UnionRef(def.name, id))
  }

  pub fn inst_enum(&mut self, loc: SourceLocation, id: (DefId, Vec<Ty>), def: &parse::EnumDef) -> Result<Ty, CompileError> {
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::EnumRef(def.name, id)); }

    if def.type_params.len() != id.1.len() {
      return Err(CompileError::IncorrectNumberOfTypeArguments(loc))
    }

    self.insts.insert(id.clone(), Inst::Enum { name: def.name, variants: def.variants.clone() });

    let mut def_ctx = DefCtx::new(self, def.parent_id);
    def_ctx.newscope();

    // Type parameters
    for (name, ty) in def.type_params.iter().zip(id.1.iter()) {
      def_ctx.define(*name, Sym::TParam(ty.clone()));
    }

    for variant_id in def.variants.iter() {
      match def_ctx.global.repo.parsed_def(*variant_id) {
        parse::Def::UnitVariant(def) => {
          def_ctx.global.insts.insert((*variant_id, id.1.clone()), Inst::UnitVariant {
            name: def.name,
            parent_enum: (def.parent_id, id.1.clone()),
            variant_index: def.variant_index
          });
        }
        parse::Def::StructVariant(def) => {
          let params = def_ctx.infer_params(&def.params)?;
          def_ctx.global.insts.insert((*variant_id, id.1.clone()), Inst::StructVariant {
            name: def.name,
            parent_enum: (def.parent_id, id.1.clone()),
            variant_index: def.variant_index,
            params
          });
        }
        _ => unreachable!()
      }
    }

    Ok(Ty::EnumRef(def.name, id))
  }

  pub fn inst_lvalue_const(&mut self, loc: SourceLocation, _id: DefId, def: &parse::ConstDef) -> Result<LValue, CompileError> {
    let mut def_ctx = DefCtx::new(self, def.parent_id);

    let ty = def_ctx.infer_ty(&def.ty)?;
    let val = def_ctx.infer_lvalue(&def.val)?;
    self.tctx.unify(loc, &ty, val.ty())?;

    Ok(val)
  }

  pub fn inst_rvalue_const(&mut self, loc: SourceLocation, _id: DefId, def: &parse::ConstDef) -> Result<RValue, CompileError> {
    let mut def_ctx = DefCtx::new(self, def.parent_id);

    let ty = def_ctx.infer_ty(&def.ty)?;
    let val = def_ctx.infer_rvalue(&def.val)?;
    self.tctx.unify(loc, &ty, val.ty())?;

    Ok(val)
  }

  pub fn inst_data(&mut self, loc: SourceLocation, id: DefId, def: &parse::DataDef) -> Result<LValue, CompileError> {
    let mut def_ctx = DefCtx::new(self, def.parent_id);

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

  pub fn inst_func_sig(&mut self, loc: SourceLocation, id: (DefId, Vec<Ty>), def: &parse::FuncDef) -> Result<RValue, CompileError> {
    // Check type argument count
    if def.type_params.len() != id.1.len() {
      return Err(CompileError::IncorrectNumberOfTypeArguments(loc))
    }

    // Crate context
    let mut def_ctx = DefCtx::new(self, def.parent_id);
    def_ctx.newscope();

    // Type parameters
    for (name, ty) in def.type_params.iter().zip(id.1.iter()) {
      def_ctx.define(*name, Sym::TParam(ty.clone()));
    }

    let mut param_tys = Vec::new();

    // Method receiver
    if let Some((Some((name, _)), ty)) = &def.receiver {
      let ty = def_ctx.infer_ty(ty)?;
      param_tys.push((*name, ty.clone()));
    }

    // Parameters
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
        locals: HashMap::new(),
        body: None,
      });
    }

    // Return reference to signature
    Ok(RValue::FuncRef {
      ty: Ty::Func(param_tys.clone(), false, Box::new(ret_ty.clone())),
      id
    })
  }

  pub fn inst_func_body(&mut self, loc: SourceLocation, id: (DefId, Vec<Ty>), def: &parse::FuncDef) -> Result<(), CompileError> {
    // Check type argument count
    if def.type_params.len() != id.1.len() {
      return Err(CompileError::IncorrectNumberOfTypeArguments(loc))
    }

    // Setup context
    let mut def_ctx = DefCtx::new(self, def.parent_id);
    def_ctx.newscope();

    // Type parameters
    for (name, ty) in def.type_params.iter().zip(id.1.iter()) {
      def_ctx.define(*name, Sym::TParam(ty.clone()));
    }

    let mut param_tys = Vec::new();
    let mut params = Vec::new();

    // Method receiver
    if let Some((Some((name, is_mut)), ty)) = &def.receiver {
      let ty = def_ctx.infer_ty(ty)?;
      let local_id = def_ctx.new_local_id();
      def_ctx.define(*name, Sym::Param(local_id));
      def_ctx.locals.insert(local_id, (*is_mut, ty.clone()));
      param_tys.push((*name, ty.clone()));
      params.push(local_id);
    }

    // Function parameters
    for (name, is_mut, ty) in def.params.iter() {
      let ty = def_ctx.infer_ty(ty)?;
      let local_id = def_ctx.new_local_id();
      def_ctx.define(*name, Sym::Param(local_id));
      def_ctx.locals.insert(local_id, (*is_mut, ty.clone()));
      param_tys.push((*name, ty.clone()));
      params.push(local_id);
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
      params,
      locals: def_ctx.locals,
      body: Some(body),
    };
    self.insts.insert(id.clone(), inst);

    Ok(())
  }

  pub fn inst_extern_data(&mut self, id: DefId, def: &parse::ExternDataDef) -> Result<LValue, CompileError> {
    let ty = DefCtx::new(self, def.parent_id).infer_ty(&def.ty)?;
    self.insts.insert((id, vec![]), Inst::ExternData { name: def.name, ty: ty.clone(), is_mut: def.is_mut });

    Ok(LValue::DataRef { ty, is_mut: def.is_mut, id })
  }

  pub fn inst_extern_func(&mut self, id: DefId, def: &parse::ExternFuncDef) -> Result<RValue, CompileError> {
    let mut def_ctx = DefCtx::new(self, def.parent_id);
    let ty = Ty::Func(def_ctx.infer_params(&def.params)?,
                      def.varargs,
                      Box::new(def_ctx.infer_ty(&def.ret_ty)?));
    self.insts.insert((id, vec![]), Inst::ExternFunc { name: def.name, ty: ty.clone() });

    Ok(RValue::FuncRef { ty, id: (id, vec![]) })
  }
}

pub(super) fn infer(repo: &Repository, tctx: &mut TVarCtx) -> Result<HashMap<(DefId, Vec<Ty>), Inst>, CompileError> {
  let mut ctx = GlobalCtx {
    repo,
    tctx,
    insts: HashMap::new(),
  };

  // Instantiate signatures for non-generic functions
  for (id, def) in repo.parsed_defs() {
    match def {
      parse::Def::Func(def) if def.type_params.len() == 0 => {
        ctx.inst_func_sig(def.loc.clone(), (*id, Vec::new()), def)?;
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
      let def = ctx.parsed_def(def_id).unwrap_func();
      ctx.inst_func_body(def.loc.clone(), (def_id, type_args), def)?;
    }
  }

  // Final de-duplication pass to get rid of type variables in instance IDs
  for ((def_id, type_args), inst) in std::mem::replace(&mut ctx.insts, HashMap::new()).into_iter() {
    ctx.insts.insert((def_id, ctx.tctx.final_type_args(&type_args)), inst);
  }

  Ok(ctx.insts)
}
