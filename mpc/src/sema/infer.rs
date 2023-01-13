/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use std::fmt::Debug;
use crate::parse::Repository;
use super::*;

pub(super) fn infer(repo: &Repository, tctx: &mut TVarCtx) -> MRes<HashMap<(DefId, Vec<Ty>), Inst>> {
  let mut ctx = CheckCtx {
    repo,
    tctx,
    insts: HashMap::new(),
    parent_ids: Vec::new(),
    scopes: Vec::new(),
    ret_ty: Vec::new(),
    loop_ty: Vec::new(),
  };

  // Instantiate signatures for non-generic functions
  for (id, def) in repo.defs.iter() {
    match def {
      parse::Def::Func(def) if def.type_params.len() == 0 => {
        ctx.inst_func_sig((*id, vec![]), def)?;
      }
      _ => ()
    }
  }

  loop {
    // De-duplicate signatures after each pass
    // TODO: investigate if this can manage to overwrite an instantiated function
    // with just a signature
    for ((def_id, type_args), inst) in std::mem::replace(&mut ctx.insts, HashMap::new()).into_iter() {
      ctx.insts.insert((def_id, ctx.tctx.root_type_args(&type_args)), inst);
    }

    // Collect function signatures whose bodies need to be instantiated
    let mut queue = vec![];
    for ((def_id, type_args), inst) in ctx.insts.iter() {
      if let Inst::Func { body: None, .. } = inst {
        queue.push((*def_id, type_args.clone()));
      }
    }

    if queue.len() == 0 { break }

    for (def_id, type_args) in queue.into_iter() {
      let parsed_func = if let parse::Def::Func(def) = ctx.parsed_def(def_id) { def } else { unreachable!() };
      ctx.inst_func_body((def_id, type_args), parsed_func)?;
    }
  }

  Ok(ctx.insts)
}

struct CheckCtx<'a> {
  repo: &'a Repository,

  // Type variable context
  tctx: &'a mut TVarCtx,

  // Checked definitions
  insts: HashMap<(DefId, Vec<Ty>), Inst>,

  // Definitions currently being checked
  parent_ids: Vec<DefId>,

  // Symbol table
  scopes: Vec<HashMap<RefStr, Sym>>,

  // Function return type
  ret_ty: Vec<Ty>,

  // Loop types
  loop_ty: Vec<Ty>,
}

#[derive(Clone)]
enum Sym {
  Def(DefId),
  TParam(Ty)
}

impl<'a> CheckCtx<'a> {
  fn inst_struct(&mut self, id: (DefId, Vec<Ty>), def: &parse::StructDef) -> MRes<Ty> {
    // Try to find previous matching copy
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::Inst(def.name, id)) }

    self.with_scope_of(id.0, |this| {
      this.insts.insert(id.clone(), Inst::Struct { name: def.name, params: None });

      // FIXME: bring type params into scope
      // if def.type_params.len() != id.1.len() {
      //   return Err(Box::new(TypeError(format!("Incorrect number of type parameters"))))
      // }
      let params = this.infer_params(&def.params)?;
      this.insts.insert(id.clone(), Inst::Struct { name: def.name, params: Some(params) });

      Ok(Ty::Inst(def.name, id))
    })
  }

  fn inst_union(&mut self, id: (DefId, Vec<Ty>), def: &parse::UnionDef) -> MRes<Ty> {
    // Try to find previous matching copy
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::Inst(def.name, id)) }

    self.with_scope_of(id.0, |this| {
      this.insts.insert(id.clone(), Inst::Union { name: def.name, params: None });

      let params = this.infer_params(&def.params)?;
      this.insts.insert(id.clone(), Inst::Union { name: def.name, params: Some(params) });

      Ok(Ty::Inst(def.name, id))
    })
  }

  fn inst_enum(&mut self, id: (DefId, Vec<Ty>), def: &parse::EnumDef) -> MRes<Ty> {
    // Try to find previous matching copy
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::Inst(def.name, id)) }

    self.with_scope_of(id.0, |this| {
      this.insts.insert(id.clone(), Inst::Enum { name: def.name, variants: None });

      let variants = this.infer_variants(&def.variants)?;
      this.insts.insert(id.clone(), Inst::Enum { name: def.name, variants: Some(variants) });

      Ok(Ty::Inst(def.name, id))
    })
  }

  fn infer_params(&mut self, params: &Vec<(RefStr, parse::Ty)>) -> MRes<Vec<(RefStr, Ty)>> {
    let mut result = vec![];
    for (name, ty) in params {
      result.push((*name, self.infer_ty(ty)?));
    }
    Ok(result)
  }

  fn infer_variants(&mut self, variants: &Vec<parse::Variant>) -> MRes<Vec<Variant>> {
    let mut result = vec![];
    for variant in variants.iter() {
      result.push(match variant {
        parse::Variant::Unit(name) => {
          Variant::Unit(*name)
        }
        parse::Variant::Struct(name, params) => {
          Variant::Struct(*name, self.infer_params(params)?)
        }
      })
    }
    Ok(result)
  }

  fn inst_data(&mut self, id: DefId, def: &parse::DataDef) -> MRes<LValue> {
    self.with_scope_of(id, |this| {
      let ty = this.infer_ty(&def.ty)?;
      let init = this.infer_rvalue(&def.init)?;
      this.tctx.unify(&ty, init.ty())?;
      this.insts.insert((id, vec![]), Inst::Data {
        name: def.name,
        ty: ty.clone(),
        is_mut: def.is_mut,
        init: consteval(&init)?
      });

      Ok(LValue::DataRef { ty, is_mut: def.is_mut, id })
    })
  }

  fn inst_func_sig(&mut self, id: (DefId, Vec<Ty>), def: &parse::FuncDef) -> MRes<RValue> {
    self.with_scope_of(id.0, |this| {
      // Try to find existing instance first
      if let Some(Inst::Func { ty, .. }) = this.insts.get(&id) {
        return Ok(RValue::FuncRef { ty: ty.clone(), id })
      }

      this.newscope();

      // Type parameters
      if def.type_params.len() != id.1.len() {
        return Err(Box::new(TypeError(format!("Incorrect number of type parameters"))))
      }
      for (name, ty) in def.type_params.iter().zip(id.1.iter()) {
        this.define(*name, Sym::TParam(ty.clone()));
      }

      // Parameters
      let mut param_tys = vec![];
      for def_id in def.params.iter() {
        let def = this.repo.param_by_id(*def_id);
        param_tys.push((def.name, this.infer_ty(&def.ty)?));
      }

      // Return type
      let ret_ty = this.infer_ty(&def.ret_ty)?;

      this.popscope();

      // Insert signature record
      this.insts.insert(id.clone(), Inst::Func {
        name: def.name,
        ty: Ty::Func(param_tys.clone(), false, Box::new(ret_ty.clone())),
        params: Vec::new(),
        body: None
      });

      // Return reference to signature
      Ok(RValue::FuncRef {
        ty: Ty::Func(param_tys.clone(), false, Box::new(ret_ty.clone())),
        id
      })
    })
  }

  fn inst_func_body(&mut self, id: (DefId, Vec<Ty>), def: &parse::FuncDef) -> MRes<()> {
    self.with_scope_of(id.0, |this| {
      // Create environment
      this.newscope();

      // Type params
      if def.type_params.len() != id.1.len() {
        return Err(Box::new(TypeError(format!("Incorrect number of type parameters"))))
      }
      for (name, ty) in def.type_params.iter().zip(id.1.iter()) {
        this.define(*name, Sym::TParam(ty.clone()));
      }

      // Regular parameters
      let mut param_ids = vec![];
      let mut param_tys = vec![];
      for def_id in def.params.iter() {
        let def = this.repo.param_by_id(*def_id);
        param_ids.push(*def_id);
        let ty = this.infer_ty(&def.ty)?;
        param_tys.push((def.name, ty.clone()));
        this.insts.insert((*def_id, vec![]), Inst::Param {
          name: def.name,
          is_mut: def.is_mut,
          ty
        });
        this.define(def.name, Sym::Def(*def_id));
      }

      // Return type
      let ret_ty = this.infer_ty(&def.ret_ty)?;

      // Body
      this.ret_ty.push(ret_ty.clone());
      let body = this.infer_rvalue(&def.body)?;
      this.tctx.unify(&ret_ty, body.ty())?;
      this.ret_ty.pop().unwrap();

      this.popscope();

      // Insert body
      this.insts.insert(id.clone(), Inst::Func {
        name: def.name,
        ty: Ty::Func(param_tys.clone(), false, Box::new(ret_ty.clone())),
        params: param_ids,
        body: Some(body)
      });

      Ok(())
    })
  }

  fn inst_extern_data(&mut self, id: DefId, def: &parse::ExternDataDef) -> MRes<LValue> {
    self.with_scope_of(id, |this| {
      let ty = this.infer_ty(&def.ty)?;
      this.insts.insert((id, vec![]), Inst::ExternData { name: def.name, ty: ty.clone(), is_mut: def.is_mut });

      Ok(LValue::DataRef { ty, is_mut: def.is_mut, id })
    })
  }

  fn inst_extern_func(&mut self, id: DefId, def: &parse::ExternFuncDef) -> MRes<RValue> {
    self.with_scope_of(id, |this| {
      let ty = Ty::Func(this.infer_params(&def.params)?,
                        def.varargs,
                        Box::new(this.infer_ty(&def.ret_ty)?));
      this.insts.insert((id, vec![]), Inst::ExternFunc { name: def.name, ty: ty.clone() });

      Ok(RValue::FuncRef { ty, id: (id, vec![]) })
    })
  }

  /// Continue checking with a certain DefId as root
  fn with_scope_of<F: FnOnce(&mut CheckCtx) -> MRes<R>, R>(&mut self, def_id: DefId, f: F) -> MRes<R> {
    self.parent_ids.push(self.repo.parent(def_id));
    let result = f(self);
    self.parent_ids.pop();
    result
  }

  /// Lookup a parsed definition by its id
  fn parsed_def(&self, id: DefId) -> &'static parse::Def {
    unsafe { &*(self.repo.defs.get(&id).unwrap() as *const _) }
  }

  /// Lookup an instance by its id
  fn inst(&self, id: &(DefId, Vec<Ty>)) -> &Inst {
    self.insts.get(id).unwrap()
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
  fn lookup(&self, path: &parse::Path) -> MRes<Sym> {
    // Single crumb paths can refer to locals
    if path.len() == 1 {
      for scope in self.scopes.iter().rev() {
        if let Some(sym) = scope.get(&path[0]) {
          return Ok(sym.clone());
        }
      }
    }

    // Otherwise check the global symbol table
    if let Some(def_id) = self.repo.locate(*self.parent_ids.last().unwrap(), path) {
      return Ok(Sym::Def(def_id))
    }
    
    Err(Box::new(UnresolvedPathError(path.clone())))
  }

  /// Infer the semantic form of a type expression
  fn infer_ty(&mut self, ty: &parse::Ty) -> MRes<Ty> {
    use parse::Ty::*;
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
      Inst(path, targs) => {
        let targs = targs
          .iter()
          .map(|ty| self.infer_ty(ty))
          .monadic_collect()?;
        self.inst_as_ty(path, targs)?
      },
      Ptr(is_mut, base_ty) => {
        Ty::Ptr(*is_mut, Box::new(self.infer_ty(base_ty)?))
      },
      Func(params, ret_ty) => {
        Ty::Func(self.infer_params(params)?,
                 false,Box::new(self.infer_ty(ret_ty)?))
      },
      Arr(elem_cnt_expr, elem_ty) => {
        let elem_cnt = self.infer_rvalue(elem_cnt_expr)
          .and_then(|rvalue| consteval_index(&rvalue))?;
        Ty::Arr(elem_cnt, Box::new(self.infer_ty(elem_ty)?))
      },
      Tuple(params) => {
        Ty::Tuple(self.infer_params(params)?)
      }
    })
  }

  /// Lookup a definition and instantiate it as a type
  fn inst_as_ty(&mut self, path: &parse::Path, targs: Vec<Ty>) -> MRes<Ty> {
    match self.lookup(path)? {
      Sym::Def(def_id) => {
        match self.parsed_def(def_id) {
          parse::Def::Type(def) => {
            self.infer_ty(&def.ty)
          }
          parse::Def::Struct(def) => {
            self.inst_struct((def_id, targs), def)
          }
          parse::Def::Union(def) => {
            self.inst_union((def_id, targs), def)
          }
          parse::Def::Enum(def) => {
            self.inst_enum((def_id, targs), def)
          }
          _ => {
            Err(Box::new(UnresolvedPathError(path.clone())))
          }
        }
      }
      Sym::TParam(ty) => {
        Ok(ty)
      }
    }
  }

  /// Infer the semantic form of an expression in an lvalue context
  fn infer_lvalue(&mut self, expr: &parse::Expr) -> MRes<LValue> {
    use parse::Expr::*;

    Ok(match expr {
      Path(path) => {
        self.inst_as_lvalue(path)?
      }
      Arr(elements) => {
        let elem_ty = self.tctx.tvar(Ty::BoundAny);
        let elements = elements.iter()
          .map(|element| self.infer_rvalue(element))
          .monadic_collect()?;
        for element in elements.iter() {
          self.tctx.unify(&elem_ty, element.ty())?;
        }
        LValue::ArrayLit {
          ty: Ty::Arr(elements.len(), Box::new(elem_ty)),
          is_mut: IsMut::No,
          elements
        }
      }
      Str(val) => {
        let ty = Ty::Arr(val.len(), Box::new(self.tctx.tvar(Ty::BoundInt)));
        LValue::StrLit { ty, is_mut: IsMut::No, val: val.clone() }
      }
      Dot(arg, name) => {
        self.infer_dot(arg, *name)?
      }
      Index(arg, idx) => {
        self.infer_index(arg, idx)?
      }
      Call(called, args) => {
        if let Some((ty, params)) = self.check_struct_ctor(called) {
          let fields = self.infer_args(&params, args)?;
          LValue::StructLit {
            ty,
            is_mut: IsMut::No,
            fields
          }
        } else {
          return Err(Box::new(TypeError(format!("Expected lvalue instead of {:?}", expr))))
        }
      }
      Ind(arg) => {
        self.infer_ind(arg)?
      }
      expr => return Err(Box::new(
        TypeError(format!("Expected lvalue instead of {:?}", expr))))
    })
  }

  /// Lookup a definition and instantiate it as an lvalue
  fn inst_as_lvalue(&mut self, path: &parse::Path) -> MRes<LValue> {
    match self.lookup(path)? {
      Sym::Def(def_id) => {
        match self.parsed_def(def_id) {
          parse::Def::Const(def) => {
            self.with_scope_of(def_id, |this| {
              this.infer_lvalue(&def.val)
            })
          }
          parse::Def::Data(def) => {
            self.inst_data(def_id, def)
          }
          parse::Def::ExternData(def) => {
            self.inst_extern_data(def_id, def)
          }
          parse::Def::Param(_) => {
            let inst = self.insts.get(&(def_id, vec![])).unwrap();
            if let Inst::Param { ty, is_mut, .. } = inst {
              Ok(LValue::ParamRef {
                ty: ty.clone(),
                is_mut: *is_mut,
                id: def_id
              })
            } else {
              unreachable!()
            }
          }
          parse::Def::Let(_) => {
            let inst = self.insts.get(&(def_id, vec![])).unwrap();
            if let Inst::Let { ty, is_mut, .. } = inst {
              Ok(LValue::LetRef {
                ty: ty.clone(),
                is_mut: *is_mut,
                id: def_id
              })
            } else {
              unreachable!()
            }
          }
          _ => Err(Box::new(TypeError(format!("{} cannot be used as an lvalue", path[0]))))
        }
      }
      Sym::TParam(..) => {
        Err(Box::new(TypeError(format!("{} cannot be used as an lvalue", path[0]))))
      }
    }
  }

  /// Infer the type of a member access expression
  fn infer_dot(&mut self, arg: &parse::Expr, name: RefStr) -> MRes<LValue> {
    // Infer argument type
    let arg = self.infer_lvalue(arg)?;

    'error: loop {
      // Find parameter list
      let ty = self.tctx.lit_ty_nonrecusrive(arg.ty());

      let (is_stru, params) = match &ty {
        Ty::Inst(_, id) => match self.inst(id) {
          Inst::Struct { params: Some(params), .. } => (true, params),
          Inst::Union { params: Some(params), .. } => (false, params),
          _ => break 'error
        },
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
          idx
        })
      } else {
        Ok(LValue::UnionDot {
          ty: param_ty.clone(),
          is_mut: arg.is_mut(),
          arg: Box::new(arg)
        })
      }
    }

    Err(Box::new(TypeError(format!("Type {:?} has no field named {}", arg.ty(), name))))
  }

  /// Infer the type of an array index expression
  fn infer_index(&mut self, arg: &parse::Expr, idx: &parse::Expr) -> MRes<LValue> {
    // Infer array type
    let arg = self.infer_lvalue(arg)?;

    // Find element type
    let ty = self.tctx.lit_ty_nonrecusrive(arg.ty());
    let elem_ty = match &ty {
      Ty::Arr(_, elem_ty) => &**elem_ty,
      _ => return Err(Box::new(TypeError(format!("Cannot index type {:?}", arg.ty()))))
    };

    // Check index type
    let idx = self.infer_rvalue(idx)?;
    self.tctx.unify(&Ty::Uintn, idx.ty())?;

    Ok(LValue::Index {
      ty: elem_ty.clone(),
      is_mut: arg.is_mut(),
      arg: Box::new(arg),
      idx: Box::new(idx)
    })
  }

  /// Infer the type of a pointer indirection expression
  fn infer_ind(&mut self, arg: &parse::Expr) -> MRes<LValue> {
    // Infer pointer type
    let arg = self.infer_rvalue(arg)?;

    // Find base type
    let ty = self.tctx.lit_ty_nonrecusrive(arg.ty());
    let (is_mut, base_ty) = match &ty {
      Ty::Ptr(is_mut, base_ty) => (*is_mut, &**base_ty),
      _ => return Err(Box::new(
        TypeError(format!("Cannot dereference type {:?}", arg.ty()))))
    };

    Ok(LValue::Ind {
      ty: base_ty.clone(),
      is_mut: is_mut,
      arg: Box::new(arg)
    })
  }

  /// Check whether or not `expr` is a struct constructor in the current context
  fn check_struct_ctor(&mut self, expr: &parse::Expr) -> Option<(Ty, Vec<(RefStr, Ty)>)> {
    if let parse::Expr::Path(path) = expr {
      // FIXME: we might need to infer type arguments
      if let Ok(ty) = self.inst_as_ty(path, vec![]) {
        if let Ty::Inst(_, id) = &ty {
          if let Inst::Struct { params, .. } = self.insts.get(id).unwrap() {
            return Some((ty, params.clone().unwrap()))
          } else {
            unreachable!()
          }
        } else {
          unreachable!()
        }
      }
    }
    None
  }

  /// Infer the semantic form of an expression in an rvalue context
  fn infer_rvalue(&mut self, expr: &parse::Expr) -> MRes<RValue> {
    use parse::Expr::*;

    Ok(match expr {
      Empty => {
        RValue::Empty { ty: Ty::Tuple(vec![]) }
      }
      Path(path) => {
        self.inst_as_rvalue(path)?
      }
      Arr(..) | Str(..) | Dot(..) | Index(..) | Ind(..) => {
        let arg = self.infer_lvalue(expr)?;
        RValue::Load {
          ty: arg.ty().clone(),
          arg: Box::new(arg)
        }
      }
      CStr(val) => {
        RValue::CStr { ty: Ty::Ptr(IsMut::No, Box::new(Ty::Int8)), val: val.clone() }
      }
      Nil => {
        RValue::Nil { ty: Ty::Ptr(IsMut::Yes, Box::new(self.tctx.tvar(Ty::BoundAny))) }
      }
      Bool(val) => {
        RValue::Bool { ty: Ty::Bool, val: *val }
      }
      Int(val) => {
        RValue::Int { ty: self.tctx.tvar(Ty::BoundInt), val: *val }
      }
      Flt(val) => {
        RValue::Flt { ty: self.tctx.tvar(Ty::BoundFlt), val: *val }
      }
      Call(called, args) => {
        if let Some((ty, params)) = self.check_struct_ctor(called) {
          let fields = self.infer_args(&params, args)?;
          let arg = LValue::StructLit {
            ty,
            is_mut: IsMut::No,
            fields
          };
          RValue::Load {
            ty: arg.ty().clone(),
            arg: Box::new(arg)
          }
        } else {
          self.infer_call(called, args)?
        }
      }
      Adr(arg) => {
        let arg = self.infer_lvalue(arg)?;
        RValue::Adr {
          ty: Ty::Ptr(arg.is_mut(), Box::new(arg.ty().clone())),
          arg: Box::new(arg)
        }
      }
      Un(op, arg) => {
        let arg = self.infer_rvalue(arg)?;
        RValue::Un {
          ty: self.infer_un(*op, arg.ty())?,
          op: *op,
          arg: Box::new(arg)
        }
      }
      LNot(arg) => {
        let arg = self.infer_rvalue(arg)?;
        self.tctx.unify(&Ty::Bool, arg.ty())?;
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
        self.tctx.unify(&Ty::Bool, lhs.ty())?;
        self.tctx.unify(&Ty::Bool, rhs.ty())?;
        RValue::LAnd { ty: Ty::Bool, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      LOr(lhs, rhs) => {
        let lhs = self.infer_rvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        self.tctx.unify(&Ty::Bool, lhs.ty())?;
        self.tctx.unify(&Ty::Bool, rhs.ty())?;
        RValue::LOr { ty: Ty::Bool, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Block(parsed_body) => {
        self.newscope();
        let mut body = vec![];
        for expr in parsed_body {
          body.push(self.infer_rvalue(expr)?);
        }
        self.popscope();

        let ty = if let Some(last) = body.last() {
          last.ty().clone()
        } else {
          Ty::Tuple(vec![])
        };

        RValue::Block { ty, body }
      }
      As(lhs, rhs) => {
        // Infer argument types
        let lhs = self.infer_lvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        self.tctx.unify(lhs.ty(), rhs.ty())?;

        // Make sure lhs is mutable
        match lhs.is_mut() {
          IsMut::Yes => (),
          _ => return Err(Box::new(
            TypeError(format!("Cannot assign to immutable location {:?}", lhs)))),
        };

        RValue::As { ty: Ty::Tuple(vec![]), lhs: Box::new(lhs), rhs: Box::new(rhs) }
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

        RValue::Rmw { ty: Ty::Tuple(vec![]), op: *op, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Continue => {
        // Can only have continue inside a loop
        match self.loop_ty.last() {
          Some(..) => (),
          None => return Err(Box::new(
            TypeError(format!("Continue outside loop")))),
        };

        RValue::Continue { ty: self.tctx.tvar(Ty::BoundAny) }
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
        self.tctx.unify(&loop_ty, arg.ty())?;

        RValue::Break { ty: self.tctx.tvar(Ty::BoundAny), arg: Box::new(arg) }
      }
      Return(arg) => {
        let arg = self.infer_rvalue(&*arg)?;

        // Can only have return inside a function
        let ret_ty = match self.ret_ty.last() {
          Some(ret_ty) => ret_ty.clone(),
          None => return Err(Box::new(
            TypeError(format!("Return outside function")))),
        };

        // Unify function return type with the returned value's type
        self.tctx.unify(&ret_ty, arg.ty())?;

        RValue::Return { ty: self.tctx.tvar(Ty::BoundAny), arg: Box::new(arg) }
      }
      Let(def_id, init) => {
        let def = self.repo.let_by_id(*def_id);

        // Add symbol
        self.define(def.name, Sym::Def(*def_id));

        // Type check initializer
        let (ty, init) = if let Some(init) = init {
          // Check initializer
          let init = self.infer_rvalue(init)?;
          // Unify type annotation with initializer type
          if let Some(ty) = &def.ty {
            let ty = self.infer_ty(ty)?;
            self.tctx.unify(&ty, init.ty())?;
          }
          (init.ty().clone(), Some(Box::new(init)))
        } else if let Some(ty) = &def.ty {
          (self.infer_ty(ty)?, None)
        } else {
          (self.tctx.tvar(Ty::BoundAny), None)
        };

        // Add instance
        self.insts.insert((*def_id, vec![]), Inst::Let {
          name: def.name,
          is_mut: def.is_mut,
          ty
        });

        RValue::Let { ty: Ty::Tuple(vec![]), id: *def_id, init }
      }
      If(cond, tbody, ebody) => {
        let cond = self.infer_rvalue(cond)?;
        self.tctx.unify(&Ty::Bool, cond.ty())?;

        let tbody = self.infer_rvalue(tbody)?;
        let ebody = self.infer_rvalue(ebody)?;
        self.tctx.unify(tbody.ty(), ebody.ty())?;

        RValue::If {
          ty: tbody.ty().clone(),
          cond: Box::new(cond),
          tbody: Box::new(tbody),
          ebody: Box::new(ebody)
        }
      }
      While(cond, body) => {
        let cond = self.infer_rvalue(cond)?;
        self.tctx.unify(&Ty::Bool, cond.ty())?;

        self.loop_ty.push(Ty::Tuple(vec![]));
        let body = self.infer_rvalue(body)?;
        let ty = self.loop_ty.pop().unwrap();

        RValue::While {
          ty,
          cond: Box::new(cond),
          body: Box::new(body)
        }
      }
      Loop(body) => {
        self.loop_ty.push(self.tctx.tvar(Ty::BoundAny));
        let body = self.infer_rvalue(body)?;
        let ty = self.loop_ty.pop().unwrap();

        RValue::Loop {
          ty,
          body: Box::new(body)
        }
      }
    })
  }

  /// Lookup a definition and instantiate it as an rvalue
  fn inst_as_rvalue(&mut self, path: &parse::Path) -> MRes<RValue> {
    /// Convert an lvalue to an rvalue by loading it
    fn lvalue_to_rvalue(lvalue: LValue) -> RValue {
      RValue::Load {
        ty: lvalue.ty().clone(),
        arg: Box::new(lvalue)
      }
    }

    match self.lookup(path)? {
      Sym::Def(def_id) => {
        match self.parsed_def(def_id) {
          parse::Def::Const(def) => {
            self.with_scope_of(def_id, |this| {
              this.infer_rvalue(&def.val)
            })
          }
          parse::Def::Func(def) => {
            let targs = def.type_params
              .iter()
              .map(|_| self.tctx.tvar(Ty::BoundAny))
              .collect();

            self.inst_func_sig((def_id, targs), def)
          }
          parse::Def::Data(def) => {
            let lvalue = self.inst_data(def_id, def)?;
            Ok(lvalue_to_rvalue(lvalue))
          }
          parse::Def::ExternData(def) => {
            let lvalue = self.inst_extern_data(def_id, def)?;
            Ok(lvalue_to_rvalue(lvalue))
          }
          parse::Def::ExternFunc(def) => {
            self.inst_extern_func(def_id, def)
          }
          parse::Def::Param(_) => {
            let inst = self.insts.get(&(def_id, vec![])).unwrap();
            if let Inst::Param { ty, is_mut, .. } = inst {
              let lvalue = LValue::ParamRef {
                ty: ty.clone(),
                is_mut: *is_mut,
                id: def_id
              };
              Ok(lvalue_to_rvalue(lvalue))
            } else {
              unreachable!()
            }
          }
          parse::Def::Let(_) => {
            let inst = self.insts.get(&(def_id, vec![])).unwrap();
            if let Inst::Let { ty, is_mut, .. } = inst {
              let lvalue = LValue::LetRef {
                ty: ty.clone(),
                is_mut: *is_mut,
                id: def_id
              };
              Ok(lvalue_to_rvalue(lvalue))
            } else {
              unreachable!()
            }
          }
          _ => Err(Box::new(TypeError(format!("{} cannot be used as an rvalue", path[0]))))
        }
      }
      Sym::TParam(..) => {
        Err(Box::new(TypeError(format!("{} cannot be used as an rvalue", path[0]))))
      }
    }
  }

  fn infer_call(&mut self, called: &parse::Expr, args: &Vec<(RefStr, parse::Expr)>) -> MRes<RValue> {
    // Infer function type
    let called_expr = self.infer_rvalue(called)?;

    // Find parameter list and return type
    let called_ty = self.tctx.lit_ty_nonrecusrive(called_expr.ty());
    let (params, va, ret_ty) = match &called_ty {
      Ty::Func(params, va, ret_ty) => (params, *va, &**ret_ty),
      _ => return Err(Box::new(TypeError(format!("Cannot call type {:?}", called_expr.ty()))))
    };

    // Validate argument count
    if args.len() < params.len() {
      return Err(Box::new(TypeError(format!("Not enough arguments for {:?}", called_expr.ty()))))
    }
    if va == false && args.len() > params.len() {
      return Err(Box::new(TypeError(format!("Too many arguments for {:?}", called_expr.ty()))))
    }

    let args = self.infer_args(params, args)?;

    Ok(RValue::Call {
      ty: ret_ty.clone(),
      arg: Box::new(called_expr),
      args
    })
  }

  fn infer_args(&mut self, params: &[(RefStr, Ty)], args: &[(RefStr, parse::Expr)]) -> MRes<Vec<RValue>> {
    let mut nargs = vec![];
    let mut params_iter = params.iter();

    for (arg_name, arg_val) in args.iter() {
      // Infer type of argument value
      let arg_val = self.infer_rvalue(arg_val)?;
      // If there is a corresponding parameter name and type, check it
      if let Some((param_name, param_ty)) = params_iter.next() {
        if *arg_name != RefStr::new("") && arg_name != param_name {
          return Err(Box::new(TypeError(format!("Incorrect argument label {}", arg_name))))
        }
        self.tctx.unify(arg_val.ty(), param_ty)?;
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
        self.tctx.unify(arg, &Ty::BoundNum)
      }
      UnOp::Not => {
        self.tctx.unify(arg, &Ty::BoundInt)
      }
    }
  }

  fn infer_bin(&mut self, op: BinOp, lhs: &Ty, rhs: &Ty) -> MRes<Ty> {
    // Check argument types and infer result type
    match op {
      // Both arguments must have matching numeric types
      // Result has the same type as the arguments
      BinOp::Mul | BinOp::Div | BinOp::Add | BinOp::Sub => {
        self.tctx.unify(lhs, &Ty::BoundNum)?;
        self.tctx.unify(lhs, rhs)
      }

      // Both arguments must have matching integer types
      // Result has the same type as the arguments
      BinOp::Mod | BinOp::And | BinOp::Xor | BinOp::Or  => {
        self.tctx.unify(lhs, &Ty::BoundInt)?;
        self.tctx.unify(lhs, rhs)
      }

      // Both arguments must have integer types
      // Result has the left argument's type
      BinOp::Lsh | BinOp::Rsh => {
        self.tctx.unify(rhs, &Ty::BoundInt)?;
        self.tctx.unify(lhs, &Ty::BoundInt)
      }

      // Both arguments must have matching numeric types
      // Result is a boolean
      BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
        self.tctx.unify(lhs, &Ty::BoundNum)?;
        self.tctx.unify(lhs, rhs)?;
        Ok(Ty::Bool)
      }
    }
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

#[derive(Debug)]
struct UnresolvedPathError(parse::Path);

impl fmt::Display for UnresolvedPathError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    // There is always at least one crumb
    write!(f, "Unresolved path {}", self.0[0].borrow_rs())?;
    // Then the rest can be prefixed with ::
    for crumb in self.0[1..].iter() {
      write!(f, "::{}", crumb.borrow_rs())?;
    }
    Ok(())
  }
}

impl error::Error for UnresolvedPathError {}
