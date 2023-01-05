// SPDX-License-Identifier: GPL-2.0-only

use super::*;

pub(super) fn infer_module(tctx: &mut TVarCtx, parsed_module: &parse::Repository) -> MRes<HashMap<(DefId, Vec<Ty>), Inst>> {
  let mut ctx = CheckCtx {
    tctx,
    parsed_defs: &parsed_module.defs,
    insts: HashMap::new(),
    scopes: vec! [ HashMap::new() ],
    local_cnt: 0,
    local_defs: Vec::new(),
    ret_ty: Vec::new(),
    loop_ty: Vec::new(),
  };

  // Build symbol table
  for (id, def) in parsed_module.defs.iter() {
    ctx.define(def.name(), Sym::Def(*id));
  }

  // Instantiate signatures for non-generic functions
  for (id, def) in parsed_module.defs.iter() {
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
  // Type variable context
  tctx: &'a mut TVarCtx,

  // Parsed definitions
  parsed_defs: &'a HashMap<DefId, parse::Def>,

  // Checked definitions
  insts: HashMap<(DefId, Vec<Ty>), Inst>,

  // Symbol table
  scopes: Vec<HashMap<RefStr, Sym>>,

  // Local definition
  local_cnt: usize,
  local_defs: Vec<HashMap<LocalId, LocalDef>>,

  // Function return type
  ret_ty: Vec<Ty>,

  // Loop types
  loop_ty: Vec<Ty>,
}

#[derive(Clone)]
enum Sym {
  Def(DefId),
  Local(LocalId),
  TParam(Ty)
}

impl<'a> CheckCtx<'a> {
  fn inst_struct(&mut self, id: (DefId, Vec<Ty>), def: &parse::StructDef) -> MRes<Ty> {
    // Try to find previous matching copy
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::Inst(def.name, id)) }

    self.insts.insert(id.clone(), Inst::Struct { name: def.name, params: None });

    // FIXME: bring type params into scope
    // if def.type_params.len() != id.1.len() {
    //   return Err(Box::new(TypeError(format!("Incorrect number of type parameters"))))
    // }
    let params = self.infer_params(&def.params)?;
    self.insts.insert(id.clone(), Inst::Struct { name: def.name, params: Some(params) });

    Ok(Ty::Inst(def.name, id))
  }

  fn inst_union(&mut self, id: (DefId, Vec<Ty>), def: &parse::UnionDef) -> MRes<Ty> {
    // Try to find previous matching copy
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::Inst(def.name, id)) }

    self.insts.insert(id.clone(), Inst::Union { name: def.name, params: None });

    let params = self.infer_params(&def.params)?;
    self.insts.insert(id.clone(), Inst::Union { name: def.name, params: Some(params) });

    Ok(Ty::Inst(def.name, id))
  }

  fn inst_enum(&mut self, id: (DefId, Vec<Ty>), def: &parse::EnumDef) -> MRes<Ty> {
    // Try to find previous matching copy
    if let Some(..) = self.insts.get(&id) { return Ok(Ty::Inst(def.name, id)) }

    self.insts.insert(id.clone(), Inst::Enum { name: def.name, variants: None });

    let variants = self.infer_variants(&def.variants)?;
    self.insts.insert(id.clone(), Inst::Enum { name: def.name, variants: Some(variants) });

    Ok(Ty::Inst(def.name, id))
  }

  fn infer_params(&mut self, params: &Vec<(RefStr, parse::Ty)>) -> MRes<Vec<(RefStr, Ty)>> {
    let mut result = vec![];
    for (name, ty) in params {
      result.push((*name, self.infer_ty(ty)?));
    }
    Ok(result)
  }

  fn infer_variants(&mut self, variants: &Vec<(RefStr, parse::Variant)>) -> MRes<Vec<(RefStr, Variant)>> {
    let mut result = vec![];
    for (name, variant) in variants {
      result.push((*name, match variant {
        parse::Variant::Unit => {
          Variant::Unit(*name)
        }
        parse::Variant::Struct(params) => {
          Variant::Struct(*name, self.infer_params(params)?)
        }
      }));
    }
    Ok(result)
  }

  fn inst_const(&mut self, id: DefId, def: &parse::ConstDef) -> MRes<RValue> {
    let ty = self.infer_ty(&def.ty)?;
    let val = self.infer_rvalue(&def.val)?;
    self.tctx.unify(&ty, val.ty())?;
    self.insts.insert((id, vec![]), Inst::Const { name: def.name, ty: ty.clone(), val });

    Ok(RValue::ConstRef { ty, name: def.name, id })
  }

  fn inst_data(&mut self, id: DefId, def: &parse::DataDef) -> MRes<LValue> {
    let ty = self.infer_ty(&def.ty)?;
    let init = self.infer_rvalue(&def.init)?;
    self.tctx.unify(&ty, init.ty())?;
    self.insts.insert((id, vec![]), Inst::Data {
      name: def.name,
      ty: ty.clone(),
      is_mut: def.is_mut,
      init
    });

    Ok(LValue::DataRef { ty, is_mut: def.is_mut, name: def.name, id })
  }

  fn inst_func_sig(&mut self, id: (DefId, Vec<Ty>), def: &parse::FuncDef) -> MRes<RValue> {
    // Try to find exisiting instance first
    if let Some(Inst::Func { name, ty, .. }) = self.insts.get(&id) {
      return Ok(RValue::FuncRef { ty: ty.clone(), name: *name, id })
    }

    self.newscope();

    // Type params
    if def.type_params.len() != id.1.len() {
      return Err(Box::new(TypeError(format!("Incorrect number of type parameters"))))
    }
    for (name, ty) in def.type_params.iter().zip(id.1.iter()) {
      self.define(*name, Sym::TParam(ty.clone()));
    }

    // Regular parameters
    let mut param_tys = vec![];
    for (name, _, ty) in def.params.iter() {
      param_tys.push((*name, self.infer_ty(ty)?));
    }

    // Return type
    let ret_ty = self.infer_ty(&def.ret_ty)?;

    self.popscope();

    // Insert signature record
    self.insts.insert(id.clone(), Inst::Func {
      name: def.name,
      ty: Ty::Func(param_tys.clone(), false, Box::new(ret_ty.clone())),
      locals: HashMap::new(),
      body: None
    });

    // Return reference to signature
    Ok(RValue::FuncRef {
      ty: Ty::Func(param_tys.clone(), false, Box::new(ret_ty.clone())),
      name: def.name,
      id
    })
  }

  fn inst_func_body(&mut self, id: (DefId, Vec<Ty>), def: &parse::FuncDef) -> MRes<()> {
    // Create environment
    self.newscope();
    self.local_defs.push(HashMap::new());

    // Type params
    if def.type_params.len() != id.1.len() {
      return Err(Box::new(TypeError(format!("Incorrect number of type parameters"))))
    }
    for (name, ty) in def.type_params.iter().zip(id.1.iter()) {
      self.define(*name, Sym::TParam(ty.clone()));
    }

    // Regular parameters
    let mut param_tys = vec![];
    for (index, (name, is_mut, ty)) in def.params.iter().enumerate() {
      let ty = self.infer_ty(ty)?;
      param_tys.push((*name, ty.clone()));
      self.newlocal(LocalDef::Param { name: *name, ty, is_mut: *is_mut, index: index });
    }

    // Return type
    let ret_ty = self.infer_ty(&def.ret_ty)?;

    // Body
    self.ret_ty.push(ret_ty.clone());
    let body = self.infer_rvalue(&def.body)?;
    self.tctx.unify(&ret_ty, body.ty())?;
    self.ret_ty.pop().unwrap();

    let locals = self.local_defs.pop().unwrap();
    self.popscope();

    // Insert body
    self.insts.insert(id.clone(), Inst::Func {
      name: def.name,
      ty: Ty::Func(param_tys.clone(), false,Box::new(ret_ty.clone())),
      locals,
      body: Some(body)
    });

    Ok(())
  }

  fn inst_extern_data(&mut self, id: DefId, def: &parse::ExternDataDef) -> MRes<LValue> {
    let ty = self.infer_ty(&def.ty)?;
    self.insts.insert((id, vec![]), Inst::ExternData { name: def.name, ty: ty.clone(), is_mut: def.is_mut });

    Ok(LValue::DataRef { ty, is_mut: def.is_mut, name: def.name, id })
  }

  fn inst_extern_func(&mut self, id: DefId, def: &parse::ExternFuncDef) -> MRes<RValue> {
    let ty = Ty::Func(self.infer_params(&def.params)?,
                      def.varargs,
                      Box::new(self.infer_ty(&def.ret_ty)?));
    self.insts.insert((id, vec![]), Inst::ExternFunc { name: def.name, ty: ty.clone() });

    Ok(RValue::FuncRef { ty, name: def.name, id: (id, vec![]) })
  }

  /// Lookup a parsed definition by its id
  fn parsed_def(&self, id: DefId) -> &'static parse::Def {
    unsafe { &*(self.parsed_defs.get(&id).unwrap() as *const _) }
  }

  /// Lookup a local definition by its id
  fn local_def(&self, id: LocalId) -> &LocalDef {
    self.local_defs.last().unwrap().get(&id).unwrap()
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
  fn lookup(&self, name: RefStr) -> MRes<Sym> {
    for scope in self.scopes.iter().rev() {
      if let Some(sym) = scope.get(&name) {
        return Ok(sym.clone());
      }
    }
    Err(Box::new(UnresolvedIdentError { name }))
  }

  /// Create local definition with a new id
  fn newlocal(&mut self, def: LocalDef) -> LocalId {
    let id = LocalId(self.local_cnt);
    self.local_cnt += 1;

    self.define(def.name(), Sym::Local(id));
    self.local_defs.last_mut().unwrap().insert(id, def);
    id
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
        self.inst_as_ty(path[0], targs)?
      },
      Ptr(is_mut, base_ty) => {
        Ty::Ptr(*is_mut, Box::new(self.infer_ty(base_ty)?))
      },
      Func(params, ret_ty) => {
        Ty::Func(self.infer_params(params)?,
                 false,Box::new(self.infer_ty(ret_ty)?))
      },
      Arr(_, elem_ty) => {
        // FIXME: evaluate elem_cnt constant expression
        Ty::Arr(0, Box::new(self.infer_ty(elem_ty)?))
      },
      Tuple(params) => {
        Ty::Tuple(self.infer_params(params)?)
      }
    })
  }

  /// Lookup a definition and instantiate it as a type
  fn inst_as_ty(&mut self, name: RefStr, targs: Vec<Ty>) -> MRes<Ty> {
    match self.lookup(name)? {
      Sym::Def(def_id) => {
        match self.parsed_def(def_id) {
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
            Err(Box::new(UnresolvedIdentError { name }))
          }
        }
      }
      Sym::TParam(ty) => {
        Ok(ty)
      }
      _ => {
        Err(Box::new(UnresolvedIdentError { name }))
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
      Str(val) => {
        let ty = Ty::Arr(val.len(), Box::new(self.tctx.tvar(Ty::BoundInt)));
        LValue::Str { ty, is_mut: IsMut::No, val: val.clone() }
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
      expr => return Err(Box::new(
        TypeError(format!("Expected lvalue instead of {:?}", expr))))
    })
  }

  /// Lookup a definition and instantiate it as an lvalue
  fn inst_as_lvalue(&mut self, path: &parse::Path) -> MRes<LValue> {
    match self.lookup(path[0])? {
      Sym::Def(def_id) => {
        match self.parsed_def(def_id) {
          parse::Def::Data(def) => {
            self.inst_data(def_id, def)
          }
          parse::Def::ExternData(def) => {
            self.inst_extern_data(def_id, def)
          }
          _ => Err(Box::new(TypeError(format!("{} cannot be used as an lvalue", path[0]))))
        }
      }
      Sym::Local(id) => {
        match self.local_def(id) {
          LocalDef::Param { ty, is_mut, .. } => {
            Ok(LValue::ParamRef { ty: ty.clone(), is_mut: *is_mut, name: path[0], id })
          },
          LocalDef::Let { ty, is_mut, .. } => {
            Ok(LValue::LetRef { ty: ty.clone(), is_mut: *is_mut, name: path[0], id })
          },
        }
      }
      Sym::TParam(..) => {
        Err(Box::new(TypeError(format!("{} cannot be used as an lvalue", path[0]))))
      }
    }
  }

  fn infer_dot(&mut self, arg: &parse::Expr, name: RefStr) -> MRes<LValue> {
    // Infer argument type
    let arg = self.infer_lvalue(arg)?;

    'error: loop {
      // Find parameter list
      let params = match arg.ty() {
        Ty::Inst(_, id) => match self.inst(id) {
          Inst::Struct { params: Some(params), .. } => params,
          Inst::Union { params: Some(params), .. } => params,
          _ => break 'error
        },
        Ty::Tuple(params) => params,
        _ => break 'error
      };

      // Find parameter
      let (idx, param_ty) = match lin_search(params, &name) {
        Some(val) => val,
        None => break 'error
      };

      return Ok(LValue::Dot {
        ty: param_ty.clone(),
        is_mut: arg.is_mut(),
        arg: Box::new(arg),
        name: name,
        idx: idx
      });
    }

    Err(Box::new(TypeError(format!("Type {:?} has no field named {}", arg.ty(), name))))
  }

  fn infer_index(&mut self, arg: &parse::Expr, idx: &parse::Expr) -> MRes<LValue> {
    // Infer array type
    let arg = self.infer_lvalue(arg)?;

    // Find element type
    let elem_ty = match arg.ty() {
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

  fn infer_ind(&mut self, arg: &parse::Expr) -> MRes<LValue> {
    // Infer pointer type
    let arg = self.infer_rvalue(arg)?;

    // Find base type
    let (is_mut, base_ty) = match arg.ty() {
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

  /// Infer the semantic form of an expression in an rvalue context
  fn infer_rvalue(&mut self, expr: &parse::Expr) -> MRes<RValue> {
    use parse::Expr::*;

    Ok(match expr {
      Null => {
        RValue::Null { ty: Ty::Tuple(vec![]) }
      }
      Path(path) => {
        self.inst_as_rvalue(path)?
      }
      Str(..) | Dot(..) | Index(..) | Ind(..) => {
        let arg = self.infer_lvalue(expr)?;
        RValue::Load {
          ty: arg.ty().clone(),
          arg: Box::new(arg)
        }
      }
      CStr(val) => {
        RValue::CStr { ty: Ty::Ptr(IsMut::No, Box::new(Ty::Int8)), val: val.clone() }
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
      Char(val) => {
        RValue::Char { ty: self.tctx.tvar(Ty::BoundInt), val: val.clone() }
      }
      Call(arg, args) => {
        self.infer_call(arg, args)?
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
      Cast(..) => {
        todo!()
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
      Let(name, is_mut, ty, init) => {
        // Check initializer
        let init = self.infer_rvalue(init)?;

        // Unify type annotation with initializer type
        if let Some(ty) = ty {
          let ty = self.infer_ty(ty)?;
          self.tctx.unify(&ty, init.ty())?;
        }

        // Add local definition
        let id = self.newlocal(LocalDef::Let {
          name: *name,
          is_mut: *is_mut,
          ty: init.ty().clone()
        });

        // Add let expression
        RValue::Let { ty: Ty::Tuple(vec![]), id, init: Box::new(init) }
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

    match self.lookup(path[0])? {
      Sym::Def(def_id) => {
        match self.parsed_def(def_id) {
          parse::Def::Const(def) => {
            self.inst_const(def_id, def)
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
          _ => Err(Box::new(TypeError(format!("{} cannot be used as an rvalue", path[0]))))
        }
      }
      Sym::Local(id) => {
        match self.local_def(id) {
          LocalDef::Param { ty, is_mut, .. } => {
            let lvalue = LValue::ParamRef { ty: ty.clone(), is_mut: *is_mut, name: path[0], id };
            Ok(lvalue_to_rvalue(lvalue))
          },
          LocalDef::Let { ty, is_mut, .. } => {
            let lvalue = LValue::LetRef { ty: ty.clone(), is_mut: *is_mut, name: path[0], id };
            Ok(lvalue_to_rvalue(lvalue))
          }
        }
      }
      Sym::TParam(..) => {
        Err(Box::new(TypeError(format!("{} cannot be used as an rvalue", path[0]))))
      }
    }
  }

  fn infer_call(&mut self, arg: &parse::Expr, args: &Vec<(RefStr, parse::Expr)>) -> MRes<RValue> {
    // Infer function type
    let called_expr = self.infer_rvalue(arg)?;

    // Find parameter list and return type
    let (params, va, ret_ty) = match called_expr.ty() {
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

    // Type check call arguments
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
      nargs.push((*arg_name, arg_val));
    }

    Ok(RValue::Call { ty: ret_ty.clone(), arg: Box::new(called_expr), args: nargs })
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
struct UnresolvedIdentError {
  name: RefStr
}

impl fmt::Display for UnresolvedIdentError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Unresolved identifier {}", self.name)
  }
}

impl error::Error for UnresolvedIdentError {}
