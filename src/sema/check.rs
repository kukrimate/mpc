// SPDX-License-Identifier: GPL-2.0-only

use super::*;

pub(super) fn check_module(tctx: &mut TVarCtx, parsed_module: &parse::Module) -> MRes<Module> {
  let mut ctx = CheckCtx {
    tctx,
    parsed_defs: &parsed_module.defs,
    checked_defs: HashMap::new(),
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

  // Start checking at main
  for (id, def) in parsed_module.defs.iter() {
    if def.name().borrow_rs() == "main" {
      ctx.check_def(*id, def)?;
    }
  }

  Ok(Module::new(ctx.checked_defs))
}

struct CheckCtx<'a> {
  // Type variable context
  tctx: &'a mut TVarCtx,

  // Parsed definitions
  parsed_defs: &'a HashMap<DefId, parse::Def>,

  // Checked definitions
  checked_defs: HashMap<DefId, Def>,

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
}

impl<'a> CheckCtx<'a> {
  fn check_def(&mut self, id: DefId, def: &parse::Def) -> MRes<()> {
    match def {
      parse::Def::Struct { name, type_params, params } => {
        assert_eq!(type_params.len(), 0);

        // Temporary record
        self.checked_defs.insert(id, Def::Struct { name: *name, params: None });

        // Body
        let params = self.check_params(params)?;
        self.checked_defs.insert(id, Def::Struct { name: *name, params: Some(params) });
      }
      parse::Def::Union { name, type_params, params } => {
        assert_eq!(type_params.len(), 0);

        // Temporary record
        self.checked_defs.insert(id, Def::Union { name: *name, params: None });

        // Body
        let params = self.check_params(params)?;
        self.checked_defs.insert(id, Def::Union { name: *name, params: Some(params) });
      }
      parse::Def::Enum { name, type_params, variants } => {
        assert_eq!(type_params.len(), 0);

        // Temporary record
        self.checked_defs.insert(id, Def::Enum { name: *name, variants: None });

        // Body
        let variants = self.check_variants(variants)?;
        self.checked_defs.insert(id, Def::Enum { name: *name, variants: Some(variants) });
      }
      parse::Def::Const { name, ty, val } => {
        // Temporary record
        let ty = self.check_ty(ty)?;
        self.checked_defs.insert(id, Def::Const { name: *name, ty: ty.clone(), val: None });

        // Body
        let val = self.infer_rvalue(val)?;
        self.tctx.unify(&ty, val.ty())?;
        self.checked_defs.insert(id, Def::Const { name: *name, ty, val: Some(val) });
      }
      parse::Def::Data { name, is_mut, ty, init } => {
        // Temporary record
        let ty = self.check_ty(ty)?;
        self.checked_defs.insert(id, Def::Data { name: *name, ty: ty.clone(), is_mut: *is_mut, init: None });

        // Body
        let init = self.infer_rvalue(init)?;
        self.tctx.unify(&ty, init.ty())?;
        self.checked_defs.insert(id, Def::Data { name: *name, ty, is_mut: *is_mut, init: Some(init) });
      }
      parse::Def::Func { type_params, name, params, ret_ty, body } => {
        assert_eq!(type_params.len(), 0);

        // Temporary record
        let mut param_tys = vec![];
        for (name, _, ty) in params.iter() { param_tys.push((*name, self.check_ty(ty)?)); }
        let ty = Ty::Func(param_tys, Box::new(self.check_ty(ret_ty)?));
        self.checked_defs.insert(id, Def::Func { name: *name, ty: ty.clone(), locals: HashMap::new(), body: None });

        // Body
        self.newscope();
        self.local_defs.push(HashMap::new());
        let ret_ty = self.check_ty(ret_ty)?;
        self.ret_ty.push(ret_ty);

        for (index, (name, is_mut, ty)) in params.iter().enumerate() {
          let ty = self.check_ty(ty)?;
          self.newlocal(LocalDef::Param { name: *name, ty: ty, is_mut: *is_mut, index: index });
        }

        let body = self.infer_rvalue(body)?;
        let locals = self.local_defs.pop().unwrap();
        let ret_ty = self.ret_ty.pop().unwrap();
        self.tctx.unify(&ret_ty, body.ty())?;
        self.popscope();

        self.checked_defs.insert(id, Def::Func { name: *name, ty, locals, body: Some(body) });
      }
      parse::Def::ExternData { name, is_mut, ty } => {
        let ty = self.check_ty(ty)?;
        self.checked_defs.insert(id, Def::ExternData { name: *name, ty, is_mut: *is_mut });
      }
      parse::Def::ExternFunc { name, params, ret_ty } => {
        let ty = Ty::Func(self.check_params(params)?, Box::new(self.check_ty(ret_ty)?));
        self.checked_defs.insert(id, Def::ExternFunc { name: *name, ty });
      }
    }

    Ok(())
  }

  fn check_variants(&mut self, variants: &Vec<(RefStr, parse::Variant)>) -> MRes<Vec<(RefStr, Variant)>> {
    let mut result = vec![];
    for (name, variant) in variants {
      result.push((*name, match variant {
        parse::Variant::Unit => {
          Variant::Unit(*name)
        }
        parse::Variant::Struct(params) => {
          Variant::Struct(*name, self.check_params(params)?)
        }
      }));
    }
    Ok(result)
  }

  /// Resolve definitions by id

  fn parsed_def(&self, id: DefId) -> &'static parse::Def {
    unsafe { &*(self.parsed_defs.get(&id).unwrap() as *const _) }
  }

  fn checked_def(&mut self, id: DefId) -> MRes<&Def> {
    match self.checked_def_hack(id) {
      Some(def) => return Ok(def),
      None => ()
    }

    let parsed_def = self.parsed_def(id);
    self.check_def(id, parsed_def)?;
    Ok(self.checked_defs.get(&id).unwrap())
  }


  fn checked_def_hack(&self, id: DefId) -> Option<&'static Def> {
    match self.checked_defs.get(&id) {
      Some(def) => Some(unsafe { &*(def as *const _) }),
      None => None
    }
  }

  /// Create scope

  fn newscope(&mut self) {
    self.scopes.push(HashMap::new());
  }

  /// Exit scope

  fn popscope(&mut self) {
    self.scopes.pop().unwrap();
  }

  /// Introduce symbol

  fn define(&mut self, name: RefStr, sym: Sym) {
    self.scopes.last_mut().unwrap().insert(name, sym);
  }

  /// Resolve symbol

  fn lookup(&self, name: RefStr) -> MRes<Sym> {
    for scope in self.scopes.iter().rev() {
      if let Some(sym) = scope.get(&name) {
        return Ok(sym.clone());
      }
    }
    Err(Box::new(UnresolvedIdentError { name }))
  }

  /// Create local variable

  fn newlocal(&mut self, def: LocalDef) -> LocalId {
    let id = LocalId(self.local_cnt);
    self.local_cnt += 1;
    
    self.define(def.name(), Sym::Local(id));
    self.local_defs.last_mut().unwrap().insert(id, def);
    id
  }

  /// Resolve local by id

  fn local_def(&self, id: LocalId) -> &LocalDef {
    self.local_defs.last().unwrap().get(&id).unwrap()
  }

  //
  // Types
  //

  fn check_ty(&mut self, ty: &parse::Ty) -> MRes<Ty> {
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
      Path(path) => {
        self.resolve_ty(path[0])?
      },
      Ptr(is_mut, base_ty) => {
        Ty::Ptr(*is_mut, Box::new(self.check_ty(base_ty)?))
      },
      Func(params, ret_ty) => {
        Ty::Func(self.check_params(params)?, Box::new(self.check_ty(ret_ty)?))
      },
      Arr(_, elem_ty) => {
        // FIXME: evaluate elem_cnt constant expression
        Ty::Arr(0, Box::new(self.check_ty(elem_ty)?))
      },
      Tuple(params) => {
        Ty::Tuple(self.check_params(params)?)
      }
    })
  }

  fn resolve_ty(&mut self, name: RefStr) -> MRes<Ty> {
    'error: loop {
      let id = match self.lookup(name)? {
        Sym::Def(id) => id,
        _ => break 'error
      };

      match self.checked_def(id)? {
        Def::Struct {..} |
        Def::Union {..} |
        Def::Enum {..} => (),
        _ => break 'error
      }

      return Ok(Ty::Ref(name, id))
    }

    Err(Box::new(UnresolvedIdentError { name }))
  }

  fn check_params(&mut self, params: &Vec<(RefStr, parse::Ty)>) -> MRes<Vec<(RefStr, Ty)>> {
    let mut result = vec![];
    for (name, ty) in params {
      result.push((*name, self.check_ty(ty)?));
    }
    Ok(result)
  }

  //
  // Expressions
  //

  fn resolve_lvalue(&mut self, path: &parse::Path) -> MRes<LValue> {
    match self.lookup(path[0])? {
      // Global definition
      Sym::Def(id) => {
        match self.checked_def(id)? {
          // Global data defintions
          Def::Data { ty, is_mut, .. } |
          Def::ExternData { ty, is_mut, .. } => {
            Ok(LValue::DataRef {
              ty: ty.clone(),
              is_mut: is_mut.clone(),
              name: path[0],
              id
            })
          }
          // Wrong kind of definition
          _ => Err(Box::new(TypeError(format!("{} cannot be used as an lvalue", path[0]))))
        }
      }
      // Function parameters
      Sym::Local(id) => {
        match self.local_def(id) {
          LocalDef::Param { ty, is_mut, .. } => {
            Ok(LValue::ParamRef {
              ty: ty.clone(),
              is_mut: is_mut.clone(),
              name: path[0],
              id
            })
          },
          LocalDef::Let { ty, is_mut, .. } => {
            Ok(LValue::LetRef {
              ty: ty.clone(),
              is_mut: is_mut.clone(),
              name: path[0],
              id
            })
          },
          _ => Err(Box::new(TypeError(format!("{} cannot be used as an lvalue", path[0]))))
        }
      }
    }
  }

  fn resolve_rvalue(&mut self, path: &parse::Path) -> MRes<RValue> {
    match self.lookup(path[0])? {
      // Global definition
      Sym::Def(id) => {
        match self.checked_def(id)? {
          // Constant definition
          Def::Const { name, ty, .. } => {
            Ok(RValue::ConstRef {
              ty: ty.clone(),
              name: *name,
              id
            })
          }
          // Function definition
          Def::Func { name, ty, .. } |
          Def::ExternFunc { name, ty, .. } => {
            Ok(RValue::FuncRef {
              ty: ty.clone(),
              name: *name,
              id
            })
          }
          // Data defintions
          Def::Data { ty, is_mut, .. } |
          Def::ExternData { ty, is_mut, .. } => {
            let lvalue = LValue::DataRef {
              ty: ty.clone(),
              is_mut: is_mut.clone(),
              name: path[0],
              id
            };
            Ok(self.load_lvalue(lvalue))
          }
          // Wrong kind of definition
          _ => Err(Box::new(TypeError(format!("{} cannot be used as an rvalue", path[0]))))
        }
      }
      // Function parameters
      Sym::Local(id) => {
        match self.local_def(id) {
          LocalDef::Param { ty, is_mut, .. } => {
            let lvalue = LValue::ParamRef {
              ty: ty.clone(),
              is_mut: is_mut.clone(),
              name: path[0],
              id
            };
            Ok(self.load_lvalue(lvalue))
          },
          LocalDef::Let { ty, is_mut, .. } => {
            let lvalue = LValue::LetRef {
              ty: ty.clone(),
              is_mut: is_mut.clone(),
              name: path[0],
              id
            };
            Ok(self.load_lvalue(lvalue))
          }
          _ => Err(Box::new(TypeError(format!("{} cannot be used as an rvalue", path[0]))))
        }
      }
    }
  }

  fn load_lvalue(&self, lvalue: LValue) -> RValue {
    RValue::Load {
      ty: lvalue.ty().clone(),
      arg: Box::new(lvalue)
    }
  }

  fn infer_dot(&mut self, arg: &parse::Expr, name: RefStr) -> MRes<LValue> {
    // Infer argument type
    let arg = self.infer_lvalue(arg)?;

    'error: loop {
      // Find parameter list
      let params = match arg.ty() {
        Ty::Ref(_, id) => match self.checked_def(*id)? {
          Def::Struct { params: Some(params), .. } => params,
          Def::Union { params: Some(params), .. } => params,
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

    Err(Box::new(
      TypeError(format!("Type {:?} has no field named {}", arg.ty(), name))))
  }

  fn infer_index(&mut self, arg: &parse::Expr, idx: &parse::Expr) -> MRes<LValue> {
    // Infer array type
    let arg = self.infer_lvalue(arg)?;

    // Find element type
    let elem_ty = match arg.ty() {
      Ty::Arr(_, elem_ty) => &**elem_ty,
      _ => return Err(Box::new(
        TypeError(format!("Cannot index type {:?}", arg.ty()))))
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


  fn infer_call(&mut self, arg: &parse::Expr, args: &Vec<(RefStr, parse::Expr)>) -> MRes<RValue> {
    // Infer function type
    let arg = self.infer_rvalue(arg)?;

    // Find parameter list and return type
    let (params, ret_ty) = match arg.ty() {
      Ty::Func(params, ret_ty) => (params, &**ret_ty),
      _ => return Err(Box::new(
        TypeError(format!("Cannot call type {:?}", arg.ty()))))
    };

    // Typecheck call arguments
    let mut nargs = vec![];

    if args.len() != params.len() {
      return Err(Box::new(
        TypeError(format!("Wrong number of arguments for {:?}", arg.ty()))))
    }

    for ((arg_name, arg_val), (param_name, param_ty)) in args.iter().zip(params.iter()) {
      if arg_name != param_name {
        return Err(Box::new(
          TypeError(format!("Incorrect argument label {}", arg_name))))
      }
      let arg_val = self.infer_rvalue(arg_val)?;
      self.tctx.unify(arg_val.ty(), param_ty)?;
      nargs.push((*arg_name, arg_val));
    }

    Ok(RValue::Call { ty: ret_ty.clone(), arg: Box::new(arg), args: nargs })
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

  fn infer_lvalue(&mut self, expr: &parse::Expr) -> MRes<LValue> {
    use parse::Expr::*;

    Ok(match expr {
      Path(path) => {
        self.resolve_lvalue(path)?
      }
      Str(val) => {
        let ty = Ty::Arr(val.borrow_rs().len(), Box::new(self.tctx.tvar(Ty::BoundInt)));
        LValue::Str { ty, is_mut: IsMut::No, val: *val }
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

  fn infer_rvalue(&mut self, expr: &parse::Expr) -> MRes<RValue> {
    use parse::Expr::*;

    Ok(match expr {
      Null => {
        RValue::Null { ty: Ty::Tuple(vec![]) }
      }
      Path(path) => {
        self.resolve_rvalue(path)?
      }
      Str(..) | Dot(..) | Index(..) | Ind(..) => {
        let arg = self.infer_lvalue(expr)?;
        RValue::Load {
          ty: arg.ty().clone(),
          arg: Box::new(arg)
        }
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
        RValue::Char { ty: self.tctx.tvar(Ty::BoundInt), val: *val }
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
          let ty = self.check_ty(ty)?;
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
