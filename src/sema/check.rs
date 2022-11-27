// SPDX-License-Identifier: GPL-2.0-only

use super::*;

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

struct LocalCtx<'a> {
  global: &'a mut CheckCtx,

  // Symbol table
  scopes: Vec<HashMap<RefStr, Sym>>,

  // Type variable context
  tctx: TVarCtx,

  // Function return types
  ret_ty: Option<Ty>,
  // Function local variables
  locals: usize,

  // Loop types
  loop_ty: Vec<Ty>,
}

#[derive(Clone)]
enum Sym {
  Param(Ty, IsMut, usize),
  Local(Ty, IsMut, usize),
}

impl<'a> LocalCtx<'a> {

  fn new(global: &'a mut CheckCtx) -> Self {
    Self {
      global: global,
      scopes: Vec::new(),
      tctx: TVarCtx::new(),
      ret_ty: None,
      locals: 0,
      loop_ty: Vec::new(),
    }
  }

  /// Resolve definition

  fn resolve(&self, name: RefStr) -> Option<Sym> {
    for scope in self.scopes.iter().rev() {
      if let Some(sym) = scope.get(&name) {
        return Some(sym.clone());
      }
    }
    None
  }

  /// Introduce definition

  fn define(&mut self, name: RefStr, sym: Sym) {
    self.scopes.last_mut().unwrap().insert(name, sym);
  }

  /// Create local variable

  fn local_def(&mut self) -> usize {
    let index = self.locals;
    self.locals += 1;
    index
  }

  /// Scope a set of statements

  fn scoped<F, R>(&mut self, f: F) -> MRes<R>
    where F: Fn(&mut LocalCtx) -> MRes<R>
  {
    self.scopes.push(HashMap::new());
    let result = f(self);
    self.scopes.pop();
    result
  }

  //
  // Expressions
  //

  fn resolve_lvalue(&self, path: &parse::Path) -> MRes<LValue> {
    // Resolve local
    if let Some(sym) = self.resolve(path[0]) {
      return Ok(match sym {
        // Function parameters
        Sym::Param(ty, is_mut, index) => {
          LValue::ParamRef {
            ty: ty.clone(),
            is_mut: is_mut.clone(),
            name: path[0],
            index: index
          }
        }
        // Local variables
        Sym::Local(ty, is_mut, index) => {
          LValue::LocalRef {
            ty: ty.clone(),
            is_mut: is_mut.clone(),
            name: path[0],
            index: index
          }
        }
      });
    }

    // Resolve global
    let def = self.global.resolve(path[0])?;
    match self.global.module.def(def) {
      // Global data defintions
      Def::Data { ty, is_mut, .. } |
      Def::ExternData { ty, is_mut, .. } => {
        Ok(LValue::DataRef {
          ty: ty.clone(),
          is_mut: is_mut.clone(),
          name: path[0],
          def: def
        })
      }
      _ => Err(Box::new(
        TypeError(format!("{} cannot be used as an lvalue", path[0]))))
    }
  }

  fn resolve_rvalue(&self, path: &parse::Path) -> MRes<RValue> {
    // Resolve local
    if let Some(sym) = self.resolve(path[0]) {
      return Ok(match sym {
        // Function parameters
        Sym::Param(ty, is_mut, index) => {
          let arg = LValue::ParamRef {
            ty: ty.clone(),
            is_mut: is_mut.clone(),
            name: path[0],
            index: index
          };
          RValue::Load {
            ty: ty.clone(),
            arg: Box::new(arg)
          }
        }
        // Local variables
        Sym::Local(ty, is_mut, index) => {
          let arg = LValue::LocalRef {
            ty: ty.clone(),
            is_mut: is_mut.clone(),
            name: path[0],
            index: index
          };
          RValue::Load {
            ty: ty.clone(),
            arg: Box::new(arg)
          }
        }
      });
    }

    // Resolve global
    let def = self.global.resolve(path[0])?;
    match self.global.module.def(def) {
      Def::Const { name, ty, .. } => {
        Ok(RValue::ConstRef {
          ty: ty.clone(),
          name: *name,
          def: def
        })
      }
      Def::Func { name, ty, .. } |
      Def::ExternFunc { name, ty, .. } => {
        Ok(RValue::FuncRef {
          ty: ty.clone(),
          name: *name,
          def: def
        })
      }
      // Global data defintions
      Def::Data { ty, is_mut, .. } |
      Def::ExternData { ty, is_mut, .. } => {
        let arg = LValue::DataRef {
          ty: ty.clone(),
          is_mut: is_mut.clone(),
          name: path[0],
          def: def
        };
        Ok(RValue::Load {
          ty: ty.clone(),
          arg: Box::new(arg)
        })
      }
      _ => Err(Box::new(
        TypeError(format!("{} cannot be used as an rvalue", path[0]))))
    }
  }

  fn infer_dot(&mut self, arg: &parse::Expr, name: RefStr) -> MRes<LValue> {
    // Infer argument type
    let arg = self.infer_lvalue(arg)?;

    'error: loop {
      // Find parameter list
      let params = match arg.ty() {
        Ty::Ref(_, def) => match self.global.module.def(*def) {
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
        let body = self.scoped(|local_ctx| {
          let mut body = vec![];
          for expr in parsed_body {
            body.push(local_ctx.infer_rvalue(expr)?);
          }
          Ok(body)
        })?;

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
        let ret_ty = match &self.ret_ty {
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
          let ty = self.global.check_ty(ty)?;
          self.tctx.unify(&ty, init.ty())?;
        }

        // Add to symbol table
        let index = self.local_def();
        self.define(*name, Sym::Local(init.ty().clone(), *is_mut, index));

        // Add let expression
        RValue::Let {
          ty: Ty::Tuple(vec![]),
          def: LocalDef { name: *name, is_mut: *is_mut, ty: init.ty().clone(), index },
          init: Box::new(init)
        }
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

struct CheckCtx {
  // Module being currenly checked
  module: Module,
  // Global symbol table
  scope: HashMap<RefStr, DefId>,
}

impl CheckCtx {
  fn new() -> Self {
    Self {
      module: Module::new(),
      scope: HashMap::new(),
    }
  }

  /// Resolve global definition

  fn resolve(&self, name: RefStr) -> MRes<DefId> {
    if let Some(def) = self.scope.get(&name) {
      Ok(*def)
    } else {
      Err(Box::new(UnresolvedIdentError { name }))
    }
  }

  //
  // Types
  //

  fn resolve_ty(&mut self, name: RefStr) -> MRes<Ty> {
    let id = self.resolve(name)?;
    match self.module.def(id) {
      Def::Struct {..} |
      Def::Union {..} |
      Def::Enum {..} => {
        Ok(Ty::Ref(name, id))
      }
      _ => {
        Err(Box::new(UnresolvedIdentError { name }))
      }
    }
  }

  fn check_params(&mut self, params: &Vec<(RefStr, parse::Ty)>) -> MRes<Vec<(RefStr, Ty)>> {
    let mut result = vec![];
    for (name, ty) in params {
      result.push((*name, self.check_ty(ty)?));
    }
    Ok(result)
  }

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

  fn check_ty_defs(&mut self, defs: &HashMap<DefId, parse::Def>) -> MRes<()>  {
    use parse::Def::*;

    // Pass 1: Create definitions
    for (id, def) in defs.iter() {
      let def = match def {
        Struct { name, .. } =>  {
          Def::Struct { name: *name, params: None }
        }
        Union { name, .. } => {
          Def::Union { name: *name, params: None }
        }
        Enum { name, .. } => {
          Def::Enum { name: *name, variants: None }
        }
        _ => continue
      };

      self.module.defs.insert(*id, def);
    }

    // Pass 2: Fill bodies
    for (id, def) in defs.iter() {
      let def = match def {
        Struct { name, params, .. } => {
          Def::Struct { name: *name, params: Some(self.check_params(params)?) }
        }
        Union { name, params, .. } => {
          Def::Union { name: *name, params: Some(self.check_params(params)?) }
        }
        Enum { name, variants, .. } => {
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
          Def::Enum { name: *name, variants: Some(result) }
        }
        _ => continue
      };

      self.module.defs.insert(*id, def);
    }

    Ok(())
  }

  fn enter_data<F, R>(&mut self, f: F) -> MRes<R>
    where F: Fn(&mut LocalCtx) -> MRes<R>
  {
    let mut local_ctx = LocalCtx::new(self);
    f(&mut local_ctx)
  }

  fn enter_func<F, R>(&mut self, params: &Vec<ParamDef>, ret_ty: &Ty, f: F) -> MRes<R>
    where F: Fn(&mut LocalCtx) -> MRes<R>
  {
    let mut local_ctx = LocalCtx::new(self);
    local_ctx.scoped(|local_ctx| {
      // Define parameters
      for param in params {
        local_ctx.define(param.name,
          Sym::Param(param.ty.clone(), param.is_mut.clone(), param.index));
      }
      // Add return type
      local_ctx.ret_ty = Some(ret_ty.clone());
      // Body callback
      f(local_ctx)
    })
  }

  fn check_defs(&mut self, defs: &HashMap<DefId, parse::Def>) -> MRes<()> {
    use parse::Def::*;

    // Pass 1: Create definitions
    for (id, def) in defs.iter() {
      let def = match def {
        Const { name, ty, val } => {
          let ty = self.check_ty(ty)?;

          let val = self.enter_data(|local_ctx| {
            let mut val = local_ctx.infer_rvalue(val)?;
            local_ctx.tctx.unify(&ty, val.ty())?;
            local_ctx.tctx.fixup_rvalue(&mut val);
            Ok(val)
          })?;

          Def::Const { name: *name, ty, val }
        }
        Data { name, is_mut, ty, .. } => {
          let ty = self.check_ty(ty)?;
          Def::Data { name: *name, ty, is_mut: *is_mut, init: None }
        }
        Func { name, params, ret_ty, .. } => {
          let mut param_tys = vec![];
          let mut param_defs = vec![];

          for (index, (name, is_mut, ty)) in params.iter().enumerate() {
            let ty = self.check_ty(ty)?;
            param_tys.push((*name, ty.clone()));
            param_defs.push(ParamDef { name: *name, is_mut: *is_mut, ty, index });
          }

          let ty = Ty::Func(param_tys, Box::new(self.check_ty(ret_ty)?));

          Def::Func { name: *name, ty, params: param_defs, body: None }
        }
        ExternData { name, is_mut, ty } => {
          let ty = self.check_ty(ty)?;

          Def::ExternData { name: *name, ty, is_mut: *is_mut }
        }
        ExternFunc { name, params, ret_ty } => {
          let ty = Ty::Func(self.check_params(params)?,
                          Box::new(self.check_ty(ret_ty)?));

          Def::ExternFunc { name: *name, ty }
        }
        _ => continue,
      };

      self.module.defs.insert(*id, def);
    }

    // Pass 2: Fill bodies
    for (id, def) in defs.iter() {
      let def = match def {
        Data { name, is_mut, ty, init } => {
          let ty = self.check_ty(ty)?;

          let init = self.enter_data(|local_ctx| {
            let mut init = local_ctx.infer_rvalue(init)?;
            local_ctx.tctx.unify(&ty, init.ty())?;
            local_ctx.tctx.fixup_rvalue(&mut init);
            Ok(init)
          })?;

          Def::Data { name: *name, ty, is_mut: *is_mut, init: Some(init) }
        }
        Func { name, params, ret_ty, body, .. } => {
          let mut param_tys = vec![];
          let mut param_defs = vec![];

          for (index, (name, is_mut, ty)) in params.iter().enumerate() {
            let ty = self.check_ty(ty)?;
            param_tys.push((*name, ty.clone()));
            param_defs.push(ParamDef { name: *name, is_mut: *is_mut, ty, index });
          }

          let ret_ty = self.check_ty(ret_ty)?;

          let ty = Ty::Func(param_tys, Box::new(ret_ty.clone()));

          let body = self.enter_func(&param_defs, &ret_ty, |local_ctx| {
            let mut body = local_ctx.infer_rvalue(body)?;
            local_ctx.tctx.unify(&ret_ty, body.ty())?;
            local_ctx.tctx.fixup_rvalue(&mut body);
            Ok(body)
          })?;

          Def::Func { name: *name, ty, params: param_defs, body: Some(body) }
        }
        _ => continue
      };

      self.module.defs.insert(*id, def);
    }

    Ok(())
  }

  fn check_module(&mut self, module: &parse::Module) -> MRes<()> {
    // Build symbol table
    for (id, def) in module.defs.iter() {
      self.scope.insert(def.name(), *id);
    }

    self.check_ty_defs(&module.defs)?;
    self.check_defs(&module.defs)?;
    Ok(())
  }
}

pub fn check_module(parsed_module: &parse::Module) -> MRes<Module> {
  let mut ctx = CheckCtx::new();
  ctx.check_module(parsed_module)?;
  Ok(ctx.module)
}
