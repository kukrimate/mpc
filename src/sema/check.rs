// SPDX-License-Identifier: GPL-2.0-only

use super::*;
use std::error;

fn unify(ty1: &mut Ty, ty2: &mut Ty) -> MRes<()> {
  use Ty::*;
  match (ty1, ty2) {
    (ty1 @ ClassAny, ty2) |
    (ty1 @ ClassNum, ty2 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|Uintn|Intn|Float|Double)) |
    (ty1 @ ClassInt, ty2 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|Uintn|Intn)) => {
      *ty1 = ty2.clone();
      Ok(())
    },
    (ty1, ty2 @ ClassAny) |
    (ty1 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|Uintn|Intn|Float|Double), ty2 @ ClassNum) |
    (ty1 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|Uintn|Intn), ty2 @ ClassInt) => {
      *ty2 = ty1.clone();
      Ok(())
    },
    (Bool, Bool) |
    (Uint8, Uint8) |
    (Int8, Int8) |
    (Uint16, Uint16) |
    (Int16, Int16) |
    (Uint32, Uint32) |
    (Int32, Int32) |
    (Uint64, Uint64) |
    (Int64, Int64) |
    (Uintn, Uintn) |
    (Intn, Intn) |
    (Float, Float) |
    (Double, Double) => {
      Ok(())
    }
    (Ref(name1, def1), Ref(name2, def2)) if def1 == def2 => {
      assert_eq!(name1, name2);
      Ok(())
    }
    (Fn(par1, ret1), Fn(par2, ret2)) if par1.len() == par2.len() => {
      for ((n1, t1), (n2, t2)) in par1.iter_mut().zip(par2.iter_mut()) {
        if n1 != n2 {
          return Err(Box::new(TypeError {}));
        }
        unify(t1, t2)?;
      }
      unify(&mut *ret1, &mut *ret2)
    }
    (Ptr(is_mut1, base1), Ptr(is_mut2, base2)) if is_mut1 == is_mut2 => {
      unify(&mut *base1, &mut *base2)
    }
    (Arr(siz1, elem1), Arr(siz2, elem2)) if siz1 == siz2 => {
      unify(&mut *elem1, &mut *elem2)
    }
    (Tuple(par1), Tuple(par2)) if par1.len() == par2.len() => {
      for ((n1, t1), (n2, t2)) in par1.iter_mut().zip(par2.iter_mut()) {
        if n1 != n2 {
          return Err(Box::new(TypeError {}));
        }
        unify(t1, t2)?;
      }
      Ok(())
    }
    _ => Err(Box::new(TypeError {}))
  }
}

/// Errors

#[derive(Debug)]
struct TypeError {}

impl fmt::Display for TypeError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Type error")
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

/// Type checker logic

struct CheckCtx {
  // Module being currenly checked
  module: Module,
  // Contexts for break/continue, and return
  loop_ty: Vec<Ty>,
  ret_ty: Vec<Ty>,
}

impl CheckCtx {
  fn new() -> Self {
    CheckCtx {
      module: Module {
        ty_defs: IndexMap::new(),
        defs: vec![ IndexMap::new() ],
      },
      loop_ty: vec![],
      ret_ty: vec![]
    }
  }

  //
  // Types
  //

  fn resolve_ty(&mut self, name: RefStr) -> MRes<Ty> {
    if let Some(ty_def) = self.module.ty_defs.get(&name) {
      Ok(Ty::Ref(name, ty_def.ptr()))
    } else {
      Err(Box::new(UnresolvedIdentError { name }))
    }
  }

  fn check_params(&mut self, params: &IndexMap<RefStr, parse::TyRef>) -> MRes<Vec<(RefStr, Ty)>> {
    let mut result = vec![];
    for (name, ty) in params {
      result.push((*name, self.check_ty(ty)?));
    }
    Ok(result)
  }

  fn check_ty(&mut self, ty: &parse::TyRef) -> MRes<Ty> {
    use parse::TyRef::*;
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
      Fn(params, ret_ty) => {
        Ty::Fn(self.check_params(params)?, Box::new(self.check_ty(ret_ty)?))
      },
      Ptr(is_mut, base_ty) => {
        Ty::Ptr(*is_mut, Box::new(self.check_ty(base_ty)?))
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

  fn check_variants(&mut self, variants: &IndexMap<RefStr, parse::Variant>) -> MRes<Vec<(RefStr, Variant)>> {
    use parse::Variant::*;

    let mut result = vec![];
    for (name, variant) in variants {
      result.push((*name, match variant {
        Unit => Variant::Unit(*name),
        Struct(params) => Variant::Struct(*name, self.check_params(params)?),
      }));
    }

    Ok(result)
  }

  fn check_ty_defs(&mut self, ty_defs: &IndexMap<RefStr, parse::TyDef>) -> MRes<()>  {
    use parse::TyDef::*;

    let mut queue = vec![];

    // Pass 1: Create objects
    for (name, ty_def) in ty_defs {
      let dummy = Own::new(TyDef::new(*name));
      queue.push((ty_def, dummy.ptr()));
      self.module.ty_defs.insert(*name, dummy);
    }

    // Pass 2: Resolve names
    for (ty_def, mut dest) in queue {
      dest.kind = match ty_def {
        Struct { params } => TyDefKind::Struct(self.check_params(params)?),
        Union { params } => TyDefKind::Union(self.check_params(params)?),
        Enum { variants } => TyDefKind::Enum(self.check_variants(variants)?),
      };
    }

    Ok(())
  }

  //
  // Definitions
  //

  fn enter(&mut self) {
    self.module.defs.push(IndexMap::new());
  }

  fn exit(&mut self) -> IndexMap<RefStr, Own<Def>> {
    self.module.defs.pop().unwrap()
  }

  fn define(&mut self, def: Def) -> Ptr<Def> {
    let def = Own::new(def);
    let ptr = def.ptr();
    self.module.defs.last_mut().unwrap().insert(def.name, def);
    ptr
  }

  fn define_param(&mut self, name: RefStr, is_mut: IsMut, ty: Ty, index: usize) -> Ptr<Def> {
    self.define(Def::with_kind(name, is_mut, ty, DefKind::Param(index)))
  }

  fn define_local(&mut self, name: RefStr, is_mut: IsMut, ty: Ty) -> Ptr<Def> {
    self.define(Def::with_kind(name, is_mut, ty, DefKind::Local))
  }

  fn resolve_def(&mut self, name: RefStr) -> MRes<Ptr<Def>> {
    for scope in self.module.defs.iter().rev() {
      if let Some(def) = scope.get(&name) {
        return Ok(def.ptr());
      }
    }
    Err(Box::new(UnresolvedIdentError { name }))
  }

  //
  // Expressions
  //

  fn infer_expr(&mut self, expr: &parse::Expr) -> MRes<Expr> {
    use parse::Expr::*;

    Ok(match expr {
      Path(path) => {
        let def = self.resolve_def(path[0])?;
        ExprRef::new(def.ty.clone(), def)
      }
      Bool(val) => {
        ExprBool::new(Ty::Bool, *val)
      }
      Int(val) => {
        ExprInt::new(Ty::ClassInt, *val)
      }
      Char(val) => {
        ExprChar::new(Ty::ClassInt, *val)
      }
      Str(val) => {
        let ty = Ty::Arr(val.borrow_rs().len(), Box::new(Ty::ClassInt));
        ExprStr::new(ty, *val)
      }
      Dot(arg, name) => {
        self.infer_dot(arg, *name)?
      }
      Call(arg, args) => {
        self.infer_call(arg, args)?
      }
      Index(arg, idx) => {
        self.infer_index(arg, idx)?
      }
      Adr(arg) => {
        let mut arg = self.infer_expr(arg)?;
        let is_mut = self.ensure_lvalue(&mut arg)?;
        ExprAdr::new(Ty::Ptr(is_mut, Box::new(arg.ty().clone())), arg)
      }
      Ind(arg) => {
        self.infer_ind(arg)?
      }
      Un(op, arg) => {
        self.infer_un(*op, arg)?
      }
      LNot(arg) => {
        let mut arg = self.infer_expr(arg)?;
        unify(arg.ty_mut(), &mut Ty::Bool)?;
        ExprLNot::new(Ty::Bool, arg)
      }
      Cast(..) => {
        todo!()
      }
      Bin(op, lhs, rhs) => {
        let (ty, lhs, rhs) = self.infer_bin(*op, lhs, rhs)?;
        ExprBin::new(ty, *op, lhs, rhs)
      }
      LAnd(lhs, rhs) => {
        let mut lhs = self.infer_expr(lhs)?;
        let mut rhs = self.infer_expr(rhs)?;
        unify(lhs.ty_mut(), &mut Ty::Bool)?;
        unify(rhs.ty_mut(), &mut Ty::Bool)?;
        ExprLAnd::new(Ty::Bool, lhs, rhs)
      }
      LOr(lhs, rhs) => {
        let mut lhs = self.infer_expr(lhs)?;
        let mut rhs = self.infer_expr(rhs)?;
        unify(lhs.ty_mut(), &mut Ty::Bool)?;
        unify(rhs.ty_mut(), &mut Ty::Bool)?;
        ExprLOr::new(Ty::Bool, lhs, rhs)
      }
      Block(body) => {
        self.enter();
        let mut nbody = vec![];
        for expr in body {
          nbody.push(self.infer_expr(expr)?);
        }
        let scope = self.exit();

        let ty = if let Some(last) = nbody.last_mut() {
          last.ty().clone()
        } else {
          Ty::Tuple(vec![])
        };

        ExprBlock::new(ty, scope, nbody)
      }
      As(lhs, rhs) => {
        // Infer argument types
        let mut lhs = self.infer_expr(lhs)?;
        let mut rhs = self.infer_expr(rhs)?;

        // Make sure lhs is mutable
        match self.ensure_lvalue(&mut lhs)? {
          IsMut::Yes => (),
          _ => return Err(Box::new(TypeError {})),
        };

        // Both sides must have identical types
        unify(lhs.ty_mut(), rhs.ty_mut())?;

        ExprAs::new(Ty::Tuple(vec![]), lhs, rhs)
      }
      Rmw(op, lhs, rhs) => {
        // Infer and check argument types
        let (_, mut lhs, rhs) = self.infer_bin(*op, lhs, rhs)?;

        // Make sure lhs is mutable
        match self.ensure_lvalue(&mut lhs)? {
          IsMut::Yes => (),
          _ => return Err(Box::new(TypeError {})),
        };

        ExprRmw::new(Ty::Tuple(vec![]), *op, lhs, rhs)
      }
      Continue => {
        ExprContinue::new(Ty::Tuple(vec![]))
      }
      Break(Some(arg)) => {
        let mut arg = self.infer_expr(&*arg)?;

        // Can only have break inside a loop
        let loop_ty = match self.loop_ty.last_mut() {
          Some(loop_ty) => loop_ty,
          None => return Err(Box::new(TypeError {})),
        };

        // Unify function return type with the returned value's type
        unify(loop_ty, arg.ty_mut())?;

        ExprBreak::new(Ty::Tuple(vec![]), Some(arg))
      }
      Break(None) => {
        // Can only have break inside a loop
        let loop_ty = match self.loop_ty.last_mut() {
          Some(loop_ty) => loop_ty,
          None => return Err(Box::new(TypeError {})),
        };

        // Loop type must be an empty tuple
        unify(loop_ty, &mut Ty::Tuple(vec![]))?;

        ExprBreak::new(Ty::Tuple(vec![]), None)
      }
      Return(Some(arg)) => {
        let mut arg = self.infer_expr(&*arg)?;

        // Can only have return inside a function
        let ret_ty = match self.ret_ty.last_mut() {
          Some(ret_ty) => ret_ty,
          None => return Err(Box::new(TypeError {})),
        };

        // Unify function return type with the returned value's type
        unify(ret_ty, arg.ty_mut())?;

        ExprReturn::new(Ty::Tuple(vec![]), Some(arg))
      }
      Return(None) => {
        // Can only have return inside a function
        let ret_ty = match self.ret_ty.last_mut() {
          Some(ret_ty) => ret_ty,
          None => return Err(Box::new(TypeError {})),
        };

        // The return type must be an empty tuple here
        unify(ret_ty, &mut Ty::Tuple(vec![]))?;

        ExprReturn::new(Ty::Tuple(vec![]), None)
      }
      Let(name, is_mut, ty, init) => {
        // Check initializer
        let mut init = self.infer_expr(init)?;

        // Unify type annotation with initializer type
        let ty = if let Some(ty) = ty {
          let mut ty = self.check_ty(ty)?;
          unify(&mut ty, init.ty_mut())?;
          ty
        } else {
          init.ty().clone()
        };

        // Define symbol
        let def = self.define_local(*name, *is_mut, ty);

        // Add let expression
        ExprLet::new(Ty::Tuple(vec![]), def, init)
      }
      If(cond, tbody, Some(ebody)) => {
        let mut cond = self.infer_expr(cond)?;
        unify(cond.ty_mut(), &mut Ty::Bool)?;

        let mut tbody = self.infer_expr(tbody)?;
        let mut ebody = self.infer_expr(ebody)?;
        unify(tbody.ty_mut(), ebody.ty_mut())?;

        ExprIf::new(tbody.ty().clone(), cond, tbody, ebody)
      }
      If(cond, tbody, None) => {
        let mut cond = self.infer_expr(cond)?;
        unify(cond.ty_mut(), &mut Ty::Bool)?;

        let mut tbody = self.infer_expr(tbody)?;
        let mut ebody = ExprBlock::new(Ty::Tuple(vec![]), IndexMap::new(), vec![]);
        unify(tbody.ty_mut(), ebody.ty_mut())?;

        ExprIf::new(tbody.ty().clone(), cond, tbody, ebody)
      }
      While(cond, body) => {
        let cond = self.infer_expr(cond)?;
        self.loop_ty.push(Ty::Tuple(vec![]));
        let body = self.infer_expr(body)?;
        self.loop_ty.pop();
        ExprWhile::new(Ty::Tuple(vec![]), cond, body)
      }
      Loop(body) => {
        self.loop_ty.push(Ty::ClassAny);
        let body = self.infer_expr(body)?;
        ExprLoop::new(self.loop_ty.pop().unwrap(), body)
      }
    })
  }

  fn ensure_lvalue(&mut self, lval: &mut Expr) -> MRes<IsMut> {
    match lval.kind_mut() {
      ExprKind::Ref(expr) => Ok(expr.def.is_mut),
      ExprKind::Str(..) => Ok(IsMut::No),
      ExprKind::Dot(expr) => Ok(expr.is_mut),
      ExprKind::Index(expr) => Ok(expr.is_mut),
      ExprKind::Ind(expr) => Ok(expr.is_mut),
      _ => return Err(Box::new(TypeError {}))
    }
  }

  fn infer_dot(&mut self, arg: &parse::Expr, name: RefStr) -> MRes<Expr> {
    // Infer argument type
    let mut arg = self.infer_expr(arg)?;
    // Infer mutablity
    let is_mut = self.ensure_lvalue(&mut arg)?;

    // Find parameter list
    let params = match arg.ty() {
      Ty::Ref(_, ty_def) => match &ty_def.kind {
        TyDefKind::Struct(params) | TyDefKind::Union(params) => params,
        _ => return Err(Box::new(TypeError {})),
      },
      Ty::Tuple(params) => params,
      _ => return Err(Box::new(TypeError {}))
    };

    // Find parameter
    let (idx, param_ty) = match lin_search(params, &name) {
      Some(val) => val,
      None => return Err(Box::new(TypeError {}))
    };

    Ok(ExprDot::new(param_ty.clone(), is_mut, arg, name, idx))
  }

  fn infer_call(&mut self, arg: &parse::Expr, args: &IndexMap<RefStr, parse::Expr>) -> MRes<Expr> {
    // Infer function type
    let arg = self.infer_expr(arg)?;

    // Find parameter list and return type
    let (params, ret_ty) = match arg.ty() {
      Ty::Fn(params, ret_ty) => (params, &**ret_ty),
      _ => return Err(Box::new(TypeError {}))
    };

    // Typecheck call arguments
    let mut nargs = vec![];

    if args.len() != params.len() {
      return Err(Box::new(TypeError {}))
    }

    for ((arg_name, arg_val), (param_name, param_ty)) in args.iter().zip(params.iter()) {
      if arg_name != param_name {
        return Err(Box::new(TypeError {}))
      }
      let mut arg_val = self.infer_expr(arg_val)?;
      let mut param_ty = param_ty.clone();
      unify(arg_val.ty_mut(), &mut param_ty)?;
      nargs.push((*arg_name, arg_val));
    }

    Ok(ExprCall::new(ret_ty.clone(), arg, nargs))
  }

  fn infer_index(&mut self, arg: &parse::Expr, idx: &parse::Expr) -> MRes<Expr> {
    // Infer array type
    let mut arg = self.infer_expr(arg)?;
    // Infer mutablity
    let is_mut = self.ensure_lvalue(&mut arg)?;

    // Find element type
    let elem_ty = match arg.ty() {
      Ty::Arr(_, elem_ty) => &**elem_ty,
      _ => return Err(Box::new(TypeError {}))
    };

    // Check index type
    let mut idx = self.infer_expr(idx)?;
    unify(idx.ty_mut(), &mut Ty::Uintn)?;

    Ok(ExprIndex::new(elem_ty.clone(), is_mut, arg, idx))
  }

  fn infer_ind(&mut self, arg: &parse::Expr) -> MRes<Expr> {
    // Infer pointer type
    let arg = self.infer_expr(arg)?;

    // Find base type
    let (is_mut, base_ty) = match arg.ty() {
      Ty::Ptr(is_mut, base_ty) => (*is_mut, &**base_ty),
      _ => return Err(Box::new(TypeError {}))
    };

    Ok(ExprInd::new(base_ty.clone(), is_mut, arg))
  }

  fn infer_un(&mut self, op: UnOp, arg: &parse::Expr) -> MRes<Expr> {
    // Infer argument type
    let mut arg = self.infer_expr(arg)?;

    // Check argument type
    match op {
      UnOp::UPlus | UnOp::UMinus => {
        unify(arg.ty_mut(), &mut Ty::ClassNum)?;
      }
      UnOp::Not => {
        unify(arg.ty_mut(), &mut Ty::ClassInt)?;
      }
    }

    Ok(ExprUn::new(arg.ty().clone(), op, arg))
  }

  fn infer_bin(&mut self, op: BinOp, lhs: &parse::Expr, rhs: &parse::Expr) -> MRes<(Ty, Expr, Expr)> {
    // Infer argument types
    let mut lhs = self.infer_expr(lhs)?;
    let mut rhs = self.infer_expr(rhs)?;

    // Check argument types and infer result type
    let ty = match op {
      // Both arguments must have matching numeric types
      // Result has the same type as the arguments
      BinOp::Mul | BinOp::Div | BinOp::Add | BinOp::Sub => {
        unify(lhs.ty_mut(), &mut Ty::ClassNum)?;
        unify(lhs.ty_mut(), rhs.ty_mut())?;
        lhs.ty().clone()
      }

      // Both arguments must have matching integer types
      // Result has the same type as the arguments
      BinOp::Mod | BinOp::And | BinOp::Xor | BinOp::Or  => {
        unify(lhs.ty_mut(), &mut Ty::ClassInt)?;
        unify(lhs.ty_mut(), rhs.ty_mut())?;
        lhs.ty().clone()
      }

      // Both arguments must have integer types
      // Result has the left argument's type
      BinOp::Lsh | BinOp::Rsh => {
        unify(lhs.ty_mut(), &mut Ty::ClassInt)?;
        unify(rhs.ty_mut(), &mut Ty::ClassInt)?;
        lhs.ty().clone()
      }

      // Both arguments must have matching numeric types
      // Result is a boolean
      BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
        unify(lhs.ty_mut(), &mut Ty::ClassNum)?;
        unify(lhs.ty_mut(), rhs.ty_mut())?;
        Ty::Bool
      }
    };

    Ok((ty, lhs, rhs))
  }

  fn check_module(&mut self, module: &parse::Module) -> MRes<()> {
    // Populate type definitions
    self.check_ty_defs(&module.ty_defs)?;

    let mut queue = vec![];

    // Create symbols for objects
    for (name, def) in &module.defs {
      match def {
        parse::Def::Const { ty, val } => {
          // Infer
          let ty = self.check_ty(ty)?;
          let val = self.infer_expr(val)?;
          self.define(Def::with_kind(*name, IsMut::No, ty, DefKind::Const(val)));
        }
        parse::Def::Data { is_mut, ty, .. } => {
          let ty = self.check_ty(ty)?;
          let ptr = self.define(Def::empty(*name, *is_mut, ty));
          queue.push((ptr, def));
        }
        parse::Def::Fn { params, ret_ty, .. } => {
          let mut new_params = vec![];
          for (name, (_, ty)) in params {
            new_params.push((*name, self.check_ty(ty)?));
          }
          let ty = Ty::Fn(new_params, Box::new(self.check_ty(ret_ty)?));
          let ptr = self.define(Def::empty(*name, IsMut::No, ty));
          queue.push((ptr, def));
        }
        parse::Def::ExternData { is_mut, ty } => {
          let ty = self.check_ty(ty)?;
          self.define(Def::with_kind(*name, *is_mut, ty, DefKind::ExternData));
        }
        parse::Def::ExternFn { params, ret_ty } => {
          let ty = Ty::Fn(self.check_params(params)?,
                          Box::new(self.check_ty(ret_ty)?));
          self.define(Def::with_kind(*name, IsMut::No, ty, DefKind::ExternFunc));
        }
      };
    }

    // Type check object bodies
    for (mut ptr, def) in queue {
      // Generate object bodies
      match def {
        parse::Def::Data { init, .. } => {
          // Check initializer type
          let mut init = self.infer_expr(init)?;
          unify(init.ty_mut(), &mut ptr.ty)?;

          // Complete definition
          ptr.kind = DefKind::Data(init);
        }
        parse::Def::Fn { params, ret_ty, body, .. } => {
          // FIXME: this could be made better by not re-checking ret_ty
          // and re-using the value from the first pass
          self.enter();

          // Create parameter symbols
          for (index, (name, (is_mut, ty))) in params.iter().enumerate() {
            let ty = self.check_ty(ty)?;
            self.define_param(*name, *is_mut, ty, index);
          }

          // Typecheck body
          let mut body = self.infer_expr(body)?;
          let mut ret_ty = self.check_ty(ret_ty)?;
          unify(body.ty_mut(), &mut ret_ty)?;

          // Exit param scope
          let params = self.exit();

          // Complete definition
          ptr.kind = DefKind::Func(params, body);
        }
        _ => ()
      }
    }

    Ok(())
  }
}

pub fn check_module(parsed_module: &parse::Module) -> MRes<Module> {
  let mut ctx = CheckCtx::new();
  ctx.check_module(parsed_module)?;
  Ok(ctx.module)
}
