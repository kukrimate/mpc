// SPDX-License-Identifier: GPL-2.0-only

use super::*;
use std::error;

fn unify(ty1: Ty, ty2: Ty) -> MRes<Ty> {
  use Ty::*;
  match (ty1, ty2) {
    (ClassAny, ty2) |
    (ClassNum, ty2 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|Uintn|Intn|Float|Double)) |
    (ClassInt, ty2 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|Uintn|Intn)) => Ok(ty2),
    (ty1, ClassAny) |
    (ty1 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|Uintn|Intn|Float|Double), ClassNum) |
    (ty1 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|Uintn|Intn), ClassInt) => Ok(ty1),
    (Bool, Bool) => Ok(Bool),
    (Uint8, Uint8) => Ok(Uint8),
    (Int8, Int8) => Ok(Int8),
    (Uint16, Uint16) => Ok(Uint16),
    (Int16, Int16) => Ok(Int16),
    (Uint32, Uint32) => Ok(Uint32),
    (Int32, Int32) => Ok(Int32),
    (Uint64, Uint64) => Ok(Uint64),
    (Int64, Int64) => Ok(Int64),
    (Uintn, Uintn) => Ok(Uintn),
    (Intn, Intn) => Ok(Intn),
    (Float, Float) => Ok(Float),
    (Double, Double) => Ok(Double),
    (Ref(name1, def1), Ref(name2, def2)) if def1 == def2 => {
      assert_eq!(name1, name2);
      Ok(Ref(name1, def1))
    },
    (Fn(par1, ret1), Fn(par2, ret2)) if par1.len() == par2.len() => {
      let mut npar = vec![];
      for ((n1, t1), (n2, t2)) in par1.into_iter().zip(par2.into_iter()) {
        if n1 != n2 {
          return Err(Box::new(TypeError {}));
        }
        npar.push((n1, unify(t1, t2)?));
      }
      Ok(Ty::Fn(npar, Box::new(unify(*ret1, *ret2)?)))
    }
    (Ptr(is_mut1, base1), Ptr(is_mut2, base2)) if is_mut1 == is_mut2 => {
      Ok(Ty::Ptr(is_mut1, Box::new(unify(*base1, *base2)?)))
    }
    (Arr(siz1, elem1), Arr(siz2, elem2)) if siz1 == siz2 => {
      Ok(Ty::Arr(siz1, Box::new(unify(*elem1, *elem2)?)))
    }
    (Tuple(par1), Tuple(par2)) if par1.len() == par2.len() => {
      let mut npar = vec![];
      for ((n1, t1), (n2, t2)) in par1.into_iter().zip(par2.into_iter()) {
        if n1 != n2 {
          return Err(Box::new(TypeError {}));
        }
        npar.push((n1, unify(t1, t2)?));
      }
      Ok(Ty::Tuple(npar))
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
      queue.push((*name, ty_def, dummy.ptr()));
      self.module.ty_defs.insert(*name, dummy);
    }

    // Pass 2: Resolve names
    for (name, ty_def, mut dest) in queue {
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

  fn define_const(&mut self, name: RefStr, ty: Ty, val: Expr) -> Ptr<Def> {
    self.define(Def::with_kind(name, IsMut::No, ty, DefKind::Const(val)))
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
        Expr::new(def.ty.clone(), ExprKind::Ref(def))
      }
      Bool(val) => {
        Expr::new(Ty::Bool, ExprKind::Bool(*val))
      }
      Int(val) => {
        Expr::new(Ty::ClassInt, ExprKind::Int(*val))
      }
      Char(val) => {
        Expr::new(Ty::ClassInt, ExprKind::Char(*val))
      }
      Str(val) => {
        let ty = Ty::Arr(val.borrow_rs().len(), Box::new(Ty::ClassInt));
        Expr::new(ty, ExprKind::Str(*val))
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
        let arg = self.infer_expr(arg)?;
        let is_mut = self.ensure_lvalue(&arg)?;
        Expr::new(Ty::Ptr(is_mut, Box::new(arg.ty.clone())), ExprKind::Adr(Box::new(arg)))
      }
      Ind(arg) => {
        self.infer_ind(arg)?
      }
      Un(op, arg) => {
        self.infer_un(*op, arg)?
      }
      Cast(arg, ty) => {
        todo!()
      }
      Bin(op, lhs, rhs) => {
        let (ty, lhs, rhs) = self.infer_bin(*op, lhs, rhs)?;
        Expr::new(ty, ExprKind::Bin(*op, Box::new(lhs), Box::new(rhs)))
      }
      Rmw(op, lhs, rhs) => {
        // Infer and check argument types
        let (_, lhs, rhs) = self.infer_bin(*op, lhs, rhs)?;

        // Make sure lhs is mutable
        match self.ensure_lvalue(&lhs)? {
          IsMut::Yes => (),
          _ => return Err(Box::new(TypeError {})),
        };

        Expr::new(Ty::Tuple(vec![]), ExprKind::Rmw(*op, Box::new(lhs), Box::new(rhs)))
      }
      As(lhs, rhs) => {
        // Infer argument types
        let mut lhs = self.infer_expr(lhs)?;
        let mut rhs = self.infer_expr(rhs)?;

        // Make sure lhs is mutable
        match self.ensure_lvalue(&lhs)? {
          IsMut::Yes => (),
          _ => return Err(Box::new(TypeError {})),
        };

        // Both sides must have identical types
        let ty = unify(lhs.ty, rhs.ty)?;
        lhs.ty = ty.clone();
        rhs.ty = ty;

        Expr::new(Ty::Tuple(vec![]), ExprKind::As(Box::new(lhs), Box::new(rhs)))
      }
      Block(body) => {
        self.enter();
        let mut nbody = vec![];
        for expr in body {
          nbody.push(self.infer_expr(expr)?);
        }
        let scope = self.exit();

        let ty = if let Some(expr) = nbody.last() {
          expr.ty.clone()
        } else {
          Ty::Tuple(vec![])
        };

        Expr::new(ty, ExprKind::Block(scope, nbody))
      }
      Continue => {
        Expr::new(Ty::Tuple(vec![]), ExprKind::Continue)
      }
      Break(Some(arg)) => {
        let mut arg = self.infer_expr(&*arg)?;

        // Can only have break inside a loop
        let loop_ty = match self.loop_ty.last_mut() {
          Some(loop_ty) => loop_ty,
          None => return Err(Box::new(TypeError {})),
        };

        // Unify function return type with the returned value's type
        *loop_ty = unify(loop_ty.clone(), arg.ty)?;
        arg.ty = loop_ty.clone();

        Expr::new(Ty::Tuple(vec![]), ExprKind::Break(Some(Box::new(arg))))
      }
      Break(None) => {
        // Can only have break inside a loop
        let loop_ty = match self.loop_ty.last_mut() {
          Some(loop_ty) => loop_ty,
          None => return Err(Box::new(TypeError {})),
        };

        // Loop type must be an empty tuple
        *loop_ty = unify(loop_ty.clone(), Ty::Tuple(vec![]))?;

        Expr::new(Ty::Tuple(vec![]), ExprKind::Break(None))
      }
      Return(Some(arg)) => {
        let mut arg = self.infer_expr(&*arg)?;

        // Can only have return inside a function
        let ret_ty = match self.ret_ty.last_mut() {
          Some(ret_ty) => ret_ty,
          None => return Err(Box::new(TypeError {})),
        };

        // Unify function return type with the returned value's type
        *ret_ty = unify(ret_ty.clone(), arg.ty)?;
        arg.ty = ret_ty.clone();

        Expr::new(Ty::Tuple(vec![]), ExprKind::Return(Some(Box::new(arg))))
      }
      Return(None) => {
        // Can only have return inside a function
        let ret_ty = match self.ret_ty.last_mut() {
          Some(ret_ty) => ret_ty,
          None => return Err(Box::new(TypeError {})),
        };

        // The return type must be an empty tuple here
        *ret_ty = unify(ret_ty.clone(), Ty::Tuple(vec![]))?;

        Expr::new(Ty::Tuple(vec![]), ExprKind::Return(None))
      }
      Let(name, is_mut, ty, init) => {
        // Check initializer
        let init = self.infer_expr(init)?;

        // Derive declared type
        let ty = if let Some(ty) = ty {
          let ty = self.check_ty(ty)?;
          unify(ty, init.ty.clone())?
        } else {
          init.ty.clone()
        };

        // Define symbol
        let def = self.define_local(*name, *is_mut, ty);

        // Add let expression
        Expr::new(Ty::Tuple(vec![]), ExprKind::Let(def, Box::new(init)))
      }
      If(cond, tbody, Some(ebody)) => {
        let cond = self.infer_expr(cond)?;
        let tbody = self.infer_expr(tbody)?;
        let ebody = self.infer_expr(ebody)?;
        Expr::new(unify(tbody.ty.clone(), ebody.ty.clone())?,
          ExprKind::If(Box::new(cond), Box::new(tbody), Box::new(ebody)))
      }
      If(cond, tbody, None) => {
        let cond = self.infer_expr(cond)?;
        let tbody = self.infer_expr(tbody)?;
        let ebody = Expr::new(Ty::Tuple(vec![]),
                          ExprKind::Block(IndexMap::new(), vec![]));
        Expr::new(unify(tbody.ty.clone(), ebody.ty.clone())?,
          ExprKind::If(Box::new(cond), Box::new(tbody), Box::new(ebody)))
      }
      While(cond, body) => {
        let cond = self.infer_expr(cond)?;
        self.loop_ty.push(Ty::Tuple(vec![]));
        let body = self.infer_expr(body)?;
        self.loop_ty.pop();
        Expr::new(Ty::Tuple(vec![]), ExprKind::While(Box::new(cond), Box::new(body)))
      }
      Loop(body) => {
        self.loop_ty.push(Ty::ClassAny);
        let body = self.infer_expr(body)?;
        Expr::new(self.loop_ty.pop().unwrap(), ExprKind::Loop(Box::new(body)))
      }
    })
  }

  fn ensure_lvalue(&mut self, lval: &Expr) -> MRes<IsMut> {
    match &lval.kind {
      ExprKind::Ref(def) => Ok(def.is_mut),
      ExprKind::Str(_) => Ok(IsMut::No),
      ExprKind::Dot(is_mut, ..) |
      ExprKind::Index(is_mut, ..) |
      ExprKind::Ind(is_mut, ..) => Ok(*is_mut),
      _ => return Err(Box::new(TypeError {}))
    }
  }

  fn infer_dot(&mut self, arg: &parse::Expr, name: RefStr) -> MRes<Expr> {
    // Infer argument type
    let arg = self.infer_expr(arg)?;
    // Infer mutablity
    let is_mut = self.ensure_lvalue(&arg)?;

    // Find parameter list
    let params = match &arg.ty {
      Ty::Ref(_, ty_def) => match &ty_def.kind {
        TyDefKind::Struct(params) | TyDefKind::Union(params) => params,
        _ => return Err(Box::new(TypeError {})),
      },
      Ty::Tuple(params) => params,
      _ => return Err(Box::new(TypeError {}))
    };

    // Find parameter
    let param_ty = match lin_search(params, &name) {
      Some(param_ty) => param_ty,
      None => return Err(Box::new(TypeError {}))
    };

    Ok(Expr::new(param_ty.clone(), ExprKind::Dot(is_mut, Box::new(arg), name)))
  }

  fn infer_call(&mut self, arg: &parse::Expr, args: &IndexMap<RefStr, parse::Expr>) -> MRes<Expr> {
    // Infer function type
    let arg = self.infer_expr(arg)?;

    // Find parameter list and return type
    let (params, ret_ty) = match &arg.ty {
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
      arg_val.ty = unify(arg_val.ty, param_ty.clone())?;
      nargs.push((*arg_name, arg_val));
    }

    Ok(Expr::new(ret_ty.clone(), ExprKind::Call(Box::new(arg), nargs)))
  }

  fn infer_index(&mut self, arg: &parse::Expr, idx: &parse::Expr) -> MRes<Expr> {
    // Infer array type
    let arg = self.infer_expr(arg)?;
    // Infer mutablity
    let is_mut = self.ensure_lvalue(&arg)?;

    // Find element type
    let elem_ty = match &arg.ty {
      Ty::Arr(_, elem_ty) => &**elem_ty,
      _ => return Err(Box::new(TypeError {}))
    };

    // Check index type
    let mut idx = self.infer_expr(idx)?;
    idx.ty = unify(idx.ty, Ty::Uintn)?;

    Ok(Expr::new(elem_ty.clone(), ExprKind::Index(is_mut, Box::new(arg), Box::new(idx))))
  }

  fn infer_ind(&mut self, arg: &parse::Expr) -> MRes<Expr> {
    // Infer pointer type
    let arg = self.infer_expr(arg)?;

    // Find base type
    let (is_mut, base_ty) = match &arg.ty {
      Ty::Ptr(is_mut, base_ty) => (*is_mut, &**base_ty),
      _ => return Err(Box::new(TypeError {}))
    };

    Ok(Expr::new(base_ty.clone(), ExprKind::Ind(is_mut, Box::new(arg))))
  }

  fn infer_un(&mut self, op: UnOp, arg: &parse::Expr) -> MRes<Expr> {
    // Infer argument type
    let mut arg = self.infer_expr(arg)?;

    // Check argument type
    match op {
      UnOp::UPlus | UnOp::UMinus => {
        arg.ty = unify(arg.ty, Ty::ClassNum)?;
      }
      UnOp::Not => {
        arg.ty = unify(arg.ty, Ty::ClassInt)?;
      }
      UnOp::LNot => {
        arg.ty = unify(arg.ty, Ty::Bool)?;
      }
    }

    Ok(Expr::new(arg.ty.clone(), ExprKind::Un(op, Box::new(arg))))
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
        let ty = unify(lhs.ty, Ty::ClassNum)?;
        let ty = unify(ty, rhs.ty)?;
        lhs.ty = ty.clone();
        rhs.ty = ty.clone();
        ty
      }

      // Both arguments must have matching integer types
      // Result has the same type as the arguments
      BinOp::Mod | BinOp::And | BinOp::Xor | BinOp::Or  => {
        let ty = unify(lhs.ty, Ty::ClassInt)?;
        let ty = unify(ty, rhs.ty)?;
        lhs.ty = ty.clone();
        rhs.ty = ty.clone();
        ty
      }

      // Both arguments must have integer types
      // Result has the left argument's type
      BinOp::Lsh | BinOp::Rsh => {
        lhs.ty = unify(lhs.ty, Ty::ClassInt)?;
        rhs.ty = unify(rhs.ty, Ty::ClassInt)?;
        lhs.ty.clone()
      }

      // Both arguments must have matching numeric types
      // Result is a boolean
      BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
        let ty = unify(lhs.ty, Ty::ClassNum)?;
        let ty = unify(ty, rhs.ty)?;
        lhs.ty = ty.clone();
        rhs.ty = ty.clone();
        Ty::Bool
      }

      // Both argument must be booleans
      // Result is a boolean
      BinOp::LAnd | BinOp::LOr => {
        lhs.ty = unify(lhs.ty, Ty::Bool)?;
        rhs.ty = unify(rhs.ty, Ty::Bool)?;
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
          self.define_const(*name, ty, val);
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
          init.ty = unify(init.ty, ptr.ty.clone())?;

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
          let ret_ty = self.check_ty(ret_ty)?;
          body.ty = unify(body.ty, ret_ty)?;

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
