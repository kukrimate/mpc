// SPDX-License-Identifier: GPL-2.0-only

use super::*;
use std::error;

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
struct CannotUnifyError(Ty, Ty);

impl fmt::Display for CannotUnifyError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Cannot unify types {:?} and {:?}", self.0, self.1)
  }
}

impl error::Error for CannotUnifyError {}

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

/// Type unification

fn unify(ty1: &mut Ty, ty2: &mut Ty) -> MRes<()> {
  use Ty::*;
  match (ty1, ty2) {
    (ty1 @ ClassAny, ty2) |
    (ty1 @ ClassNum, ty2 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|
                            Uintn|Intn|Float|Double|ClassInt|ClassFlt|ClassNum)) |
    (ty1 @ ClassInt, ty2 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|
                            Uintn|Intn|ClassInt)) |
    (ty1 @ ClassFlt, ty2 @ (Float|Double|ClassFlt)) => {
      *ty1 = ty2.clone();
      Ok(())
    },
    (ty1, ty2 @ ClassAny) |
    (ty1 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|
            Uintn|Intn|Float|Double|ClassInt|ClassFlt), ty2 @ ClassNum) |
    (ty1 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|
            Uintn|Intn), ty2 @ ClassInt) |
    (ty1 @ (Float|Double), ty2 @ ClassFlt) => {
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
    (Func(par1, ret1), Func(par2, ret2)) if par1.len() == par2.len() => {
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
    (ty1, ty2) => {
      Err(Box::new(CannotUnifyError(ty1.clone(), ty2.clone())))
    }
  }
}

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

  //
  // Definitions
  //

  fn enter(&mut self) {
    self.module.defs.push(IndexMap::new());
  }

  fn exit(&mut self) -> IndexMap<RefStr, Own<Def>> {
    self.module.defs.pop().unwrap()
  }

  fn define(&mut self, name: RefStr, def: Def) -> Ptr<Def> {
    let def = Own::new(def);
    let ptr = def.ptr();
    self.module.defs.last_mut().unwrap().insert(name, def);
    ptr
  }

  fn define_param(&mut self, name: RefStr, is_mut: IsMut, ty: Ty, index: usize) -> Ptr<Def> {
    self.define(name, Def::Param { name, ty, is_mut, index })
  }

  fn define_local(&mut self, name: RefStr, is_mut: IsMut, ty: Ty) -> Ptr<Def> {
    self.define(name, Def::Local { name, ty, is_mut })
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

  fn infer_dot(&mut self, arg: &parse::Expr, name: RefStr) -> MRes<LValue> {
    // Infer argument type
    let arg = self.infer_lvalue(arg)?;

    // Find parameter list
    let params = match arg.ty() {
      Ty::Ref(_, ty_def) => match &**ty_def {
        TyDef::Struct(_, Some(params))  => params,
        TyDef::Union(_, Some(params))   => params,
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

    Ok(LValue::Dot {
      ty: param_ty.clone(),
      is_mut: arg.is_mut(),
      arg: Box::new(arg),
      name: name,
      idx: idx
    })
  }


  fn infer_index(&mut self, arg: &parse::Expr, idx: &parse::Expr) -> MRes<LValue> {
    // Infer array type
    let arg = self.infer_lvalue(arg)?;

    // Find element type
    let elem_ty = match arg.ty() {
      Ty::Arr(_, elem_ty) => &**elem_ty,
      _ => return Err(Box::new(TypeError {}))
    };

    // Check index type
    let mut idx = self.infer_rvalue(idx)?;
    unify(idx.ty_mut(), &mut Ty::Uintn)?;

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
      _ => return Err(Box::new(TypeError {}))
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
      let mut arg_val = self.infer_rvalue(arg_val)?;
      let mut param_ty = param_ty.clone();
      unify(arg_val.ty_mut(), &mut param_ty)?;
      nargs.push((*arg_name, arg_val));
    }

    Ok(RValue::Call { ty: ret_ty.clone(), arg: Box::new(arg), args: nargs })
  }

  fn infer_un(&mut self, op: UnOp, arg: &mut Ty) -> MRes<Ty> {
    // Check argument type
    Ok(match op {
      UnOp::UPlus | UnOp::UMinus => {
        unify(arg, &mut Ty::ClassNum)?;
        arg.clone()
      }
      UnOp::Not => {
        unify(arg, &mut Ty::ClassInt)?;
        arg.clone()
      }
    })
  }

  fn infer_bin(&mut self, op: BinOp, lhs: &mut Ty, rhs: &mut Ty) -> MRes<Ty> {
    // Check argument types and infer result type
    Ok(match op {
      // Both arguments must have matching numeric types
      // Result has the same type as the arguments
      BinOp::Mul | BinOp::Div | BinOp::Add | BinOp::Sub => {
        unify(lhs, &mut Ty::ClassNum)?;
        unify(lhs, rhs)?;
        lhs.clone()
      }

      // Both arguments must have matching integer types
      // Result has the same type as the arguments
      BinOp::Mod | BinOp::And | BinOp::Xor | BinOp::Or  => {
        unify(lhs, &mut Ty::ClassInt)?;
        unify(lhs, rhs)?;
        lhs.clone()
      }

      // Both arguments must have integer types
      // Result has the left argument's type
      BinOp::Lsh | BinOp::Rsh => {
        unify(lhs, &mut Ty::ClassInt)?;
        unify(rhs, &mut Ty::ClassInt)?;
        lhs.clone()
      }

      // Both arguments must have matching numeric types
      // Result is a boolean
      BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
        unify(lhs, &mut Ty::ClassNum)?;
        unify(lhs, rhs)?;
        Ty::Bool
      }
    })
  }

  fn infer_lvalue(&mut self, expr: &parse::Expr) -> MRes<LValue> {
    use parse::Expr::*;

    Ok(match expr {
      Path(path) => {
        let def = self.resolve_def(path[0])?;
        match &*def {
          Def::Data       { name, ty, is_mut, .. } |
          Def::ExternData { name, ty, is_mut, .. } |
          Def::Param      { name, ty, is_mut, .. } |
          Def::Local      { name, ty, is_mut, .. } => {
            LValue::DataRef {
              ty: ty.clone(),
              is_mut: *is_mut,
              name: *name,
              def: def
            }
          }
          _ => return Err(Box::new(TypeError {}))
        }
      }
      Str(val) => {
        let ty = Ty::Arr(val.borrow_rs().len(), Box::new(Ty::ClassInt));
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
      _ => return Err(Box::new(TypeError {}))
    })
  }

  fn infer_rvalue(&mut self, expr: &parse::Expr) -> MRes<RValue> {
    use parse::Expr::*;

    Ok(match expr {
      Null => {
        RValue::Null { ty: Ty::Tuple(vec![]) }
      }
      Path(path) => {
        let def = self.resolve_def(path[0])?;
        match &*def {
          Def::Const { name, ty, .. } => {
            RValue::ConstRef {
              ty: ty.clone(),
              name: *name,
              def: def
            }
          }
          Def::Func { name, ty, .. } |
          Def::ExternFunc { name, ty, .. } => {
            RValue::FuncRef {
              ty: ty.clone(),
              name: *name,
              def: def
            }
          }
          Def::Data       { name, ty, is_mut, .. } |
          Def::ExternData { name, ty, is_mut, .. } |
          Def::Param      { name, ty, is_mut, .. } |
          Def::Local      { name, ty, is_mut, .. } => {
            let data_ref = LValue::DataRef {
              ty: ty.clone(),
              is_mut: *is_mut,
              name: *name,
              def: def
            };

            RValue::Load {
              ty: ty.clone(),
              arg: Box::new(data_ref)
            }
          }
        }
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
        RValue::Int { ty: Ty::ClassInt, val: *val }
      }
      Flt(val) => {
        RValue::Flt { ty: Ty::ClassFlt, val: *val }
      }
      Char(val) => {
        RValue::Char { ty: Ty::ClassInt, val: *val }
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
        let mut arg = self.infer_rvalue(arg)?;
        RValue::Un {
          ty: self.infer_un(*op, arg.ty_mut())?,
          op: *op,
          arg: Box::new(arg)
        }
      }
      LNot(arg) => {
        let mut arg = self.infer_rvalue(arg)?;
        unify(arg.ty_mut(), &mut Ty::Bool)?;
        RValue::LNot { ty: Ty::Bool, arg: Box::new(arg) }
      }
      Cast(..) => {
        todo!()
      }
      Bin(op, lhs, rhs) => {
        let mut lhs = self.infer_rvalue(lhs)?;
        let mut rhs = self.infer_rvalue(rhs)?;
        let ty = self.infer_bin(*op, lhs.ty_mut(), rhs.ty_mut())?;
        RValue::Bin { ty, op: *op, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      LAnd(lhs, rhs) => {
        let mut lhs = self.infer_rvalue(lhs)?;
        let mut rhs = self.infer_rvalue(rhs)?;
        unify(lhs.ty_mut(), &mut Ty::Bool)?;
        unify(rhs.ty_mut(), &mut Ty::Bool)?;
        RValue::LAnd { ty: Ty::Bool, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      LOr(lhs, rhs) => {
        let mut lhs = self.infer_rvalue(lhs)?;
        let mut rhs = self.infer_rvalue(rhs)?;
        unify(lhs.ty_mut(), &mut Ty::Bool)?;
        unify(rhs.ty_mut(), &mut Ty::Bool)?;
        RValue::LOr { ty: Ty::Bool, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Block(parsed_body) => {
        self.enter();
        let mut body = vec![];
        for expr in parsed_body {
          body.push(self.infer_rvalue(expr)?);
        }
        let scope = self.exit();

        let ty = if let Some(last) = body.last_mut() {
          last.ty().clone()
        } else {
          Ty::Tuple(vec![])
        };

        RValue::Block { ty, scope, body }
      }
      As(lhs, rhs) => {
        // Infer argument types
        let mut lhs = self.infer_lvalue(lhs)?;
        let mut rhs = self.infer_rvalue(rhs)?;
        unify(lhs.ty_mut(), rhs.ty_mut())?;

        // Make sure lhs is mutable
        match lhs.is_mut() {
          IsMut::Yes => (),
          _ => return Err(Box::new(TypeError {})),
        };

        RValue::As { ty: Ty::Tuple(vec![]), lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Rmw(op, lhs, rhs) => {
        // Infer and check argument types
        let mut lhs = self.infer_lvalue(lhs)?;
        let mut rhs = self.infer_rvalue(rhs)?;
        self.infer_bin(*op, lhs.ty_mut(), rhs.ty_mut())?;

        // Make sure lhs is mutable
        match lhs.is_mut() {
          IsMut::Yes => (),
          _ => return Err(Box::new(TypeError {})),
        };

        RValue::Rmw { ty: Ty::Tuple(vec![]), op: *op, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Continue => {
        // Can only have continue inside a loop
        match self.loop_ty.last_mut() {
          Some(..) => (),
          None => return Err(Box::new(TypeError {})),
        };

        RValue::Continue { ty: Ty::ClassAny }
      }
      Break(arg) => {
        let mut arg = self.infer_rvalue(&*arg)?;

        // Can only have break inside a loop
        let loop_ty = match self.loop_ty.last_mut() {
          Some(loop_ty) => loop_ty,
          None => return Err(Box::new(TypeError {})),
        };

        // Unify function return type with the returned value's type
        unify(loop_ty, arg.ty_mut())?;

        RValue::Break { ty: Ty::ClassAny, arg: Box::new(arg) }
      }
      Return(arg) => {
        let mut arg = self.infer_rvalue(&*arg)?;

        // Can only have return inside a function
        let ret_ty = match self.ret_ty.last_mut() {
          Some(ret_ty) => ret_ty,
          None => return Err(Box::new(TypeError {})),
        };

        // Unify function return type with the returned value's type
        unify(ret_ty, arg.ty_mut())?;

        RValue::Return { ty: Ty::ClassAny, arg: Box::new(arg) }
      }
      Let(name, is_mut, ty, init) => {
        // Check initializer
        let mut init = self.infer_rvalue(init)?;

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
        RValue::Let { ty: Ty::Tuple(vec![]), def, init: Box::new(init) }
      }
      If(cond, tbody, ebody) => {
        let mut cond = self.infer_rvalue(cond)?;
        unify(cond.ty_mut(), &mut Ty::Bool)?;

        let mut tbody = self.infer_rvalue(tbody)?;
        let mut ebody = self.infer_rvalue(ebody)?;
        unify(tbody.ty_mut(), ebody.ty_mut())?;

        RValue::If {
          ty: tbody.ty().clone(),
          cond: Box::new(cond),
          tbody: Box::new(tbody),
          ebody: Box::new(ebody)
        }
      }
      While(cond, body) => {
        let cond = self.infer_rvalue(cond)?;
        self.loop_ty.push(Ty::Tuple(vec![]));
        let body = self.infer_rvalue(body)?;
        self.loop_ty.pop();

        RValue::While {
          ty: Ty::Tuple(vec![]),
          cond: Box::new(cond),
          body: Box::new(body)
        }
      }
      Loop(body) => {
        self.loop_ty.push(Ty::ClassAny);
        let body = self.infer_rvalue(body)?;
        RValue::Loop {
          ty: self.loop_ty.pop().unwrap(),
          body: Box::new(body)
        }
      }
    })
  }

  fn check_ty_defs(&mut self, defs: &Vec<parse::Def>) -> MRes<()>  {
    use parse::Def::*;

    let mut queue = vec![];

    // Pass 1: Create definitions
    for def in defs.iter() {
      match def {
        Struct { name, .. } =>  {
          queue.push((def, self.module.ty_def(TyDef::Struct(*name, None))));
        }
        Union { name, .. } => {

          queue.push((def, self.module.ty_def(TyDef::Union(*name, None))));
        }
        Enum { name, .. } => {
          queue.push((def, self.module.ty_def(TyDef::Enum(*name, None))));
        }
        _ => ()
      }
    }

    // Pass 2: Fill bodies
    for (def, mut ptr) in queue {
      match (def, &mut *ptr) {
        (Struct { params, .. }, TyDef::Struct(_, dest)) => {
          *dest = Some(self.check_params(params)?);
        }
        (Union { params, .. }, TyDef::Union(_, dest)) => {
          *dest = Some(self.check_params(params)?);
        }
        (Enum { variants, .. }, TyDef::Enum(_, dest)) => {
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
          *dest = Some(result);
        }
        _ => ()
      }
    }

    Ok(())
  }

  fn check_defs(&mut self, defs: &Vec<parse::Def>) -> MRes<()> {
    use parse::Def::*;

    let mut queue = vec![];

    // Pass 1: Create definitions
    for def in defs {
      match def {
        Const { name, ty, val } => {
          let mut ty = self.check_ty(ty)?;
          let mut val = self.infer_rvalue(val)?;
          unify(&mut ty, val.ty_mut())?;
          self.define(*name, Def::Const { name: *name, ty, val });
        }
        Data { name, is_mut, ty, .. } => {
          let ty = self.check_ty(ty)?;
          let ptr = self.define(*name,
            Def::Data { name: *name, ty, is_mut: *is_mut, init: None });
          queue.push((def, ptr));
        }
        Func { name, params, ret_ty, .. } => {
          let mut new_params = vec![];
          for (name, _, ty) in params {
            new_params.push((*name, self.check_ty(ty)?));
          }
          let ty = Ty::Func(new_params, Box::new(self.check_ty(ret_ty)?));
          let ptr = self.define(*name,
            Def::Func { name: *name, ty, params: None, body: None });
          queue.push((def, ptr));
        }
        ExternData { name, is_mut, ty } => {
          let ty = self.check_ty(ty)?;
          self.define(*name,
            Def::ExternData { name: *name, ty, is_mut: *is_mut });
        }
        ExternFunc { name, params, ret_ty } => {
          let ty = Ty::Func(self.check_params(params)?,
                          Box::new(self.check_ty(ret_ty)?));
          self.define(*name, Def::ExternFunc { name: *name, ty });
        }
        _ => ()
      }
    }

    // Pass 2: Fill bodies
    for (def, mut ptr) in queue {
      match (def, &mut *ptr) {
        (Data { init, .. }, Def::Data { ty, init: dest, .. }) => {
          // Check initializer type
          let mut init = self.infer_rvalue(init)?;
          unify(init.ty_mut(), ty)?;

          // Complete definition
          *dest = Some(init);
        }
        (Func { params, ret_ty, body, .. }, Def::Func { params: dparams, body: dbody, .. }) => {
          // FIXME: this could be made better by not re-checking ret_ty
          // and re-using the value from the first pass
          self.enter();

          // Create parameter symbols
          for (index, (name, is_mut, ty)) in params.iter().enumerate() {
            let ty = self.check_ty(ty)?;
            self.define_param(*name, *is_mut, ty, index);
          }

          // Typecheck body
          let mut body = self.infer_rvalue(body)?;
          let mut ret_ty = self.check_ty(ret_ty)?;
          unify(body.ty_mut(), &mut ret_ty)?;

          // Exit param scope
          *dparams = Some(self.exit());

          // Complete definition
          *dbody = Some(body);
        }
        _ => ()
      }
    }

    Ok(())
  }

  fn check_module(&mut self, module: &parse::Module) -> MRes<()> {
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
