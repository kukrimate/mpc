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

/// Type inferencer

struct TVarCtx {
  // Bounds for each type variables
  tvars: Vec<TyBound>
}

impl TVarCtx {
  fn new() -> Self {
    Self {
      tvars: vec![],
    }
  }

  fn clear(&mut self) {
    self.tvars.clear()
  }

  fn tvar(&mut self, bound: TyBound) -> Ty {
    let ty = Ty::TVar(self.tvars.len());
    self.tvars.push(bound);
    ty
  }

  fn unify_tys(&mut self, ty1: &Ty, ty2: &Ty) -> MRes<Ty> {
    use Ty::*;
    match (ty1, ty2) {
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
        Ok(ty1.clone())
      }
      (Ref(name1, def1), Ref(name2, def2)) if def1 == def2 => {
        assert_eq!(name1, name2);
        Ok(ty1.clone())
      }
      (Func(par1, ret1), Func(par2, ret2)) if par1.len() == par2.len() => {
        let mut par = Vec::new();
        for ((n1, t1), (n2, t2)) in par1.iter().zip(par2.iter()) {
          if n1 != n2 {
            return Err(Box::new(TypeError {}));
          }
          par.push((*n1, self.unify_tys(t1, t2)?));
        }
        Ok(Ty::Func(par, Box::new(self.unify_tys(ret1, ret2)?)))
      }
      (Ptr(is_mut1, base1), Ptr(is_mut2, base2)) if is_mut1 == is_mut2 => {
        Ok(Ty::Ptr(*is_mut1, Box::new(self.unify_tys(base1, base2)?)))
      }
      (Arr(siz1, elem1), Arr(siz2, elem2)) if siz1 == siz2 => {
        Ok(Ty::Arr(*siz1, Box::new(self.unify_tys(elem1, elem2)?)))
      }
      (Tuple(par1), Tuple(par2)) if par1.len() == par2.len() => {
        let mut par = Vec::new();
        for ((n1, t1), (n2, t2)) in par1.iter().zip(par2.iter()) {
          if n1 != n2 {
            return Err(Box::new(TypeError {}));
          }
          par.push((*n1, self.unify_tys(t1, t2)?));
        }
        Ok(Ty::Tuple(par))
      }
      (var @ TVar(idx), ty) | (ty, var @ TVar(idx)) => {
        self.bound_var(*idx, &TyBound::Is(ty.clone()))?;
        Ok(var.clone())
      }
      (ty1, ty2) => {
        Err(Box::new(CannotUnifyError(ty1.clone(), ty2.clone())))
      }
    }
  }

  fn bound_var(&mut self, mut idx: usize, new: &TyBound) -> MRes<()> {
    // Skip to the end of the chain
    while let TyBound::Is(Ty::TVar(next)) = &self.tvars[idx] {
      idx = *next;
    }

    // Unify new and previous bounds
    let unified = match (self.tvars[idx].clone(), new) {
      (prev, TyBound::Is(ty)) => {
        TyBound::Is(self.bound_ty(&prev, &ty)?)
      }
      (TyBound::Int, TyBound::Any|TyBound::Num|TyBound::Int) => {
        TyBound::Int
      }
      (TyBound::Flt, TyBound::Any|TyBound::Num|TyBound::Flt) => {
        TyBound::Flt
      }
      (TyBound::Num, TyBound::Any|TyBound::Num) => {
        TyBound::Num
      }
      (TyBound::Any, new @ (TyBound::Any|TyBound::Num|
                            TyBound::Int|TyBound::Flt)) => {
        new.clone()
      }
      // Unification cannot be done
      _ => return Err(Box::new(TypeError {}))
    };

    // Update variable bound if it doesn't create a cycle
    match unified {
      TyBound::Is(Ty::TVar(nidx)) if idx == nidx => (),
      _ => self.tvars[idx] = unified,
    }

    Ok(())
  }

  fn bound_ty(&mut self, bound: &TyBound, ty: &Ty) -> MRes<Ty> {
    use Ty::*;
    match (bound, ty) {
      // Add bound to type variable
      (bound, TVar(idx)) => {
        self.bound_var(*idx, bound)?;
        Ok(ty.clone())
      }
      // Any type
      (TyBound::Any, _) |
      // Integer or floating point types
      (TyBound::Num, Uint8|Int8|Uint16|Int16|Uint32|Int32|
                      Uint64|Int64|Uintn|Intn|Float|Double) |
      // Integer types
      (TyBound::Int, Uint8|Int8|Uint16|Int16|Uint32|Int32|
                      Uint64|Int64|Uintn|Intn) |
      // Floating point types
      (TyBound::Flt, Float|Double) => Ok(ty.clone()),
      // Type doesn't satisfy bound
      _ => return Err(Box::new(TypeError {}))
    }
  }


  /// Pre LLVM pass to clean up type variable references in the IR

  fn fixup_ty(&mut self, ty: &mut Ty) {
    use Ty::*;
    match ty {
      Bool|Uint8|Int8|Uint16|Int16|Uint32|
      Int32|Uint64|Int64|Uintn|Intn|Float|Double => (),
      Ref(..) => (),
      Ptr(_, ty) => {
        self.fixup_ty(ty);
      },
      Func(params, ty) => {
        for (_, ty) in params {
          self.fixup_ty(ty);
        }
        self.fixup_ty(ty);
      },
      Arr(_, ty) => {
        self.fixup_ty(ty);
      },
      Tuple(params) => {
        for (_, ty) in params {
          self.fixup_ty(ty);
        }
      }
      TVar(mut idx) => {
        // Skip to end of chain
        while let TyBound::Is(Ty::TVar(next)) = &self.tvars[idx] {
          idx = *next;
        }
        // Convert bound to type
        *ty = match self.tvars[idx].clone() {
          TyBound::Is(mut ty) => {
            self.fixup_ty(&mut ty);
            ty
          }
          // Any type fitting the bound is valid here
          TyBound::Any => Ty::Tuple(vec![]),
          TyBound::Num |
          TyBound::Int => Ty::Int32,
          TyBound::Flt => Ty::Float,
        };
      }
    }
  }

  fn fixup_lvalue(&mut self, lvalue: &mut LValue) {
    match lvalue {
      LValue::DataRef { ty, .. } |
      LValue::Str { ty, .. } => {
        self.fixup_ty(ty);
      }
      LValue::Dot { ty, arg, .. } => {
        self.fixup_ty(ty);
        self.fixup_lvalue(arg);
      }
      LValue::Index { ty, arg, idx, .. } => {
        self.fixup_ty(ty);
        self.fixup_lvalue(arg);
        self.fixup_rvalue(idx);
      }
      LValue::Ind { ty, arg, .. } => {
        self.fixup_ty(ty);
        self.fixup_rvalue(arg);
      }
    }
  }

  fn fixup_rvalue(&mut self, rvalue: &mut RValue) {
    match rvalue {
      RValue::Null { ty } |
      RValue::Bool { ty, .. } |
      RValue::Int { ty, .. } |
      RValue::Flt { ty, .. } |
      RValue::Char { ty, .. } |
      RValue::ConstRef { ty, .. } |
      RValue::FuncRef { ty, .. } |
      RValue::Continue { ty } => {
        self.fixup_ty(ty);
      }
      RValue::Load { ty, arg } |
      RValue::Adr { ty, arg } => {
        self.fixup_ty(ty);
        self.fixup_lvalue(arg);
      }
      RValue::Call { ty, arg, args } => {
        self.fixup_ty(ty);
        self.fixup_rvalue(arg);
        for (_, arg) in args.iter_mut() {
          self.fixup_rvalue(arg);
        }
      }
      RValue::Un { ty, arg, .. } |
      RValue::Break { ty, arg } |
      RValue::Return { ty, arg } |
      RValue::LNot { ty, arg } |
      RValue::Cast { ty, arg } => {
        self.fixup_ty(ty);
        self.fixup_rvalue(arg);
      }
      RValue::Bin { ty, lhs, rhs, .. } |
      RValue::LAnd { ty, lhs, rhs } |
      RValue::LOr  { ty, lhs, rhs } => {
        self.fixup_ty(ty);
        self.fixup_rvalue(lhs);
        self.fixup_rvalue(rhs);
      }
      RValue::As { ty, lhs, rhs } |
      RValue::Rmw { ty, lhs, rhs, .. } => {
        self.fixup_ty(ty);
        self.fixup_lvalue(lhs);
        self.fixup_rvalue(rhs);
      }
      RValue::Block { ty, body, .. } => {
        self.fixup_ty(ty);
        for expr in body.iter_mut() {
          self.fixup_rvalue(expr);
        }
      }
      RValue::Let { ty, def, init, .. } => {
        self.fixup_ty(ty);
        if let Def::Local { ty, .. } = &mut **def {
          self.fixup_ty(ty);
        } else {
          unreachable!()
        }
        self.fixup_rvalue(init);
      }
      RValue::If { ty, cond, tbody, ebody } => {
        self.fixup_ty(ty);
        self.fixup_rvalue(cond);
        self.fixup_rvalue(tbody);
        self.fixup_rvalue(ebody);
      }
      RValue::While { ty, cond, body } => {
        self.fixup_ty(ty);
        self.fixup_rvalue(cond);
        self.fixup_rvalue(body);
      }
      RValue::Loop { ty, body } => {
        self.fixup_ty(ty);
        self.fixup_rvalue(body);
      }
    }
  }
}

/// Type checker logic

struct CheckCtx {
  // Module being currenly checked
  module: Module,
  // Symbol table
  scopes: Vec<HashMap<RefStr, Ptr<Def>>>,
  // Type variable context
  tctx: TVarCtx,
  // Contexts for break/continue, and return
  loop_ty: Vec<Ty>,
  ret_ty: Vec<Ty>
}

impl CheckCtx {
  fn new() -> Self {
    Self {
      module: Module::new(),
      scopes: vec![ HashMap::new() ],
      tctx: TVarCtx::new(),
      loop_ty: vec![],
      ret_ty: vec![]
    }
  }

  /// Symbol table

  fn enter(&mut self) {
    self.scopes.push(HashMap::new());
  }

  fn exit(&mut self) {
    self.scopes.pop().unwrap();
  }

  fn define(&mut self, name: RefStr, def: Ptr<Def>) {
    self.scopes.last_mut().unwrap().insert(name, def);
  }

  fn resolve_def(&mut self, name: RefStr) -> MRes<Ptr<Def>> {
    for scope in self.scopes.iter().rev() {
      if let Some(def) = scope.get(&name) {
        return Ok(*def);
      }
    }
    Err(Box::new(UnresolvedIdentError { name }))
  }

  /// Create global definition

  fn global_def(&mut self, name: RefStr, def: Def) -> Ptr<Def> {
    let own = Own::new(def);
    let ptr = own.ptr();
    self.module.defs.push(own);
    self.define(name, ptr);
    ptr
  }

  //
  // Types
  //

  fn resolve_ty(&mut self, name: RefStr) -> MRes<Ty> {
    let def = self.resolve_def(name)?;
    match &*def {
      Def::Struct {..} |
      Def::Union {..} |
      Def::Enum {..} => {
        Ok(Ty::Ref(name, def))
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

  //
  // Expressions
  //


  fn infer_dot(&mut self, arg: &parse::Expr, name: RefStr) -> MRes<LValue> {
    // Infer argument type
    let arg = self.infer_lvalue(arg)?;

    // Find parameter list
    let params = match arg.ty() {
      Ty::Ref(_, def) => match &**def {
        Def::Struct { params: Some(params), .. } => params,
        Def::Union { params: Some(params), .. } => params,
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
    let idx = self.infer_rvalue(idx)?;
    self.tctx.unify_tys(&Ty::Uintn, idx.ty())?;

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
      let arg_val = self.infer_rvalue(arg_val)?;
      self.tctx.unify_tys(arg_val.ty(), param_ty)?;
      nargs.push((*arg_name, arg_val));
    }

    Ok(RValue::Call { ty: ret_ty.clone(), arg: Box::new(arg), args: nargs })
  }

  fn infer_un(&mut self, op: UnOp, arg: &Ty) -> MRes<Ty> {
    // Check argument type
    match op {
      UnOp::UPlus | UnOp::UMinus => {
        self.tctx.bound_ty(&TyBound::Num, arg)
      }
      UnOp::Not => {
        self.tctx.bound_ty(&TyBound::Int, arg)
      }
    }
  }

  fn infer_bin(&mut self, op: BinOp, lhs: &Ty, rhs: &Ty) -> MRes<Ty> {
    // Check argument types and infer result type
    match op {
      // Both arguments must have matching numeric types
      // Result has the same type as the arguments
      BinOp::Mul | BinOp::Div | BinOp::Add | BinOp::Sub => {
        self.tctx.bound_ty(&TyBound::Num, lhs)?;
        self.tctx.unify_tys(lhs, rhs)
      }

      // Both arguments must have matching integer types
      // Result has the same type as the arguments
      BinOp::Mod | BinOp::And | BinOp::Xor | BinOp::Or  => {
        self.tctx.bound_ty(&TyBound::Int, lhs)?;
        self.tctx.unify_tys(lhs, rhs)
      }

      // Both arguments must have integer types
      // Result has the left argument's type
      BinOp::Lsh | BinOp::Rsh => {
        self.tctx.bound_ty(&TyBound::Int, rhs)?;
        self.tctx.bound_ty(&TyBound::Int, lhs)
      }

      // Both arguments must have matching numeric types
      // Result is a boolean
      BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
        self.tctx.bound_ty(&TyBound::Num, lhs)?;
        self.tctx.unify_tys(lhs, rhs)?;
        Ok(Ty::Bool)
      }
    }
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
        let ty = Ty::Arr(val.borrow_rs().len(),
                          Box::new(self.tctx.tvar(TyBound::Int)));
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
          _ => return Err(Box::new(TypeError {}))
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
        RValue::Int { ty: self.tctx.tvar(TyBound::Int), val: *val }
      }
      Flt(val) => {
        RValue::Flt { ty: self.tctx.tvar(TyBound::Flt), val: *val }
      }
      Char(val) => {
        RValue::Char { ty: self.tctx.tvar(TyBound::Int), val: *val }
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
        self.tctx.unify_tys(&Ty::Bool, arg.ty())?;
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
        self.tctx.unify_tys(&Ty::Bool, lhs.ty())?;
        self.tctx.unify_tys(&Ty::Bool, rhs.ty())?;
        RValue::LAnd { ty: Ty::Bool, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      LOr(lhs, rhs) => {
        let lhs = self.infer_rvalue(lhs)?;
        let rhs = self.infer_rvalue(rhs)?;
        self.tctx.unify_tys(&Ty::Bool, lhs.ty())?;
        self.tctx.unify_tys(&Ty::Bool, rhs.ty())?;
        RValue::LOr { ty: Ty::Bool, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Block(parsed_body) => {
        self.enter();
        let mut body = vec![];
        for expr in parsed_body {
          body.push(self.infer_rvalue(expr)?);
        }
        self.exit();

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
        self.tctx.unify_tys(lhs.ty(), rhs.ty())?;

        // Make sure lhs is mutable
        match lhs.is_mut() {
          IsMut::Yes => (),
          _ => return Err(Box::new(TypeError {})),
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
          _ => return Err(Box::new(TypeError {})),
        };

        RValue::Rmw { ty: Ty::Tuple(vec![]), op: *op, lhs: Box::new(lhs), rhs: Box::new(rhs) }
      }
      Continue => {
        // Can only have continue inside a loop
        match self.loop_ty.last() {
          Some(..) => (),
          None => return Err(Box::new(TypeError {})),
        };

        RValue::Continue { ty: self.tctx.tvar(TyBound::Any) }
      }
      Break(arg) => {
        let arg = self.infer_rvalue(&*arg)?;

        // Can only have break inside a loop
        let loop_ty = match self.loop_ty.last() {
          Some(loop_ty) => loop_ty.clone(),
          None => return Err(Box::new(TypeError {})),
        };

        // Unify function return type with the returned value's type
        self.tctx.unify_tys(&loop_ty, arg.ty())?;

        RValue::Break { ty: self.tctx.tvar(TyBound::Any), arg: Box::new(arg) }
      }
      Return(arg) => {
        let arg = self.infer_rvalue(&*arg)?;

        // Can only have return inside a function
        let ret_ty = match self.ret_ty.last() {
          Some(ret_ty) => ret_ty.clone(),
          None => return Err(Box::new(TypeError {})),
        };

        // Unify function return type with the returned value's type
        self.tctx.unify_tys(&ret_ty, arg.ty())?;

        RValue::Return { ty: self.tctx.tvar(TyBound::Any), arg: Box::new(arg) }
      }
      Let(name, is_mut, ty, init) => {
        // Check initializer
        let init = self.infer_rvalue(init)?;

        // Unify type annotation with initializer type
        let ty = if let Some(ty) = ty {
          let ty = self.check_ty(ty)?;
          self.tctx.unify_tys(&ty, init.ty())?;
          ty
        } else {
          init.ty().clone()
        };

        // Create definition
        let def = Own::new(Def::Local { name: *name, is_mut: *is_mut, ty });
        // Add to symbol table
        self.define(*name, def.ptr());

        // Add let expression
        RValue::Let { ty: Ty::Tuple(vec![]), def, init: Box::new(init) }
      }
      If(cond, tbody, ebody) => {
        let cond = self.infer_rvalue(cond)?;
        self.tctx.unify_tys(&Ty::Bool, cond.ty())?;

        let tbody = self.infer_rvalue(tbody)?;
        let ebody = self.infer_rvalue(ebody)?;
        self.tctx.unify_tys(tbody.ty(), ebody.ty())?;

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
        let ty = self.tctx.tvar(TyBound::Any);
        self.loop_ty.push(ty);
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
          queue.push((def,
            self.global_def(*name, Def::Struct { name: *name, params: None })));
        }
        Union { name, .. } => {
          queue.push((def,
            self.global_def(*name, Def::Union { name: *name, params: None })));
        }
        Enum { name, .. } => {
          queue.push((def,
            self.global_def(*name, Def::Enum { name: *name, variants: None })));
        }
        _ => ()
      }
    }

    // Pass 2: Fill bodies
    for (def, mut ptr) in queue {
      match (def, &mut *ptr) {
        (Struct { params, .. }, Def::Struct { params: dest, .. }) => {
          *dest = Some(self.check_params(params)?);
        }
        (Union { params, .. }, Def::Union { params: dest, .. }) => {
          *dest = Some(self.check_params(params)?);
        }
        (Enum { variants, .. }, Def::Enum { variants: dest, .. }) => {
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
          self.tctx.clear();
          let ty = self.check_ty(ty)?;
          let mut val = self.infer_rvalue(val)?;
          self.tctx.unify_tys(&ty, val.ty())?;
          self.tctx.fixup_rvalue(&mut val);
          self.global_def(*name, Def::Const { name: *name, ty, val });
        }
        Data { name, is_mut, ty, .. } => {
          let ty = self.check_ty(ty)?;
          let ptr = self.global_def(*name,
            Def::Data { name: *name, ty, is_mut: *is_mut, init: None });
          queue.push((def, ptr));
        }
        Func { name, params, ret_ty, .. } => {
          let mut param_tys = vec![];
          let mut param_defs = vec![];

          for (index, (name, is_mut, ty)) in params.iter().enumerate() {
            let ty = self.check_ty(ty)?;
            param_tys.push((*name, ty.clone()));
            param_defs.push(Own::new(
              Def::Param { name: *name, is_mut: *is_mut, ty, index }));
          }

          let ty = Ty::Func(param_tys, Box::new(self.check_ty(ret_ty)?));
          let ptr = self.global_def(*name,
            Def::Func { name: *name, ty, params: param_defs, body: None });
          queue.push((def, ptr));
        }
        ExternData { name, is_mut, ty } => {
          let ty = self.check_ty(ty)?;
          self.global_def(*name,
            Def::ExternData { name: *name, ty, is_mut: *is_mut });
        }
        ExternFunc { name, params, ret_ty } => {
          let ty = Ty::Func(self.check_params(params)?,
                          Box::new(self.check_ty(ret_ty)?));
          self.global_def(*name, Def::ExternFunc { name: *name, ty });
        }
        _ => ()
      }
    }

    // Pass 2: Fill bodies
    for (def, mut ptr) in queue {
      match (def, &mut *ptr) {
        (Data { init, .. }, Def::Data { ty, init: dest, .. }) => {
          // Check initializer type
          self.tctx.clear();
          let mut init = self.infer_rvalue(init)?;
          self.tctx.unify_tys(ty, init.ty())?;
          self.tctx.fixup_rvalue(&mut init);

          // Complete definition
          *dest = Some(init);
        }
        (Func { ret_ty, body, .. }, Def::Func { params, body: dest, .. }) => {
          // Create parameter scope
          self.enter();
          for def in params {
            if let Def::Param { name, .. } = &**def {
              self.define(*name, def.ptr());
            } else {
              unreachable!()
            }
          }

          // Typecheck body
          self.tctx.clear();
          let ret_ty = self.check_ty(ret_ty)?;
          let mut body = self.infer_rvalue(body)?;
          self.tctx.unify_tys(&ret_ty, body.ty())?;
          self.tctx.fixup_rvalue(&mut body);

          // Exit paraemeter scope
          self.exit();

          // Complete definition
          *dest = Some(body);
        }
        _ => ()
      }
    }

    Ok(())
  }

  fn check_module(&mut self, module: &parse::Module) -> MRes<()> {
    self.check_ty_defs(&module.defs)?;
    self.check_defs(&module.defs)?;
    println!("{:?}", self.tctx.tvars);
    Ok(())
  }
}

pub fn check_module(parsed_module: &parse::Module) -> MRes<Module> {
  let mut ctx = CheckCtx::new();
  ctx.check_module(parsed_module)?;
  Ok(ctx.module)
}
