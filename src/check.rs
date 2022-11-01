use crate::parse::{self,IsMut,UnOp,BinOp};
use crate::util::*;
use indexmap::IndexMap;
use std::collections::{HashMap};
use std::fmt::Write;
use std::{error,fmt};

/// Types

#[derive(Clone)]
pub enum Ty {
  // Real types
  Bool,
  Uint8,
  Int8,
  Uint16,
  Int16,
  Uint32,
  Int32,
  Uint64,
  Int64,
  Uintn,
  Intn,
  Float,
  Double,
  Ref(RefStr, TyDef),
  Fn(Vec<(RefStr, Ty)>, Box<Ty>),
  Ptr(IsMut, Box<Ty>),
  Arr(usize, Box<Ty>),
  Tuple(Vec<(RefStr, Ty)>),
  // Deduction
  ClassNum,
  ClassInt,
}

pub type TyDef = Ptr<TyDefS>;

pub enum TyDefS {
  Unresolved,
  Struct(RefStr, Vec<(RefStr, Ty)>),
  Union(RefStr, Vec<(RefStr, Ty)>),
  Enum(RefStr, Vec<(RefStr, Variant)>),
}

pub enum Variant {
  Unit(RefStr),
  Struct(RefStr, Vec<(RefStr, Ty)>),
}

fn write_comma_separated<I, T, W>(f: &mut fmt::Formatter<'_>, iter: I, wfn: W) -> fmt::Result
  where I: Iterator<Item=T>,
        W: Fn(&mut fmt::Formatter<'_>, &T) -> fmt::Result,
{
  write!(f, "(")?;
  let mut comma = false;
  for item in iter {
    if comma {
      write!(f, ", ")?;
    } else {
      comma = true;
    }
    wfn(f, &item)?;
  }
  write!(f, ")")
}

fn write_params(f: &mut fmt::Formatter<'_>, params: &Vec<(RefStr, Ty)>) -> fmt::Result {
  write_comma_separated(f, params.iter(), |f, (name, ty)| write!(f, "{}: {:?}", name, ty))
}

impl fmt::Debug for TyDefS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use TyDefS::*;
    match self {
      Struct(name, params) => {
        write!(f, "struct {} ", name)?;
        write_params(f, params)
      },
      Union(name, params) => {
        write!(f, "union {} ", name)?;
        write_params(f, params)
      },
      Enum(name, variants) => {
        write!(f, "enum {} ", name)?;
        write_comma_separated(f, variants.iter(), |f, (_, variant)| {
          match variant {
            Variant::Unit(name) => {
              write!(f, "{}", name)
            },
            Variant::Struct(name, params) => {
              write!(f, "{} ", name)?;
              write_params(f, params)
            },
          }
        })
      }
      _ => unreachable!(),
    }
  }
}

impl fmt::Debug for Ty {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use Ty::*;
    match self {
      Bool => write!(f, "Bool"),
      Uint8 => write!(f, "Uint8"),
      Int8 => write!(f, "Int8"),
      Uint16 => write!(f, "Uint16"),
      Int16 => write!(f, "Int16"),
      Uint32 => write!(f, "Uint32"),
      Int32 => write!(f, "Int32"),
      Uint64 => write!(f, "Uint64"),
      Int64 => write!(f, "Int64"),
      Uintn => write!(f, "Uintn"),
      Intn => write!(f, "Intn"),
      Float => write!(f, "Float"),
      Double => write!(f, "Double"),
      Ref(name, _) => write!(f, "{}", name),
      Fn(params, ty) => {
        write!(f, "Function")?;
        write_params(f, params)?;
        write!(f, " -> {:?}", ty)
      },
      Ptr(is_mut, ty) => write!(f, "*{} {:?}", is_mut, ty),
      Arr(cnt, ty) => write!(f, "[{}]{:?}", cnt, ty),
      Tuple(params) => write_params(f, params),
      ClassNum | ClassInt => unreachable!()
    }
  }
}

/// Expressions

pub struct Expr(Ty, ExprKind);

pub enum ExprKind {
  Ref(Def),
  Bool(bool),
  Int(usize),
  Char(RefStr),
  Str(RefStr),
  Dot(IsMut, Box<Expr>, RefStr),
  Call(Box<Expr>, Vec<(RefStr, Expr)>),
  Index(IsMut, Box<Expr>, Box<Expr>),
  Adr(Box<Expr>),
  Ind(IsMut, Box<Expr>),
  Un(UnOp, Box<Expr>),
  Cast(Box<Expr>, Ty),
  Bin(BinOp, Box<Expr>, Box<Expr>),
  Rmw(BinOp, Box<Expr>, Box<Expr>),
  As(Box<Expr>, Box<Expr>),
  Block(HashMap<RefStr, Own<DefS>>, Vec<Expr>),
  Continue,
  Break(Option<Box<Expr>>),
  Return(Option<Box<Expr>>),
  Let(Def, Box<Expr>),
  If(Box<Expr>, Box<Expr>, Box<Expr>),
  While(Box<Expr>, Box<Expr>),
  Loop(Box<Expr>),
}

impl fmt::Debug for Expr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use ExprKind::*;
    match &self.1 {
      Ref(def) => write!(f, "{}", def.name),
      Bool(val) => write!(f, "{}", val),
      Int(val) => write!(f, "{}", val),
      Char(val) => write!(f, "c{:?}", val),
      Str(val) => write!(f, "s{:?}", val),
      Dot(_, arg, name) => write!(f, ". {:?} {}", arg, name),
      Call(arg, args) => {
        write!(f, "{:?}", arg)?;
        write_comma_separated(f, args.iter(),
          |f, (name, arg)| write!(f, "{}: {:?}", name, arg))
      }
      Index(_, arg, idx) => write!(f, "{:?}[{:?}]", arg, idx),
      Adr(arg) => write!(f, "Adr {:?}", arg),
      Ind(_, arg) => write!(f, "Ind {:?}", arg),
      Un(op, arg) => write!(f, "{:?} {:?}", op, arg),
      Cast(arg, ty) => write!(f, "Cast {:?} {:?}", arg, ty),
      Bin(op, lhs, rhs) => write!(f, "{:?} {:?} {:?}", op, lhs, rhs),
      Rmw(op, lhs, rhs) => write!(f, "{:?}As {:?} {:?}", op, lhs, rhs),
      As(dst, src) => write!(f, "As {:?} {:?}", dst, src),
      Block(_, body) => {
        write!(f, "{{\n")?;
        let mut pf = PadAdapter::wrap(f);
        for expr in body {
          write!(&mut pf, "{:?};\n", expr)?;
        }
        write!(f, "}}")
      },
      Continue => write!(f, "continue"),
      Break(None) => write!(f, "break"),
      Break(Some(arg)) => write!(f, "break {:?}", arg),
      Return(None) => write!(f, "return"),
      Return(Some(arg)) => write!(f, "return {:?}", arg),
      Let(def, init) => write!(f, "let{} {}: {:?} = {:?}",
                                def.is_mut, def.name, def.ty, init),
      If(cond, tbody, ebody) => write!(f, "if {:?} {:?} {:?}",
                                        cond, tbody, ebody),
      While(cond, body) => write!(f, "while {:?} {:?}", cond, body),
      Loop(body) => write!(f, "loop {:?}", body),
    }
  }
}

/// Definitions

pub type Def = Ptr<DefS>;

pub struct DefS {
  name: RefStr,
  is_mut: IsMut,
  ty: Ty,
  kind: DefKind,
}

pub enum DefKind {
  Const(Expr),
  Fn,
  Data,
  Param(usize),
  Local,
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

pub struct CheckCtx {
  // Type definitions
  ty_defs: HashMap<RefStr, Own<TyDefS>>,
  // Definitions
  defs: Vec<HashMap<RefStr, Own<DefS>>>,
}

impl CheckCtx {
  pub fn new() -> Self {
    CheckCtx {
      ty_defs: HashMap::new(),
      defs: vec![ HashMap::new() ],
    }
  }

  //
  // Types
  //

  fn resolve_ty(&mut self, name: RefStr) -> MRes<Ty> {
    if let Some(ty_def) = self.ty_defs.get(&name) {
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

  pub fn check_ty_defs(&mut self, ty_defs: &IndexMap<RefStr, parse::TyDef>) -> MRes<()>  {
    use parse::TyDef::*;

    let mut queue = vec![];

    // Pass 1: Create objects
    for (name, ty_def) in ty_defs {
      let dummy = Own::new(TyDefS::Unresolved);
      queue.push((*name, ty_def, dummy.ptr()));
      self.ty_defs.insert(*name, dummy);
    }

    // Pass 2: Resolve names
    for (name, ty_def, mut dest) in queue {
      *dest = match ty_def {
        Struct { params } => TyDefS::Struct(name, self.check_params(params)?),
        Union { params } => TyDefS::Union(name, self.check_params(params)?),
        Enum { variants } => TyDefS::Enum(name, self.check_variants(variants)?),
      };
    }

    Ok(())
  }

  //
  // Definitions
  //

  fn enter(&mut self) {
    self.defs.push(HashMap::new());
  }

  fn exit(&mut self) -> HashMap<RefStr, Own<DefS>> {
    self.defs.pop().unwrap()
  }

  fn define_const(&mut self, name: RefStr, ty: Ty, val: Expr) {
    let def = Own::new(DefS { name, is_mut: IsMut::No, ty, kind: DefKind::Const(val) });
    self.defs.last_mut().unwrap().insert(name, def);
  }

  fn define_data(&mut self, name: RefStr, is_mut: IsMut, ty: Ty) {
    let def = Own::new(DefS { name, is_mut, ty, kind: DefKind::Data });
    self.defs.last_mut().unwrap().insert(name, def);
  }

  fn define_fn(&mut self, name: RefStr, ty: Ty) {
    let def = Own::new(DefS { name, is_mut: IsMut::No, ty, kind: DefKind::Fn });
    self.defs.last_mut().unwrap().insert(name, def);
  }

  fn define_param(&mut self, name: RefStr, is_mut: IsMut, ty: Ty, index: usize) {
    let def = Own::new(DefS { name, is_mut, ty, kind: DefKind::Param(index) });
    self.defs.last_mut().unwrap().insert(name, def);
  }

  fn define_local(&mut self, name: RefStr, is_mut: IsMut, ty: Ty) -> Def {
    let def = Own::new(DefS { name, is_mut, ty, kind: DefKind::Local });
    let ptr = def.ptr();
    self.defs.last_mut().unwrap().insert(name, def);
    ptr
  }

  fn resolve_def(&mut self, name: RefStr) -> MRes<Def> {
    for scope in self.defs.iter().rev() {
      if let Some(def) = scope.get(&name) {
        return Ok(def.ptr());
      }
    }
    Err(Box::new(UnresolvedIdentError { name }))
  }

  //
  // Expressions
  //

  fn unify(&mut self, ty1: Ty, ty2: Ty) -> MRes<Ty> {
    use Ty::*;
    match (ty1, ty2) {
      (ClassNum, ty2 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|Uintn|Intn|Float|Double)) |
      (ClassInt, ty2 @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|Uintn|Intn)) => Ok(ty2),
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
          npar.push((n1, self.unify(t1, t2)?));
        }
        Ok(Ty::Fn(npar, Box::new(self.unify(*ret1, *ret2)?)))
      }
      (Ptr(is_mut1, base1), Ptr(is_mut2, base2)) if is_mut1 == is_mut2 => {
        Ok(Ty::Ptr(is_mut1, Box::new(self.unify(*base1, *base2)?)))
      }
      (Arr(siz1, elem1), Arr(siz2, elem2)) if siz1 == siz2 => {
        Ok(Ty::Arr(siz1, Box::new(self.unify(*elem1, *elem2)?)))
      }
      (Tuple(par1), Tuple(par2)) if par1.len() == par2.len() => {
        let mut npar = vec![];
        for ((n1, t1), (n2, t2)) in par1.into_iter().zip(par2.into_iter()) {
          if n1 != n2 {
            return Err(Box::new(TypeError {}));
          }
          npar.push((n1, self.unify(t1, t2)?));
        }
        Ok(Ty::Tuple(npar))
      }
      _ => Err(Box::new(TypeError {}))
    }
  }

  fn infer_expr(&mut self, expr: &parse::Expr) -> MRes<Expr> {
    use parse::Expr::*;

    Ok(match expr {
      Path(path) => {
        let def = self.resolve_def(path[0])?;
        Expr(def.ty.clone(), ExprKind::Ref(def))
      }
      Bool(val) => {
        Expr(Ty::Bool, ExprKind::Bool(*val))
      }
      Int(val) => {
        Expr(Ty::ClassInt, ExprKind::Int(*val))
      }
      Char(val) => {
        Expr(Ty::ClassInt, ExprKind::Char(*val))
      }
      Str(val) => {
        let ty = Ty::Arr(val.borrow_rs().len(), Box::new(Ty::ClassInt));
        Expr(ty, ExprKind::Str(*val))
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
        Expr(Ty::Ptr(is_mut, Box::new(arg.0.clone())), ExprKind::Adr(Box::new(arg)))
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
        Expr(ty, ExprKind::Bin(*op, Box::new(lhs), Box::new(rhs)))
      }
      Rmw(op, lhs, rhs) => {
        // Infer and check argument types
        let (_, lhs, rhs) = self.infer_bin(*op, lhs, rhs)?;

        // Make sure lhs is mutable
        match self.ensure_lvalue(&lhs)? {
          IsMut::Yes => (),
          _ => return Err(Box::new(TypeError {})),
        };

        Expr(Ty::Tuple(vec![]), ExprKind::Rmw(*op, Box::new(lhs), Box::new(rhs)))
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
        let ty = self.unify(lhs.0, rhs.0)?;
        lhs.0 = ty.clone();
        rhs.0 = ty;

        Expr(Ty::Tuple(vec![]), ExprKind::As(Box::new(lhs), Box::new(rhs)))
      }
      Block(body) => {
        self.enter();
        let mut nbody = vec![];
        for expr in body {
          nbody.push(self.infer_expr(expr)?);
        }
        let scope = self.exit();

        let ty = if let Some(expr) = nbody.last() {
          expr.0.clone()
        } else {
          Ty::Tuple(vec![])
        };

        Expr(ty, ExprKind::Block(scope, nbody))
      }
      Continue => {
        Expr(Ty::Tuple(vec![]), ExprKind::Continue)
      }
      Break(arg) => {
        let arg = if let Some(arg) = arg {
          Some(Box::new(self.infer_expr(&*arg)?))
        } else {
          None
        };
        Expr(Ty::Tuple(vec![]), ExprKind::Break(arg))
      }
      Return(arg) => {
        let arg = if let Some(arg) = arg {
          Some(Box::new(self.infer_expr(&*arg)?))
        } else {
          None
        };
        Expr(Ty::Tuple(vec![]), ExprKind::Return(arg))
      }
      Let(name, is_mut, ty, init) => {
        // Check initializer
        let init = self.infer_expr(init)?;

        // Derive declared type
        let ty = if let Some(ty) = ty {
          let ty = self.check_ty(ty)?;
          self.unify(ty, init.0.clone())?
        } else {
          init.0.clone()
        };

        // Define symbol
        let def = self.define_local(*name, *is_mut, ty);

        // Add let expression
        Expr(Ty::Tuple(vec![]), ExprKind::Let(def, Box::new(init)))
      }
      If(cond, tbody, Some(ebody)) => {
        let cond = self.infer_expr(cond)?;
        let tbody = self.infer_expr(tbody)?;
        let ebody = self.infer_expr(ebody)?;
        Expr(self.unify(tbody.0.clone(), ebody.0.clone())?,
          ExprKind::If(Box::new(cond), Box::new(tbody), Box::new(ebody)))
      }
      If(cond, tbody, None) => {
        let cond = self.infer_expr(cond)?;
        let tbody = self.infer_expr(tbody)?;
        let ebody = Expr(Ty::Tuple(vec![]),
                          ExprKind::Block(HashMap::new(), vec![]));
        Expr(self.unify(tbody.0.clone(), ebody.0.clone())?,
          ExprKind::If(Box::new(cond), Box::new(tbody), Box::new(ebody)))
      }
      While(cond, body) => {
        let cond = self.infer_expr(cond)?;
        let body = self.infer_expr(body)?;
        Expr(Ty::Tuple(vec![]), ExprKind::While(Box::new(cond), Box::new(body)))
      }
      Loop(body) => {
        let body = self.infer_expr(body)?;
        Expr(Ty::Tuple(vec![]), ExprKind::Loop(Box::new(body)))
      }
    })
  }

  fn ensure_lvalue(&mut self, lval: &Expr) -> MRes<IsMut> {
    match &lval.1 {
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
    let params = match &arg.0 {
      Ty::Ref(_, ty_def) => match &**ty_def {
        TyDefS::Struct(_, params) | TyDefS::Union(_, params) => params,
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

    Ok(Expr(param_ty.clone(), ExprKind::Dot(is_mut, Box::new(arg), name)))
  }

  fn infer_call(&mut self, arg: &parse::Expr, args: &IndexMap<RefStr, parse::Expr>) -> MRes<Expr> {
    // Infer function type
    let arg = self.infer_expr(arg)?;

    // Find parameter list and return type
    let (params, ret_ty) = match &arg.0 {
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
      arg_val.0 = self.unify(arg_val.0, param_ty.clone())?;
      nargs.push((*arg_name, arg_val));
    }

    Ok(Expr(ret_ty.clone(), ExprKind::Call(Box::new(arg), nargs)))
  }

  fn infer_index(&mut self, arg: &parse::Expr, idx: &parse::Expr) -> MRes<Expr> {
    // Infer array type
    let arg = self.infer_expr(arg)?;
    // Infer mutablity
    let is_mut = self.ensure_lvalue(&arg)?;

    // Find element type
    let elem_ty = match &arg.0 {
      Ty::Arr(_, elem_ty) => &**elem_ty,
      _ => return Err(Box::new(TypeError {}))
    };

    // Check index type
    let mut idx = self.infer_expr(idx)?;
    idx.0 = self.unify(idx.0, Ty::Uintn)?;

    Ok(Expr(elem_ty.clone(), ExprKind::Index(is_mut, Box::new(arg), Box::new(idx))))
  }

  fn infer_ind(&mut self, arg: &parse::Expr) -> MRes<Expr> {
    // Infer pointer type
    let arg = self.infer_expr(arg)?;

    // Find base type
    let (is_mut, base_ty) = match &arg.0 {
      Ty::Ptr(is_mut, base_ty) => (*is_mut, &**base_ty),
      _ => return Err(Box::new(TypeError {}))
    };

    Ok(Expr(base_ty.clone(), ExprKind::Ind(is_mut, Box::new(arg))))
  }

  fn infer_un(&mut self, op: UnOp, arg: &parse::Expr) -> MRes<Expr> {
    // Infer argument type
    let mut arg = self.infer_expr(arg)?;

    // Check argument type
    match op {
      UnOp::UPlus | UnOp::UMinus => {
        arg.0 = self.unify(arg.0, Ty::ClassNum)?;
      }
      UnOp::Not => {
        arg.0 = self.unify(arg.0, Ty::ClassInt)?;
      }
      UnOp::LNot => {
        arg.0 = self.unify(arg.0, Ty::Bool)?;
      }
    }

    Ok(Expr(arg.0.clone(), ExprKind::Un(op, Box::new(arg))))
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
        let ty = self.unify(lhs.0, Ty::ClassNum)?;
        let ty = self.unify(ty, rhs.0)?;
        lhs.0 = ty.clone();
        rhs.0 = ty.clone();
        ty
      }

      // Both arguments must have matching integer types
      // Result has the same type as the arguments
      BinOp::Mod | BinOp::And | BinOp::Xor | BinOp::Or  => {
        let ty = self.unify(lhs.0, Ty::ClassInt)?;
        let ty = self.unify(ty, rhs.0)?;
        lhs.0 = ty.clone();
        rhs.0 = ty.clone();
        ty
      }

      // Both arguments must have integer types
      // Result has the left argument's type
      BinOp::Lsh | BinOp::Rsh => {
        lhs.0 = self.unify(lhs.0, Ty::ClassInt)?;
        rhs.0 = self.unify(rhs.0, Ty::ClassInt)?;
        lhs.0.clone()
      }

      // Both arguments must have matching numeric types
      // Result is a boolean
      BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
        let ty = self.unify(lhs.0, Ty::ClassNum)?;
        let ty = self.unify(ty, rhs.0)?;
        lhs.0 = ty.clone();
        rhs.0 = ty.clone();
        Ty::Bool
      }

      // Both argument must be booleans
      // Result is a boolean
      BinOp::LAnd | BinOp::LOr => {
        lhs.0 = self.unify(lhs.0, Ty::Bool)?;
        rhs.0 = self.unify(rhs.0, Ty::Bool)?;
        Ty::Bool
      }
    };

    Ok((ty, lhs, rhs))
  }

  pub fn check_module(&mut self, module: &parse::Module) -> MRes<()> {
    // Populate type definitions
    self.check_ty_defs(&module.ty_defs)?;

    // Create symbols for objects
    for (name, def) in &module.defs {
      match def {
        parse::Def::Const { ty, val } => {
          let ty = self.check_ty(ty)?;
          let val = self.infer_expr(val)?;
          self.define_const(*name, ty, val);
        }
        parse::Def::Data { is_mut, ty, .. } => {
          let ty = self.check_ty(ty)?;
          self.define_data(*name, *is_mut, ty);
        }
        parse::Def::Fn { params, ret_ty, .. } => {
          let mut new_params = vec![];
          for (name, (_, ty)) in params {
            new_params.push((*name, self.check_ty(ty)?));
          }
          let ty = Ty::Fn(new_params, Box::new(self.check_ty(ret_ty)?));
          self.define_fn(*name, ty);
        }
        parse::Def::Extern { is_mut, ty } => {
          let ty = self.check_ty(ty)?;
          self.define_data(*name, *is_mut, ty);
        }
        parse::Def::ExternFn { params, ret_ty } => {
          let ty = Ty::Fn(self.check_params(params)?,
                          Box::new(self.check_ty(ret_ty)?));
          self.define_fn(*name, ty);
        }
      };
    }

    // Type check object bodies
    for (name, def) in &module.defs {
      // Generate object bodies
      match def {
        parse::Def::Data { is_mut, init, .. } => {
          // Typecheck initializer
          let init = self.infer_expr(init)?;
          println!("data{} {} = {:#?}", is_mut, name, init);
        }
        parse::Def::Fn { params, ret_ty, body } => {
          print!("fn {}(", name);
          self.enter();
          // Create parameter symbols
          let mut first = true;
          for (index, (name, (is_mut, ty))) in params.iter().enumerate() {
            let ty = self.check_ty(ty)?;
            if first {
              print!("{}: {:?}", name, ty);
              first = false;
            } else {
              print!(", {}: {:?}", name, ty);
            }
            self.define_param(*name, *is_mut, ty, index);
          }
          print!(") -> {:?}", self.check_ty(ret_ty)?);
          // Typecheck body
          let body = self.infer_expr(body)?;
          println!(" {:#?}", body);
          self.exit();
        }
        _ => ()
      }
    }

    Ok(())
  }
}
