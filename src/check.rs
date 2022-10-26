use crate::parse::{self,BinOp};
use crate::util::*;
use indexmap::IndexMap;
use std::collections::{HashMap};
use std::fmt::Write;
use std::{error,fmt};

/// Types

pub type Ty = Ptr<TyS>;

pub enum TyS {
  Unresolved,

  Var(usize),

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
  Fn(Vec<(RefStr, Ty)>, Ty),
  Ptr(Ty),
  Arr(usize, Ty),
  Tuple(Vec<(RefStr, Ty)>),

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

fn write_variants(f: &mut fmt::Formatter<'_>, variants: &Vec<(RefStr, Variant)>) -> fmt::Result {
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

impl TyS {
    fn write_def(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use TyS::*;
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
        write_variants(f, variants)
      }
      _ => unreachable!(),
    }
  }

  fn write_ref(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use TyS::*;
    match self {
      Unresolved => unreachable!(),
      Var(idx) => write!(f, "'{}", idx),
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
      Fn(params, ty) => {
        write!(f, "Function")?;
        write_params(f, params)?;
        write!(f, " -> {:?}", ty)
      },
      Ptr(ty) => write!(f, "*{:?}", ty),
      Arr(cnt, ty) => write!(f, "[{}]{:?}", cnt, ty),
      Tuple(params) => write_params(f, params),
      Struct(name, _) |
      Union(name, _) |
      Enum(name, _) => {
        write!(f, "{}", name)
      }
    }
  }
}

impl fmt::Debug for TyS {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if f.alternate() {
      self.write_def(f)
    } else {
      self.write_ref(f)
    }
  }
}

/// Expressions

pub type Expr = Ptr<ExprS>;

pub struct ExprS {
  ty: Ty,
  kind: ExprKind,
}

pub enum ExprKind {
  Ref(Def),
  Bool(bool),
  Int(usize),
  Char(RefStr),
  Str(RefStr),
  Dot(Expr, RefStr),
  Call(Expr, Vec<(RefStr, Expr)>),
  Index(Expr, Expr),
  Adr(Expr),
  Ind(Expr),
  UMinus(Expr),
  Not(Expr),
  LNot(Expr),
  Cast(Expr, Ty),
  Bin(BinOp, Expr, Expr),
  Rmw(BinOp, Expr, Expr),
  As(Expr, Expr),
  Block(Vec<Expr>),
  Continue,
  Break(Option<Expr>),
  Return(Option<Expr>),
  Let(Def, Expr),
  If(Expr, Expr, Expr),
  While(Expr, Expr),
  Loop(Expr),
}

impl fmt::Debug for ExprS {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use ExprKind::*;
    match &self.kind {
      Ref(def) => write!(f, "{}", def.name),
      Bool(val) => write!(f, "{}", val),
      Int(val) => write!(f, "{}", val),
      Char(val) => write!(f, "c{:?}", val),
      Str(val) => write!(f, "s{:?}", val),
      Dot(arg, name) => write!(f, ". {:?} {}", arg, name),
      Call(arg, args) => {
        write!(f, "{:?}", arg)?;
        write_comma_separated(f, args.iter(),
          |f, (name, arg)| write!(f, "{}: {:?}", name, arg))
      }
      Index(arg, idx) => write!(f, "{:?}[{:?}]", arg, idx),
      Adr(arg) => write!(f, "Adr {:?}", arg),
      Ind(arg) => write!(f, "Ind {:?}", arg),
      UMinus(arg) => write!(f, "Neg {:?}", arg),
      Not(arg) => write!(f, "Not {:?}", arg),
      LNot(arg) => write!(f, "LNot {:?}", arg),
      Cast(arg, ty) => write!(f, "Cast {:?} {:?}", arg, ty),
      Bin(op, lhs, rhs) => write!(f, "{:?} {:?} {:?}", op, lhs, rhs),
      Rmw(op, lhs, rhs) => write!(f, "{:?}As {:?} {:?}", op, lhs, rhs),
      As(dst, src) => write!(f, "As {:?} {:?}", dst, src),
      Block(body) => {
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
      Let(def, init) => write!(f, "let {}: {:?} = {:?}", def.name, def.ty, init),
      If(cond, tbody, ebody) => write!(f, "if {:?} {:?} {:?}", cond, tbody, ebody),
      While(cond, body) => write!(f, "while {:?} {:?}", cond, body),
      Loop(body) => write!(f, "loop {:?}", body),
    }
  }
}

/// Definitions

pub type Def = Ptr<DefS>;

pub struct DefS {
  name: RefStr,
  is_mut: bool,
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
  // Allocator for IR structures
  arena: Arena,
  // Type variables
  tvars: Vec<Ty>,
  // Type definitions
  ty_defs: HashMap<RefStr, Ty>,
  // Definitions
  defs: Vec<HashMap<RefStr, Def>>,
  // Context :(
  return_ty: Ty,
  break_ty: Ty,
}

impl CheckCtx {
  pub fn new() -> Self {
    let mut arena = Arena::new();
    let unit = arena.alloc(TyS::Tuple(vec![]));
    CheckCtx {
      arena,
      tvars: Vec::new(),
      ty_defs: HashMap::new(),
      defs: vec![ HashMap::new() ],
      return_ty: unit,
      break_ty: unit,
    }
  }

  fn tvar(&mut self) -> Ty {
    let idx = self.tvars.len();
    let ty = self.alloc(TyS::Var(idx));
    self.tvars.push(ty);
    ty
  }

  fn alloc<T: 'static>(&mut self, val: T) -> Ptr<T> {
    self.arena.alloc(val)
  }

  //
  // Types
  //

  fn resolve_ty(&mut self, name: RefStr) -> MRes<Ty> {
    if let Some(ty) = self.ty_defs.get(&name) {
      Ok(*ty)
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
      Bool => self.alloc(TyS::Bool),
      Uint8 => self.alloc(TyS::Uint8),
      Int8 => self.alloc(TyS::Int8),
      Uint16 => self.alloc(TyS::Uint16),
      Int16 => self.alloc(TyS::Int16),
      Uint32 => self.alloc(TyS::Uint32),
      Int32 => self.alloc(TyS::Int32),
      Uint64 => self.alloc(TyS::Uint64),
      Int64 => self.alloc(TyS::Int64),
      Uintn => self.alloc(TyS::Uintn),
      Intn => self.alloc(TyS::Intn),
      Float => self.alloc(TyS::Float),
      Double => self.alloc(TyS::Double),
      Path(path) => {
        self.resolve_ty(path[0])?
      },
      Fn(params, ret_ty) => {
        let ty = TyS::Fn(self.check_params(params)?,
                              self.check_ty(ret_ty)?);
        self.alloc(ty)
      },
      Ptr(base_ty) => {
        let ty = TyS::Ptr(self.check_ty(base_ty)?);
        self.alloc(ty)
      },
      Arr(_, elem_ty) => {
        // FIXME: evaluate elem_cnt constant expression
        let ty = TyS::Arr(0, self.check_ty(elem_ty)?);
        self.alloc(ty)
      },
      Tuple(params) => {
        let ty = TyS::Tuple(self.check_params(params)?);
        self.alloc(ty)
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
      let dummy = self.arena.alloc(TyS::Unresolved);
      self.ty_defs.insert(*name, dummy.ptr());
      queue.push((*name, ty_def, dummy));
    }

    // Pass 2: Resolve names
    for (name, ty_def, mut dest) in queue {
      *dest = match ty_def {
        Struct { params } => TyS::Struct(name, self.check_params(params)?),
        Union { params } => TyS::Union(name, self.check_params(params)?),
        Enum { variants } => TyS::Enum(name, self.check_variants(variants)?),
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

  fn exit(&mut self) {
    self.defs.pop().expect("Cannot exit global scope");
  }

  fn define_const(&mut self, name: RefStr, ty: Ty, val: Expr) -> Def {
    let def = self.alloc(DefS {
      name, is_mut: false, ty, kind: DefKind::Const(val)
    });
    self.defs.last_mut().unwrap().insert(name, def);
    def
  }

  fn define_data(&mut self, name: RefStr, is_mut: bool, ty: Ty) -> Def {
    let def = self.alloc(DefS {
      name, is_mut, ty, kind: DefKind::Data
    });
    self.defs.last_mut().unwrap().insert(name, def);
    def
  }

  fn define_fn(&mut self, name: RefStr, ty: Ty) -> Def {
    let def = self.alloc(DefS {
      name, is_mut: false, ty, kind: DefKind::Fn
    });
    self.defs.last_mut().unwrap().insert(name, def);
    def
  }

  fn define_param(&mut self, name: RefStr, is_mut: bool, ty: Ty, index: usize) -> Def {
    let def = self.alloc(DefS {
      name, is_mut, ty, kind: DefKind::Param(index)
    });
    self.defs.last_mut().unwrap().insert(name, def);
    def
  }

  fn define_local(&mut self, name: RefStr, is_mut: bool, ty: Ty) -> Def {
    let def = self.alloc(DefS {
      name, is_mut, ty, kind: DefKind::Local
    });
    self.defs.last_mut().unwrap().insert(name, def);
    def
  }

  fn resolve_def(&mut self, name: RefStr) -> MRes<Def> {
    for scope in self.defs.iter().rev() {
      if let Some(def) = scope.get(&name) {
        return Ok(*def);
      }
    }
    Err(Box::new(UnresolvedIdentError { name }))
  }

  //
  // Type checking
  //

  fn check_same(&mut self, ty1: Ty, ty2: Ty) -> MRes<Ty> {
    use TyS::*;
    match (&*ty1, &*ty2) {
      (Bool, Bool) => Ok(ty1),
      (Uint8, Uint8) => Ok(ty1),
      (Int8, Int8) => Ok(ty1),
      (Uint16, Uint16) => Ok(ty1),
      (Int16, Int16) => Ok(ty1),
      (Uint32, Uint32) => Ok(ty1),
      (Int32, Int32) => Ok(ty1),
      (Uint64, Uint64) => Ok(ty1),
      (Int64, Int64) => Ok(ty1),
      (Uintn, Uintn) => Ok(ty1),
      (Intn, Intn) => Ok(ty1),
      (Float, Float) => Ok(ty1),
      (Double, Double) => Ok(ty1),
      (Fn(par1, ret1), Fn(par2, ret2)) if par1.len() == par2.len() => {
        for ((n1, t1), (n2, t2)) in par1.iter().zip(par2.iter()) {
          if n1 != n2 {
            return Err(Box::new(TypeError {}));
          }
          self.check_same(*t1, *t2)?;
        }
        self.check_same(*ret1, *ret2)?;
        Ok(ty1)
      }
      (Ptr(base1), Ptr(base2)) => {
        self.check_same(*base1, *base2)?;
        Ok(ty1)
      }
      (Arr(siz1, elem1), Arr(siz2, elem2)) if siz1 == siz2 => {
        self.check_same(*elem1, *elem2)?;
        Ok(ty1)
      }
      (Tuple(par1), Tuple(par2)) if par1.len() == par2.len() => {
        for ((n1, t1), (n2, t2)) in par1.iter().zip(par2.iter()) {
          if n1 != n2 {
            return Err(Box::new(TypeError {}));
          }
          self.check_same(*t1, *t2)?;
        }
        Ok(ty1)
      }
      // FIXME: struct/union/enum
      _ => Err(Box::new(TypeError {}))
    }
  }

  fn check_bool(&mut self, ty: Ty) -> MRes<Ty> {
    use TyS::*;
    match &*ty {
      Bool => Ok(ty),
      _ => Err(Box::new(TypeError {}))
    }
  }

  fn check_int(&mut self, ty: Ty) -> MRes<Ty> {
    use TyS::*;
    match &*ty {
      Uint8 | Int8 | Uint16 | Int16 |
      Uint32 | Int32 | Uint64 | Int64 |
      Uintn | Intn => Ok(ty),
      _ => Err(Box::new(TypeError {}))
    }
  }

  fn check_num(&self, ty: Ty) -> MRes<Ty> {
    use TyS::*;
    match &*ty {
      Uint8 | Int8 | Uint16 | Int16 |
      Uint32 | Int32 | Uint64 | Int64 |
      Uintn | Intn | Float | Double => Ok(ty),
      _ => Err(Box::new(TypeError {}))
    }
  }

  fn check_binop(&mut self, op: BinOp, ty1: Ty, ty2: Ty) -> MRes<Ty> {
    use BinOp::*;
    match op {
      Mul | Div | Add | Sub => {
        self.check_num(ty1)?;
        self.check_same(ty1, ty2)
      }
      Mod | And | Xor | Or => {
        self.check_int(ty1)?;
        self.check_same(ty1, ty2)
      }
      Lsh | Rsh => {
        self.check_int(ty2)?;
        self.check_int(ty1)
      }
      Eq | Ne | Lt | Gt | Le | Ge => {
        self.check_num(ty1)?;
        self.check_same(ty1, ty2)?;
        Ok(self.alloc(TyS::Bool))
      }
      LAnd | LOr => {
        self.check_bool(ty1)?;
        self.check_bool(ty2)
      }
    }
  }

  //
  // Expressions
  //

  fn check_expr(&mut self, expr: &parse::Expr) -> MRes<Expr> {
    use parse::Expr::*;

    Ok(match expr {
      Path(path) => {
        let def = self.resolve_def(path[0])?;
        self.alloc(ExprS {
          ty: def.ty,
          kind: ExprKind::Ref(def),
        })
      }
      Bool(val) => {
        let ty = self.alloc(TyS::Bool);
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Bool(*val),
        })
      }
      Int(val) => {
        let ty = self.tvar();
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Int(*val),
        })
      }
      Char(val) => {
        let ty = self.tvar();
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Char(*val),
        })
      }
      Str(val) => {
        let ty = self.tvar();
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Str(*val),
        })
      }
      Dot(arg, name) => {
        let arg = self.check_expr(arg)?;
        let ty = match &*arg.ty {
          TyS::Tuple(params) |
          TyS::Struct(_, params) |
          TyS::Union(_, params) => {
            if let Some(pty) = lin_search(params, name) {
              *pty
            } else {
              panic!("No field {} of type {:?}", name, arg.ty)
            }
          }
          ty => panic!(". applied to non-aggregate type {:?}", ty)
        };
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Dot(arg, *name),
        })
      }
      Call(arg, args) => {
        let arg = self.check_expr(arg)?;
        let (params, ty) = match &*arg.ty {
          TyS::Fn(params, ret_ty) => (params, *ret_ty),
          ty => panic!("Type {:?} is not callable", ty)
        };
        // FIXME: type check arguments
        let mut nargs = vec![];
        for (name, arg) in args {
          nargs.push((*name, self.check_expr(arg)?));
        }
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Call(arg, nargs),
        })
      }
      Index(arg, idx) => {
        let arg = self.check_expr(arg)?;
        let ty = match &*arg.ty {
          TyS::Arr(_, ty) => *ty,
          ty => panic!("Type {:?} not indexable", ty),
        };
        let idx = self.check_expr(idx)?;
        self.check_int(idx.ty)?;
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Index(arg, idx),
        })
      }
      Adr(arg) => {
        let arg = self.check_expr(arg)?;
        let ty = self.alloc(TyS::Ptr(arg.ty));
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Adr(arg),
        })
      }
      Ind(arg) => {
        let arg = self.check_expr(arg)?;
        let ty = match &*arg.ty {
          TyS::Ptr(ty) => *ty,
          ty => panic!("Type {:?} cannot be dereferenced", ty),
        };
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Ind(arg),
        })
      }
      UPlus(arg) => {
        let arg = self.check_expr(arg)?;
        self.check_num(arg.ty)?;
        arg
      }
      UMinus(arg) => {
        let arg = self.check_expr(arg)?;
        let ty = self.check_num(arg.ty)?;
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::UMinus(arg),
        })
      }
      Not(arg) => {
        let arg = self.check_expr(arg)?;
        let ty = self.check_int(arg.ty)?;
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Not(arg),
        })
      }
      LNot(arg) => {
        let arg = self.check_expr(arg)?;
        let ty = self.check_bool(arg.ty)?;
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::LNot(arg),
        })
      }
      Cast(_, _) => {
        todo!()
      }
      Bin(op, lhs, rhs) => {
        let lhs = self.check_expr(lhs)?;
        let rhs = self.check_expr(rhs)?;
        let ty = self.check_binop(*op, lhs.ty, rhs.ty)?;
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Bin(*op, lhs, rhs),
        })
      }
      Rmw(op, lhs, rhs) => {
        let lhs = self.check_expr(lhs)?;
        let rhs = self.check_expr(rhs)?;
        let ty = self.check_binop(*op, lhs.ty, rhs.ty)?;
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Rmw(*op, lhs, rhs),
        })
      }
      As(lhs, rhs) => {
        let lhs = self.check_expr(lhs)?;
        let rhs = self.check_expr(rhs)?;
        let ty = self.check_same(lhs.ty, rhs.ty)?;
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::As(lhs, rhs),
        })
      }
      Block(body) => {
        self.enter();
        let mut nbody = vec![];
        for expr in body {
          nbody.push(self.check_expr(expr)?);
        }
        self.exit();
        let ty = if let Some(expr) = nbody.last() {
          expr.ty
        } else {
          self.alloc(TyS::Tuple(vec![]))
        };
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Block(nbody),
        })
      }
      Continue => {
        let ty = self.alloc(TyS::Tuple(vec![]));
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Continue,
        })
      }
      Break(arg) => {
        let ty = self.alloc(TyS::Tuple(vec![]));
        let arg = if let Some(expr) = arg {
          let expr = self.check_expr(&*expr)?;
          self.break_ty = expr.ty;
          Some(expr)
        } else {
          None
        };
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Break(arg),
        })
      }
      Return(arg) => {
        let ty = self.alloc(TyS::Tuple(vec![]));
        let arg = if let Some(expr) = arg {
          let expr = self.check_expr(&*expr)?;
          self.return_ty = expr.ty;
          Some(expr)
        } else {
          None
        };
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Return(arg),
        })
      }
      Let(name, is_mut, ty, init) => {
        // Check initializer
        let init = self.check_expr(init)?;

        // Check type
        let ty = if let Some(ty) = ty {
          let ty = self.check_ty(ty)?;
          self.check_same(ty, init.ty)?
        } else {
          init.ty
        };

        // Define symbol
        let def = self.define_local(*name, *is_mut, ty);

        let ty = self.alloc(TyS::Tuple(vec![]));
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Let(def, init),
        })
      }
      If(cond, tbody, Some(ebody)) => {
        let cond = self.check_expr(cond)?;
        let tbody = self.check_expr(tbody)?;
        let ebody = self.check_expr(ebody)?;
        let ty = self.check_same(tbody.ty, ebody.ty)?;
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::If(cond, tbody, ebody),
        })
      }
      If(cond, tbody, None) => {
        let cond = self.check_expr(cond)?;
        let tbody = self.check_expr(tbody)?;
        let ty = self.alloc(TyS::Tuple(vec![]));
        let ebody = self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Block(vec![]),
        });
        let ty = self.check_same(tbody.ty, ebody.ty)?;
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::If(cond, tbody, ebody),
        })
      }
      While(cond, body) => {
        let cond = self.check_expr(cond)?;
        let body = self.check_expr(body)?;
        let ty = self.alloc(TyS::Tuple(vec![]));
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::While(cond, body),
        })
      }
      Loop(body) => {
        let prev = self.break_ty;
        let body = self.check_expr(body)?;
        let expr = self.alloc(ExprS {
          ty: self.break_ty,
          kind: ExprKind::Loop(body)
        });
        self.break_ty = prev;
        expr
      }
    })
  }

  pub fn check_module(&mut self, module: &parse::Module) -> MRes<()> {
    // Populate type definitions
    self.check_ty_defs(&module.ty_defs)?;

    // Create symbols for objects
    for (name, def) in &module.defs {
      match def {
        parse::Def::Const { ty, val } => {
          let ty = self.check_ty(ty)?;
          let val = self.check_expr(val)?;
          self.define_const(*name, ty, val);
        }
        parse::Def::Data { is_mut, ty, .. } => {
          let ty = self.check_ty(ty)?;
          self.define_data(*name, *is_mut, ty);
        }
        parse::Def::Fn { params, ret_ty, .. } => {
          let mut ty_params = vec![];
          for (name, (_, ty)) in params {
            let ty = self.check_ty(ty)?;
            ty_params.push((*name, ty));
          }
          let ret_ty = self.check_ty(ret_ty)?;
          let ty = self.alloc(TyS::Fn(ty_params, ret_ty));
          self.define_fn(*name, ty);
        }
        parse::Def::Extern { is_mut, ty } => {
          let ty = self.check_ty(ty)?;
          self.define_data(*name, *is_mut, ty);
        }
        parse::Def::ExternFn { params, ret_ty } => {
          let tys = TyS::Fn(self.check_params(params)?,
                              self.check_ty(ret_ty)?);
          let ty = self.alloc(tys);
          self.define_fn(*name, ty);
        }
      };
    }

    // Type check object bodies
    for (name, def) in &module.defs {
      // Generate object bodies
      match def {
        parse::Def::Data { init, .. } => {
          // Typecheck initializer
          let init = self.check_expr(init)?;
          println!("{:#?}", init);
        }
        parse::Def::Fn { params, ret_ty, body } => {
          self.enter();
          // Create parameter symbols
          for (index, (name, (is_mut, ty))) in params.iter().enumerate() {
            let ty = self.check_ty(ty)?;
            self.define_param(*name, *is_mut, ty, index);
          }
          // Typecheck body
          let body = self.check_expr(body)?;
          println!("{:#?}", body);
          self.exit();
        }
        _ => ()
      }
    }

    Ok(())
  }
}
