use crate::parse::{self,BinOp};
use crate::util::*;
use indexmap::{indexmap,IndexMap};
use std::collections::{HashMap};
use std::fmt::Write;
use std::{error,fmt};

/// Types

pub type Ty = Ptr<TyS>;

pub enum Variant {
  Unit(RefStr),
  Struct(RefStr, IndexMap<RefStr, Ty>),
}

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
  Fn(IndexMap<RefStr, Ty>, Ty),
  Ptr(Ty),
  Arr(usize, Ty),
  Tuple(IndexMap<RefStr, Ty>),

  Struct(RefStr, IndexMap<RefStr, Ty>),
  Union(RefStr, IndexMap<RefStr, Ty>),
  Enum(RefStr, IndexMap<RefStr, Variant>),
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

fn write_params(f: &mut fmt::Formatter<'_>, params: &IndexMap<RefStr, Ty>) -> fmt::Result {
  write_comma_separated(f, params.iter(), |f, (name, ty)| write!(f, "{}: {:?}", name, ty))
}

fn write_variants(f: &mut fmt::Formatter<'_>, variants: &IndexMap<RefStr, Variant>) -> fmt::Result {
  write_comma_separated(f, variants.iter(), |f, (name, variant)| {
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

  fn is_same(ty1: Ty, ty2: Ty) -> bool {
    true
  }

  fn is_bool(&self) -> bool {
    let v = self;
    matches!(TyS::Bool, v)
  }

  fn is_int(&self) -> bool {
    use TyS::*;
    match self {
      Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn => true,
      _ => false,
    }
  }
  fn is_num(&self) -> bool {
    use TyS::*;
    match self {
      Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn | Float | Double => true,
      _ => false,
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
  Call(Expr, IndexMap<RefStr, Expr>),
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
  If(Expr, Expr, Option<Expr>),
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
      If(cond, tbody, None) => write!(f, "if {:?} {:?}", cond, tbody),
      If(cond, tbody, Some(ebody)) => write!(f, "if {:?} {:?} {:?}", cond, tbody, ebody),
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
    let unit = arena.alloc(TyS::Tuple(indexmap!{})).ptr();
    CheckCtx {
      arena,
      ty_defs: HashMap::new(),
      defs: vec![ HashMap::new() ],
      return_ty: unit,
      break_ty: unit,
    }
  }

  fn alloc<T: 'static>(&mut self, val: T) -> Ptr<T> {
    self.arena.alloc(val).ptr()
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

  fn check_params(&mut self, params: &IndexMap<RefStr, parse::TyRef>) -> MRes<IndexMap<RefStr, Ty>> {
    let mut result = indexmap!{};
    for (name, ty) in params {
      result.insert(*name, self.check_ty(ty)?);
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

  fn check_variants(&mut self, variants: &IndexMap<RefStr, parse::Variant>) -> MRes<IndexMap<RefStr, Variant>> {
    use parse::Variant::*;

    let mut result = indexmap!{};

    for (name, variant) in variants {
      result.insert(*name, match variant {
        Unit => Variant::Unit(*name),
        Struct(params) => Variant::Struct(*name, self.check_params(params)?),
      });
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

  fn define_local(&mut self, name: RefStr, is_mut: bool, ty: Ty) -> Def {
    let def = self.alloc(DefS {
      name, is_mut: false, ty, kind: DefKind::Local
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
  // Expressions
  //

  fn check_expr(&mut self, expr: &parse::Expr) -> MRes<Expr> {
    use parse::Expr::*;

    fn check_bin(op: BinOp, lhs: Ty, rhs: Ty) -> Option<Ty> {
      use BinOp::*;
      match op {
        // Argument types must match and be numeric
        Mul | Div | Add | Sub | Eq | Ne | Lt | Gt | Le | Ge => {
          if TyS::is_same(lhs, rhs) && lhs.is_num() {
            Some(lhs)
          } else {
            None
          }
        }
        // Arguments types must match and be integer
        Mod | And | Xor | Or => {
          if TyS::is_same(lhs, rhs) && lhs.is_int() {
            Some(lhs)
          } else {
            None
          }
        }
        // Argument types must be integers
        Lsh | Rsh => {
          if lhs.is_int() && rhs.is_int() {
            Some(lhs)
          } else {
            None
          }
        }
        // Argument types must be boolean
        LAnd | LOr => {
          if lhs.is_bool() && rhs.is_bool() {
            Some(lhs)
          } else {
            None
          }
        }
      }
    }

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
        let ty = self.alloc(TyS::Intn);
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Int(*val),
        })
      }
      Char(val) => {
        let ty = self.alloc(TyS::Intn);
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Char(*val),
        })
      }
      Str(val) => {
        let ty = self.alloc(TyS::Intn);
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
            if let Some(pty) = params.get(name) {
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
        let mut nargs = indexmap!{};
        // FIXME: type check arguments
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
        if !idx.ty.is_int() {
          panic!("Type {:?} cannot be used as an index", idx.ty);
        }
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
        if !arg.ty.is_num() {
          panic!("Unary + applied to non-numeric type {:?}", arg.ty);
        }
        arg
      }
      UMinus(arg) => {
        let arg = self.check_expr(arg)?;
        if !arg.ty.is_num() {
          panic!("Unary + applied to non-numeric type {:?}", arg.ty);
        }
        self.alloc(ExprS {
          ty: arg.ty,
          kind: ExprKind::UMinus(arg),
        })
      }
      Not(arg) => {
        let arg = self.check_expr(arg)?;
        if !arg.ty.is_int() {
          panic!("Bitwise inverse of non-integer type {:?}", arg.ty);
        }
        self.alloc(ExprS {
          ty: arg.ty,
          kind: ExprKind::Not(arg),
        })
      }
      LNot(arg) => {
        let arg = self.check_expr(arg)?;
        if !arg.ty.is_bool() {
          panic!("Logical inverse of non-boolean type {:?}", arg.ty);
        }
        self.alloc(ExprS {
          ty: arg.ty,
          kind: ExprKind::LNot(arg),
        })
      }
      Cast(_, _) => {
        todo!()
      }
      Bin(op, lhs, rhs) => {
        let lhs = self.check_expr(lhs)?;
        let rhs = self.check_expr(rhs)?;
        let ty = if let Some(ty) = check_bin(*op, lhs.ty, rhs.ty) {
          ty
        } else {
          panic!("Invalid arguments {:?} and {:?} for {:?}", lhs.ty, rhs.ty, op);
        };
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Bin(*op, lhs, rhs),
        })
      }
      Rmw(op, lhs, rhs) => {
        let lhs = self.check_expr(lhs)?;
        let rhs = self.check_expr(rhs)?;
        let ty = if let Some(ty) = check_bin(*op, lhs.ty, rhs.ty) {
          ty
        } else {
          panic!("Invalid arguments {:?} and {:?} for {:?}", lhs.ty, rhs.ty, op);
        };
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Rmw(*op, lhs, rhs),
        })
      }
      As(lhs, rhs) => {
        let lhs = self.check_expr(lhs)?;
        let rhs = self.check_expr(rhs)?;
        if !TyS::is_same(lhs.ty, rhs.ty) {
          panic!("Cannot assign {:?} to {:?}", rhs.ty, lhs.ty)
        }
        self.alloc(ExprS {
          ty: lhs.ty,
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
          self.alloc(TyS::Tuple(indexmap!{}))
        };
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Block(nbody),
        })
      }
      Continue => {
        let ty = self.alloc(TyS::Tuple(indexmap!{}));
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Continue,
        })
      }
      Break(arg) => {
        let ty = self.alloc(TyS::Tuple(indexmap!{}));
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
        let ty = self.alloc(TyS::Tuple(indexmap!{}));
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
          self.check_ty(ty)?
        } else {
          init.ty
        };

        // Define symbol
        let def = self.define_local(*name, *is_mut, ty);

        let ty = self.alloc(TyS::Tuple(indexmap!{}));
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Let(def, init),
        })
      }
      If(cond, tbody, ebody) => {
        let cond = self.check_expr(cond)?;
        let tbody = self.check_expr(tbody)?;
        let (ebody, ty) = if let Some(ebody) = ebody {
          (Some(self.check_expr(ebody)?), tbody.ty)
        } else {
          (None, self.alloc(TyS::Tuple(indexmap!{})))
        };

        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::If(cond, tbody, ebody),
        })
      }
      While(cond, body) => {
        let cond = self.check_expr(cond)?;
        let body = self.check_expr(body)?;
        let ty = self.alloc(TyS::Tuple(indexmap!{}));
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

/*
    let mut fn_queue = vec![];
    let mut data_queue = vec![];
*/

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
        parse::Def::Fn { params, ret_ty, body } => {
          let mut ty_params = indexmap!{};
          for (name, (is_mut, ty)) in params {
            let ty = self.check_ty(ty)?;
            ty_params.insert(*name, ty);
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

/*
    // Pass 3: type check object bodies

    for (mut obj, def) in todo_objects.into_iter() {
      // Save these to not upset the borrow checker
      let name = obj.name;
      let ty = obj.ty;

      // Generate object bodies
      match (&mut obj.kind, def) {
        (ObjKind::Fn, Fn { params, body, .. }) => {
          self.enter();
          // Add parameters to scope
          for (idx, (name, (is_mut, ty))) in params.iter().enumerate() {
            let ty = self.check_ty(ty)?;
            // Allocate symbol
            let obj = self.alloc(ObjS {
              name: *name,
              is_mut: *is_mut,
              ty: ty,
              kind: ObjKind::Local(stor),
            });
            self.define(*name, Def::Obj(obj));
          }
          // Type check body
          let body = self.check_expr(body)?;
          self.exit();
        }
        (ObjKind::Data { .. }, Data { init, .. }) => {
          let expr = self.check_expr(init)?;
        }
        _ => unreachable!(),
      };
    }*/

    Ok(())
  }
}
