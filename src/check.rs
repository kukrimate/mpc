use crate::parse::{self,BinOp};
use crate::util::*;
use indexmap::{indexmap,IndexMap};
use std::collections::{HashMap};
use std::{error,fmt};

/// Types

pub type Ty = Ptr<TyS>;

#[derive(Debug)]
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
  Unit(RefStr),
  Tuple(IndexMap<RefStr, Ty>),

  Struct(IndexMap<RefStr, Ty>),
  Union(IndexMap<RefStr, Ty>),
  Enum(IndexMap<RefStr, Ty>),
}

impl TyS {
  fn is_same(ty1: Ty, ty2: Ty) -> bool { true }
  fn is_bool(&self) -> bool { let v = self; matches!(TyS::Bool, v) }
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

/// Definitions

pub type Obj = Ptr<ObjS>;

#[derive(Debug)]
pub struct ObjS {
  name: RefStr,
  ty: Ty,
  kind: ObjKind,
}

#[derive(Debug)]
pub enum ObjKind {
  // Function, const, and data with bodies
  Fn {
    params: IndexMap<RefStr, Obj>,
    body: Option<Expr>
  },
  Const {
    val: Option<Expr>
  },
  Data {
    is_mut: bool,
    init: Option<Expr>
  },

  // Function parameters and locals
  Param {
    is_mut: bool
  },
  Local {
    is_mut: bool,
    init: Expr,
  },

  // External stuff has no bodies
  Extern { is_mut: bool },
  ExternFn,
}

#[derive(Debug)]
pub enum Def {
  Ty(Ty),
  Obj(Obj),
}

/// Expressions

pub type Expr = Ptr<ExprS>;

pub struct ExprS {
  ty: Ty,
  kind: ExprKind,
}

pub enum ExprKind {
  Obj(Obj),
  Bool(bool),
  Int(usize),
  Char(RefStr),
  Str(RefStr),
  Dot(Expr, RefStr),
  Call(Expr, IndexMap<RefStr, Expr>),
  Index(Expr, Expr),
  Ref(Expr),
  Deref(Expr),
  UMinus(Expr),
  Not(Expr),
  LNot(Expr),
  Cast(Expr, Ty),
  Bin(BinOp, Expr, Expr),
  As(Expr, Expr),
  Block(Vec<Expr>),
  Continue,
  Break(Option<Expr>),
  Return(Option<Expr>),
  Let(RefStr, bool, Option<Ty>, Expr),
  If(Expr, Expr, Option<Expr>),
  While(Expr, Expr),
  Loop(Expr),
  Nop,
}

impl std::fmt::Debug for ExprS {
  fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    use ExprKind::*;
    match &self.kind {
      Obj(obj) => write!(fmt, "{}", obj.name),
      Bool(val) => write!(fmt, "{}", val),
      Int(val) => write!(fmt, "{}", val),
      Char(val) => write!(fmt, "c{:?}", val),
      Str(val) => write!(fmt, "s{:?}", val),
      Dot(arg, name) => write!(fmt, ". {:?} {}", arg, name),
      Call(arg, args) => {
        write!(fmt, "() {:?}", arg)?;
        for arg in args {
          write!(fmt, " {:?}", arg)?;
        }
        Ok(())
      }
      Index(arg, idx) => todo!(),
      Ref(arg) => todo!(),
      Deref(arg) => todo!(),
      UMinus(arg) => todo!(),
      Not(arg) => todo!(),
      LNot(arg) => todo!(),
      Cast(arg, ty) => todo!(),
      Bin(op, lhs, rhs) => todo!(),
      As(dst, src) => todo!(),
      Block(body) => todo!(),
      Continue => todo!(),
      Break(arg) => todo!(),
      Return(arg) => todo!(),
      Let(name, is_mut, ty, init) => todo!(),
      If(cond, tbody, ebody) => todo!(),
      While(cond, body) => todo!(),
      Loop(body) => todo!(),
      Nop => todo!(),
    }
  }
}

/// Errors

#[derive(Debug)]
struct UnknownTypeError {
  name: RefStr
}

impl fmt::Display for UnknownTypeError {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    write!(fmt, "Unknown typename {}", self.name)
  }
}

impl error::Error for UnknownTypeError {}

#[derive(Debug)]
struct UnknownObjectError {
  name: RefStr
}

impl fmt::Display for UnknownObjectError {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    write!(fmt, "Unknown object {}", self.name)
  }
}

impl error::Error for UnknownObjectError {}

/// Type checker logic

struct Ctx<'ctx> {
  // Module being analyzed
  module: &'ctx parse::Module,
  // Allocator for IR structures
  arena: Arena,
  // Symbol table
  symtab: Vec<HashMap<RefStr, Def>>,
  // Type variable table
  tvars: Vec<Ty>,

  // Context :(
  return_ty: Ty,
  break_ty: Ty,
}

impl<'ctx> Ctx<'ctx> {
  fn new(module: &'ctx parse::Module) -> Self {
    let mut arena = Arena::new();
    let unit = arena.alloc(TyS::Tuple(indexmap!{})).ptr();

    Ctx {
      module,
      arena,
      symtab: vec![ HashMap::new() ],
      tvars: vec![],
      return_ty: unit,
      break_ty: unit,
    }
  }

  fn alloc<T: 'static>(&mut self, val: T) -> Ptr<T> {
    self.arena.alloc(val).ptr()
  }

  fn enter(&mut self) {
    self.symtab.push(HashMap::new());
  }

  fn exit(&mut self) {
    assert!(self.symtab.len() > 0);
    self.symtab.pop();
  }

  fn define(&mut self, name: RefStr, def: Def) {
    self.symtab.last_mut().unwrap().insert(name, def);
  }

  fn resolve_ty(&mut self, name: RefStr) -> MRes<Ty> {
    for scope in self.symtab.iter().rev() {
      if let Some(Def::Ty(ty)) = scope.get(&name) {
        return Ok(*ty);
      }
    }
    Err(Box::new(UnknownTypeError { name }))
  }

  fn resolve_obj(&mut self, name: RefStr) -> MRes<Obj> {
    for scope in self.symtab.iter().rev() {
      if let Some(Def::Obj(obj)) = scope.get(&name) {
        return Ok(*obj);
      }
    }
    Err(Box::new(UnknownObjectError { name }))
  }

  fn newtvar(&mut self) -> Ty {
    let ty = self.alloc(TyS::Var(self.tvars.len()));
    self.tvars.push(ty);
    ty
  }

  fn check_params(&mut self, params: &IndexMap<RefStr, parse::Ty>) -> MRes<IndexMap<RefStr, Ty>> {
    let mut nparams = indexmap!{};
    for (name, ty) in params {
      nparams.insert(*name, self.check_ty(ty)?);
    }
    Ok(nparams)
  }

  fn check_variants(&mut self, variants: &IndexMap<RefStr, parse::Variant>) -> MRes<IndexMap<RefStr, Ty>> {
    let mut nparams = indexmap!{};
    for (name, variant) in variants {
      use parse::Variant::*;
      match variant {
        Unit => {
          nparams.insert(*name, self.alloc(TyS::Unit(*name)));
        }
        Struct(params) => {
          let sparams = self.check_params(params)?;
          nparams.insert(*name, self.alloc(TyS::Struct(sparams)));
        }
      }
    }
    Ok(nparams)
  }

  fn check_ty(&mut self, ty: &parse::Ty) -> MRes<Ty> {
    use parse::Ty::*;
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
      Path(path) => self.resolve_ty(path[0])?,
      Fn(params, ret_ty) => {
        let ty = TyS::Fn(self.check_params(params)?,
                              self.check_ty(ret_ty)?);
        self.alloc(ty)
      },
      Ptr(base_ty) => {
        let ty = TyS::Ptr(self.check_ty(base_ty)?);
        self.alloc(ty)
      },
      Arr(elem_cnt, elem_ty) => {
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
        let obj = self.resolve_obj(path[0])?;
        self.alloc(ExprS {
          ty: obj.ty,
          kind: ExprKind::Obj(obj),
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
        let ty = self.newtvar();
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Int(*val),
        })
      }
      Char(val) => {
        let ty = self.newtvar();
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Char(*val),
        })
      }
      Str(val) => {
        let ty = self.newtvar();
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Str(*val),
        })
      }
      Dot(arg, name) => {
        let arg = self.check_expr(arg)?;
        let ty = match &*arg.ty {
          TyS::Tuple(params) |
          TyS::Struct(params) |
          TyS::Union(params) => {
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
      Ref(arg) => {
        let arg = self.check_expr(arg)?;
        let ty = self.alloc(TyS::Ptr(arg.ty));
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Ref(arg),
        })
      }
      Deref(arg) => {
        let arg = self.check_expr(arg)?;
        let ty = match &*arg.ty {
          TyS::Ptr(ty) => *ty,
          ty => panic!("Type {:?} cannot be dereferenced", ty),
        };
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Ref(arg),
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
      Cast(arg, ty) => {
        todo!()
      }
      Bin(op, lhs, rhs) | Rmw(op, lhs, rhs) => {
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
        let mut nbody = vec![];
        for expr in body {
          nbody.push(self.check_expr(expr)?);
        }
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
        let init = self.check_expr(init)?;
        let ty = if let Some(ty) = ty {
          // FIXME: make sure this is the same type as the type of init
          self.check_ty(ty)?
        } else {
          init.ty
        };
        let obj = self.alloc(ObjS {
          name: *name,
          ty: ty,
          kind: ObjKind::Local { is_mut: *is_mut, init: init }
        });
        self.define(*name, Def::Obj(obj));

        // FIXME: maybe make these block elements not expressions
        // this is so ugly :(
        let ty = self.alloc(TyS::Tuple(indexmap!{}));
        self.alloc(ExprS {
          ty: ty,
          kind: ExprKind::Nop,
        })
      }
      If(cond, tbody, ebody) => {
        todo!()
      }
      While(cond, body) => {
        todo!()
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

  fn check_root(&mut self) -> MRes<()> {
    use parse::Def::*;

    // Pass 1: create symbols
    let mut todo_types = vec![];
    let mut todo_objects = vec![];

    for (name, def) in &self.module.defs {
      let def = match def {
        Struct { .. } | Union { .. } | Enum { .. } => {
          let ty = self.arena.alloc(TyS::Unresolved);
          todo_types.push((ty, def));
          Def::Ty(ty.ptr())
        }
        Fn { params, ret_ty, body } => {
          // Create function type
          let mut ty_params = indexmap!{};
          let mut obj_params = indexmap!{};
          for (name, (is_mut, ty)) in params {
            let ty = self.check_ty(ty)?;
            ty_params.insert(*name, ty);
            // Create symbol for parameters
            obj_params.insert(*name, self.alloc(ObjS {
              name: *name,
              ty: ty,
              kind: ObjKind::Param { is_mut: *is_mut },
            }));
          }
          let ret_ty = self.check_ty(ret_ty)?;
          let ty = self.alloc(TyS::Fn(ty_params, ret_ty));

          let obj = self.arena.alloc(ObjS {
            name: *name,
            ty: ty,
            kind: ObjKind::Fn {
              params: obj_params,
              body: None,
            }
          });
          todo_objects.push((obj, def));
          Def::Obj(obj.ptr())
        }
        Const { ty, val } => {
          let ty = self.check_ty(ty)?;
          let obj = self.arena.alloc(ObjS {
            name: *name,
            ty: ty,
            kind: ObjKind::Const {
              val: None
            }
          });
          todo_objects.push((obj, def));
          Def::Obj(obj.ptr())
        }
        Data { is_mut, ty, init } => {
          let ty = self.check_ty(ty)?;
          let obj = self.arena.alloc(ObjS {
            name: *name,
            ty: ty,
            kind: ObjKind::Data {
              is_mut: *is_mut,
              init: None
            }
          });
          todo_objects.push((obj, def));
          Def::Obj(obj.ptr())
        }
        Extern { is_mut, ty } => {
          let ty = self.check_ty(ty)?;
          Def::Obj(self.alloc(ObjS {
            name: *name,
            ty: ty,
            kind: ObjKind::Extern { is_mut: *is_mut }
          }))
        }
        ExternFn { params, ret_ty } => {
          let tys = TyS::Fn(self.check_params(params)?,
                              self.check_ty(ret_ty)?);
          let ty = self.alloc(tys);
          Def::Obj(self.alloc(ObjS {
            name: *name,
            ty: ty,
            kind: ObjKind::ExternFn
          }))
        }
      };

      self.define(*name, def);
    }

    // Pass 2: resolve references in types

    for (mut ty, def) in todo_types.into_iter() {
      *ty = match def {
        Struct { params } => TyS::Struct(self.check_params(params)?),
        Union { params } => TyS::Union(self.check_params(params)?),
        Enum { variants } => TyS::Enum(self.check_variants(variants)?),
        _ => unreachable!(),
      };
    }

    // Pass 3: type check object bodies

    for (mut obj, def) in todo_objects.into_iter() {
      match (&mut obj.kind, def) {
        (ObjKind::Fn { params, body }, Fn { body: parsed_body, .. }) => {
          self.enter();
          // Add parameters to current scope
          for (name, obj) in params {
            self.define(*name, Def::Obj(*obj));
          }
          // Type check body
          *body = Some(self.check_expr(parsed_body)?);
          self.exit();
        }
        (ObjKind::Const { val }, Const { val: parsed_val, .. }) => {
          *val = Some(self.check_expr(parsed_val)?);
        }
        (ObjKind::Data { init, .. }, Data { init: parsed_init, .. }) => {
          *init = Some(self.check_expr(parsed_init)?);
        }
        _ => unreachable!(),
      };
    }

    println!("{:#?}", self.symtab);
    Ok(())
  }
}

pub fn check_module(module: &parse::Module) -> MRes<()> {
  let mut ctx = Ctx::new(module);
  ctx.check_root()
}
