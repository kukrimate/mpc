use crate::parse;
use crate::util::*;
use indexmap::{indexmap,IndexMap};
use std::{error,fmt};
use std::ops::DerefMut;
use std::collections::{HashMap};

/// Syntax tree after type checking

pub type Ty = Ptr<TyS>;

#[derive(Debug)]
pub enum TyS {
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
  Struct(RefStr, IndexMap<RefStr, Ty>),
  Union(RefStr, IndexMap<RefStr, Ty>),
  Enum(RefStr, IndexMap<RefStr, Ty>),
}

impl core::cmp::PartialEq for TyS {
  fn eq(&self, rhs: &TyS) -> bool {
    use TyS::*;

    fn eq_params(p1: &IndexMap<RefStr, Ty>, p2: &IndexMap<RefStr, Ty>) -> bool {
      if p1.len() != p2.len() {
        return false;
      }
      for ((n1, t1), (n2, t2)) in p1.iter().zip(p2.iter()) {
        if n1 != n2 || t1 != t2 {
          return false;
        }
      }
      true
    }

    match (self, rhs) {
      (Bool, Bool)|(Uint8, Uint8)|(Int8, Int8)|
      (Uint16, Uint16)|(Int16, Int16)|(Uint32, Uint32)|
      (Int32, Int32)|(Uint64, Uint64)|(Int64, Int64)|
      (Uintn, Uintn)|(Intn, Intn)|(Float, Float)|
      (Double, Double) => true,
      (Fn(p1, r1), Fn(p2, r2)) => r1 == r2 && eq_params(p1, p2),
      (Ptr(ty1), Ptr(ty2)) => ty1 == ty2,
      (Arr(s1, ty1), Arr(s2, ty2)) => s1 == s2 && ty1 == ty2,
      (Unit(n1), Unit(n2)) => n1 == n2,
      (Tuple(p1), Tuple(p2)) => eq_params(p1, p2),
      (Struct(n1, _), Struct(n2, _)) => n1 == n2,
      (Union(n1, _), Union(n2, _)) => n1 == n2,
      (Enum(n1, _), Enum(n2, _)) => n1 == n2,
      _ => false,
    }
  }
}

impl core::cmp::Eq for TyS {}

impl core::hash::Hash for TyS {
  fn hash<H: core::hash::Hasher>(&self, h: &mut H) {
    use TyS::*;

    fn hash_params<H: core::hash::Hasher>(p: &IndexMap<RefStr, Ty>, h: &mut H) {
      for (n, t) in p {
        n.hash(h);
        t.hash(h);
      }
    }

    match self {
      Bool => 0.hash(h),
      Uint8 => 1.hash(h),
      Int8 => 2.hash(h),
      Uint16 => 3.hash(h),
      Int16 => 4.hash(h),
      Uint32 => 5.hash(h),
      Int32 => 6.hash(h),
      Uint64 => 7.hash(h),
      Int64 => 8.hash(h),
      Uintn => 9.hash(h),
      Intn => 10.hash(h),
      Float => 11.hash(h),
      Double => 12.hash(h),
      Fn(p, r) => {
        13.hash(h);
        hash_params(p, h);
        r.hash(h);
      },
      Ptr(t) => {
        14.hash(h);
        t.hash(h);
      },
      Arr(n, t) => {
        15.hash(h);
        n.hash(h);
        t.hash(h);
      },
      Unit(n) => {
        16.hash(h);
        n.hash(h);
      },
      Tuple(p) => {
        17.hash(h);
        hash_params(p, h);
      },
      Struct(n, _) => {
        18.hash(h);
        n.hash(h);
      },
      Union(n, _) => {
        19.hash(h);
        n.hash(h);
      },
      Enum(n, _) => {
        20.hash(h);
        n.hash(h);
      },
    }
  }
}

/// Errors occuring during type checking

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

struct Ctx<'ctx> {
  module: &'ctx parse::Module,

  // Type interning pool
  types: InternPool<TyS>,

  // Global symbol table
  globals: HashMap<RefStr, Ty>,
}

impl<'ctx> Ctx<'ctx> {
  fn new(module: &'ctx parse::Module) -> Self {
    Ctx { module, types: InternPool::new(), globals: HashMap::new() }
  }

  fn intern_ty(&mut self, ty: TyS) -> Ty {
    self.types.intern(ty).ptr()
  }

  fn resolve_ty(&mut self, name: RefStr) -> MRes<Ty> {
    match self.globals.get(&name) {
      Some(ptr) => {
        Ok(*ptr)
      }
      None => {
        Err(Box::new(UnknownTypeError { name }))
      }
    }
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
          nparams.insert(*name, self.intern_ty(TyS::Unit(*name)));
        }
        Struct(params) => {
          let sparams = self.check_params(params)?;
          nparams.insert(*name, self.intern_ty(TyS::Struct(*name, sparams)));
        }
      }
    }
    Ok(nparams)
  }

  fn check_ty(&mut self, ty: &parse::Ty) -> MRes<Ty> {
    use parse::Ty::*;
    Ok(match ty {
      Bool => self.intern_ty(TyS::Bool),
      Uint8 => self.intern_ty(TyS::Uint8),
      Int8 => self.intern_ty(TyS::Int8),
      Uint16 => self.intern_ty(TyS::Uint16),
      Int16 => self.intern_ty(TyS::Int16),
      Uint32 => self.intern_ty(TyS::Uint32),
      Int32 => self.intern_ty(TyS::Int32),
      Uint64 => self.intern_ty(TyS::Uint64),
      Int64 => self.intern_ty(TyS::Int64),
      Uintn => self.intern_ty(TyS::Uintn),
      Intn => self.intern_ty(TyS::Intn),
      Float => self.intern_ty(TyS::Float),
      Double => self.intern_ty(TyS::Double),
      Path(path) => self.resolve_ty(path[0])?,
      Fn(params, ret_ty) => {
        let ty = TyS::Fn(self.check_params(params)?,
                              self.check_ty(ret_ty)?);
        self.intern_ty(ty)
      },
      Ptr(base_ty) => {
        let ty = TyS::Ptr(self.check_ty(base_ty)?);
        self.intern_ty(ty)
      },
      Arr(elem_cnt, elem_ty) => {
        // FIXME: evaluate elem_cnt constant expression
        let ty = TyS::Arr(0, self.check_ty(elem_ty)?);
        self.intern_ty(ty)
      },
      Tuple(params) => {
        let ty = TyS::Tuple(self.check_params(params)?);
        self.intern_ty(ty)
      }
    })
  }

/*
  fn enter_scope(&mut self) {
    self.scopes.push(HashMap::new());
  }

  fn define_local(&mut self, name: RefStr, def: LocalDef<'ctx>) {
    assert!(self.scopes.len() > 0);
    self.scopes.last_mut().unwrap().insert(name, def);
  }

  fn exit_scope(&mut self) {
    assert!(self.scopes.len() > 0);
    self.scopes.pop();
  }

  fn check_root(&mut self) -> MRes<()> {
    // Pass 1: create symbols
    let mut todo = vec![];

    for (name, def) in &self.module.defs {
      use parse::Def::*;
      match def {
        Struct { .. } | Union { .. } | Enum { .. } => {
          let ty = self.intern_ty(TyS::Invalid);
          todo.push((*name, def, ty));
          self.globals.insert(*name, ty);
        }
        _ => ()
      }
    }

    // Pass 2: resolve references

  /*
    for (name, def, mem) in &mut todo {
      use parse::Def::*;
      match def {
        Struct { params } => {
          **mem = TyS::Struct(*name, self.check_params(params)?);
        }
        Union { params } => {
          **mem = TyS::Union(*name, self.check_params(params)?);
        }
        Enum { variants } => {
          **mem = TyS::Enum(*name, self.check_variants(variants)?);
        }
        _ => ()
      }
    }
  */

    println!("{:?}", self.globals);

/*
    for (_, def) in &self.module.defs {
      use parse::Def::*;
      match &def {
        Struct { params } => {
          self.check_ty(ty)?;
        },
        Fn { params, ret_ty, body } => {
          self.enter_scope();
          for (name, (is_mut, ty)) in params {
            self.check_ty(ty)?;
          }
          self.exit_scope();
        },
        Const { ty, val } => {
          self.check_ty(ty)?;
        },
        Data { is_mut, ty, init } => {
          self.check_ty(ty)?;
        },
        Extern { is_mut, ty } => {
          self.check_ty(ty)?;
        },
        ExternFn { params, ret_ty } => {
          for (_, ty) in params {
            self.check_ty(ty)?;
          }
          self.check_ty(ret_ty)?;
        },
      }
    }
*/

    Ok(())
  }
  */

  fn check_root(&mut self) -> MRes<()> {
    use parse::Def::*;

    // Pass 1: create symbols
    let mut todo = vec![];

    for (name, def) in &self.module.defs {

      let ty = match def {
        Struct { .. } => self.types.intern(TyS::Struct(*name, indexmap!{})).ptr_mut(),
        Union { .. } => self.types.intern(TyS::Union(*name, indexmap!{})).ptr_mut(),
        Enum { .. } => self.types.intern(TyS::Enum(*name, indexmap!{})).ptr_mut(),
        _ => continue,
      };

      self.globals.insert(*name, ty.ptr());
      todo.push((ty, def));
    }

    // Pass 2: resolve references
    for (ty, def) in &mut todo {
      match (ty.deref_mut(), def) {
        (TyS::Struct(_, dest), Struct { ref params, .. }) => {
          *dest = self.check_params(params)?;
        },
        (TyS::Union(_, dest), Union { ref params, .. }) => {
          *dest = self.check_params(params)?;
        },
        (TyS::Enum(_, dest), Enum { ref variants, .. }) => {
          *dest = self.check_variants(variants)?;
        },
        _ => unreachable!(),
      }
    }


    println!("{:#?}", self.globals);

    Ok(())
  }
}

pub fn check_module(module: &parse::Module) -> MRes<()> {
  let mut ctx = Ctx::new(module);
  ctx.check_root()
}
