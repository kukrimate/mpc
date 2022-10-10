use crate::parse;
use crate::util::*;
use indexmap::{indexmap,IndexMap};
use std::{error,fmt};
use std::collections::{HashMap};

/// Syntax tree after type checking

pub type Ty = Ptr<TyS>;

#[derive(Debug)]
pub enum TyS {
  Invalid,

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
  types: Arena<TyS>,

  // Global symbol table
  globals: HashMap<RefStr, Ty>,
}

impl<'ctx> Ctx<'ctx> {
  fn new(module: &'ctx parse::Module) -> Self {
    Ctx { module, types: Arena::new(), globals: HashMap::new() }
  }

  fn alloc_ty(&mut self, ty: TyS) -> Ptr<TyS> {
    self.types.alloc(ty).ptr()
  }

  fn resolve_ty(&mut self, name: RefStr) -> MRes<Ty> {
    match self.globals.get(&name) {
      Some(ty) => Ok(*ty),
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
          nparams.insert(*name, self.alloc_ty(TyS::Unit(*name)));
        }
        Struct(params) => {
          let sparams = self.check_params(params)?;
          nparams.insert(*name, self.alloc_ty(TyS::Struct(*name, sparams)));
        }
      }
    }
    Ok(nparams)
  }

  fn check_ty(&mut self, ty: &parse::Ty) -> MRes<Ty> {
    use parse::Ty::*;
    Ok(match ty {
      Bool => self.alloc_ty(TyS::Bool),
      Uint8 => self.alloc_ty(TyS::Uint8),
      Int8 => self.alloc_ty(TyS::Int8),
      Uint16 => self.alloc_ty(TyS::Uint16),
      Int16 => self.alloc_ty(TyS::Int16),
      Uint32 => self.alloc_ty(TyS::Uint32),
      Int32 => self.alloc_ty(TyS::Int32),
      Uint64 => self.alloc_ty(TyS::Uint64),
      Int64 => self.alloc_ty(TyS::Int64),
      Uintn => self.alloc_ty(TyS::Uintn),
      Intn => self.alloc_ty(TyS::Intn),
      Float => self.alloc_ty(TyS::Float),
      Double => self.alloc_ty(TyS::Double),
      Path(path) => self.resolve_ty(path[0])?,
      Fn(params, ret_ty) => {
        let ty = TyS::Fn(self.check_params(params)?,
                              self.check_ty(ret_ty)?);
        self.alloc_ty(ty)
      },
      Ptr(base_ty) => {
        let ty = TyS::Ptr(self.check_ty(base_ty)?);
        self.alloc_ty(ty)
      },
      Arr(elem_cnt, elem_ty) => {
        // FIXME: evaluate elem_cnt constant expression
        let ty = TyS::Arr(0, self.check_ty(elem_ty)?);
        self.alloc_ty(ty)
      },
      Tuple(params) => {
        let ty = TyS::Tuple(self.check_params(params)?);
        self.alloc_ty(ty)
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
          let ty = self.alloc_ty(TyS::Invalid);
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
      match def {
        Struct { .. } | Union { .. } | Enum { .. } => (),
        _ => continue,
      }

      let ptr_mut = self.types.alloc(TyS::Invalid);
      self.globals.insert(*name, ptr_mut.ptr());
      todo.push((*name, def, ptr_mut));
    }

    // Pass 2: resolve references
    for (name, def, ptr_mut) in &mut todo {
      let ty = match def {
        Struct { params } => TyS::Struct(*name, self.check_params(params)?),
        Union { params } => TyS::Union(*name, self.check_params(params)?),
        Enum { variants } => TyS::Enum(*name, self.check_variants(variants)?),
        _ => unreachable!(),
      };
      **ptr_mut = ty;
    }


    println!("{:#?}", self.globals);

    Ok(())
  }
}

pub fn check_module(module: &parse::Module) -> MRes<()> {
  let mut ctx = Ctx::new(module);
  ctx.check_root()
}
