use crate::*;
use crate::ast::*;
use crate::util::*;
use std::collections::HashMap;

/// Errors occuring during type checking

#[derive(Debug)]
struct UnknownTypeError {
  path: Path
}

impl fmt::Display for UnknownTypeError {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    // FIXME: print entire path
    write!(fmt, "Unknown typename {}", self.path[0])
  }
}

impl error::Error for UnknownTypeError {}

#[derive(Debug)]
struct UnknownObjectError {
  path: Path
}

impl fmt::Display for UnknownObjectError {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    // FIXME: print entire path
    write!(fmt, "Unknown object {}", self.path[0])
  }
}

impl error::Error for UnknownObjectError {}

/// Local definitions

enum LocalDef {
  Param { is_mut: bool, ty: &'static Ty },
  Let { is_mut: bool, ty: Ty },
}

struct Ctx<'a> {
  module: &'a mut Module,
  scopes: Vec<HashMap<RefStr, LocalDef>>,

  // Context

}

impl<'a> Ctx<'a> {
  fn new(module: &'a mut Module) -> Self {
    Ctx { module, scopes: vec![] }
  }

  fn resolve_ty(&mut self, path: &Path) -> MRes<&'static Ty> {
    // FIXME: resolve based on full path
    if let Some(Def::Ty(ty)) = self.module.defs.get(&path[0]) {
      Ok(evil(&ty))
    } else {
      Err(Box::new(UnknownTypeError { path: path.clone() }))
    }
  }

  fn check_ty(&mut self, ty: &mut Ty) -> MRes<()> {
    use Ty::*;
    match ty {
      Bool | Uint8 | Int8 | Uint16 | Int16 |  Uint32 |
      Int32 | Uint64 | Int64 | Uintn | Intn | Float |
      Double | Enumerator => {
        Ok(())
      },
      Path(path) => {
        let r = self.resolve_ty(&path)?;
        *ty = Ref(r);
        Ok(())
      },
      Fn(params, ret_ty) => {
        for (_, ty) in params {
          self.check_ty(ty)?;
        }
        self.check_ty(ret_ty)
      },
      Ptr(ty) | Arr(_, ty) => {
        self.check_ty(ty)
      },
      Tuple(params) | Struct(params) | Union(params) | Enum(params) => {
        for (_, ty) in params {
          self.check_ty(ty)?;
        }
        Ok(())
      },
      Ref(_) => unreachable!(),
    }
  }

  fn enter_scope(&mut self) {
    self.scopes.push(HashMap::new());
  }

  fn define_local(&mut self, name: RefStr, def: LocalDef) {
    assert!(self.scopes.len() > 0);
    self.scopes.last_mut().unwrap().insert(name, def);
  }

  fn exit_scope(&mut self) {
    assert!(self.scopes.len() > 0);
    self.scopes.pop();
  }

  fn check_expr(&mut self, expr: &mut Expr) -> MRes<()> {
    Ok(())
  }

  fn check_root(&mut self) -> MRes<()> {
    for (_, mut def) in evil_mut(&mut self.module.defs) {
      use Def::*;
      match &mut def {
        Ty(ref mut ty) => self.check_ty(ty)?,
        Fn { params, ret_ty, body } => {
          self.enter_scope();
          for (name, (is_mut, ty)) in params.iter_mut() {
            self.check_ty(ty)?;
            self.define_local(*name, LocalDef::Param {
              is_mut: *is_mut, ty: evil(ty)
            });
          }
          self.check_expr(body)?;
          self.exit_scope();
        },
        Const { ty, val } => {
          self.check_ty(ty)?;
          self.check_expr(val)?;
        },
        Data { is_mut, ty, init } => {
          self.check_ty(ty)?;
          self.check_expr(init)?;
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
    Ok(())
  }
}

pub fn check_module(module: &mut Module) -> MRes<()> {
  let mut ctx = Ctx::new(module);
  ctx.check_root()
}
