/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use super::*;

#[derive(Debug)]
struct CannotUnifyError(Ty, Ty);

impl fmt::Display for CannotUnifyError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Cannot unify types {:?} and {:?}", self.0, self.1)
  }
}

impl error::Error for CannotUnifyError {}

/// Type inference engine
///
/// The algorithm used is similar to "Algorithm J" from the paper
/// "A Theory of Type Polymorphism in Programming" by Robin Milner,
/// but with the typing rules extended with type constructors for
/// additional types supported that are irrelevant to lambda calculus.
///
/// A type is a term containing literal types and type variables, nested in
/// a variety of type constructors. Type variables are held in a context that
/// has a variety of methods for enforcing equality or other constraints on
/// types, which are called by `check.rs` according to the typing rules.
///
/// The most important operation is enforcing equality of two types. This is
/// done using Robinson's first order unification. The most important operation
/// arises when the unification algorithm finds that two type variables must be
/// equal. Type variables are represented as a "disjoint-set forset", where each
/// set is a set of type variables that are deemed equal. When two type variables
/// are found to be equal during unification, the union of the sets they
/// represent is computed using the union-find algorithm.

#[derive(Debug)]
pub(super) struct TVarCtx {
  tvars: Vec<Ty>
}

impl TVarCtx {
  pub(super) fn new() -> Self {
    Self {
      tvars: vec![],
    }
  }

  pub(super) fn tvar(&mut self, bound: Ty) -> Ty {
    let ty = Ty::TVar(self.tvars.len());
    self.tvars.push(bound);
    ty
  }

  fn root(&mut self, idx: usize) -> usize {
    if let Ty::TVar(parent) = &self.tvars[idx] {
      let parent = *parent;
      let root = self.root(parent);
      self.tvars[idx] = Ty::TVar(root);
      root
    } else {
      idx
    }
  }

  pub(super) fn unify(&mut self, ty1: &Ty, ty2: &Ty) -> MRes<Ty> {
    use Ty::*;
    'error: loop {
      return Ok(match (ty1, ty2) {
        (Bool, Bool) => Bool,
        (Uint8, Uint8) => Uint8,
        (Int8, Int8) => Int8,
        (Uint16, Uint16) => Uint16,
        (Int16, Int16) => Int16,
        (Uint32, Uint32) => Uint32,
        (Int32, Int32) => Int32,
        (Uint64, Uint64) => Uint64,
        (Int64, Int64) => Int64,
        (Uintn, Uintn) => Uintn,
        (Intn, Intn) => Intn,
        (Float, Float) => Float,
        (Double, Double) => Double,
        (StructRef(name, (def_id, targs1)), StructRef(_, (def_id2, targs2))) if def_id == def_id2 => {
          let targs = targs1
            .iter()
            .zip(targs2.iter())
            .map(|(ty1, ty2)| self.unify(ty1, ty2))
            .monadic_collect()?;
          StructRef(*name, (*def_id, targs))
        }
        (UnionRef(name, (def_id, targs1)), UnionRef(_, (def_id2, targs2))) if def_id == def_id2 => {
          let targs = targs1
            .iter()
            .zip(targs2.iter())
            .map(|(ty1, ty2)| self.unify(ty1, ty2))
            .monadic_collect()?;
          UnionRef(*name, (*def_id, targs))
        }
        (EnumRef(name, (def_id, targs1)), EnumRef(_, (def_id2, targs2))) if def_id == def_id2 => {
          let targs = targs1
            .iter()
            .zip(targs2.iter())
            .map(|(ty1, ty2)| self.unify(ty1, ty2))
            .monadic_collect()?;
          EnumRef(*name, (*def_id, targs))
        }
        (Func(par1, va1, ret1),
          Func(par2, va2, ret2)) if par1.len() == par2.len() && va1 == va2 => {
          let mut par = Vec::new();
          for ((n1, t1), (n2, t2)) in par1.iter().zip(par2.iter()) {
            if n1 != n2 {
              break 'error;
            }
            par.push((*n1, self.unify(t1, t2)?));
          }
          Func(par, *va1,Box::new(self.unify(ret1, ret2)?))
        }
        (Ptr(is_mut1, base1), Ptr(is_mut2, base2)) => {
          let is_mut = if *is_mut1 == IsMut::Yes
              && *is_mut2 == IsMut::Yes { IsMut::Yes } else { IsMut::No };
          Ptr(is_mut, Box::new(self.unify(base1, base2)?))
        }
        (Arr(siz1, elem1), Arr(siz2, elem2)) if siz1 == siz2 => {
          Arr(*siz1, Box::new(self.unify(elem1, elem2)?))
        }
        (Unit, Unit) => {
          Unit
        }
        (Tuple(par1), Tuple(par2)) if par1.len() == par2.len() => {
          let mut par = Vec::new();
          for ((n1, t1), (n2, t2)) in par1.iter().zip(par2.iter()) {
            if n1 != n2 {
              break 'error;
            }
            par.push((*n1, self.unify(t1, t2)?));
          }
          Tuple(par)
        }
        (TVar(idx1), TVar(idx2)) => {
          // Find root nodes
          let root1 = self.root(*idx1);
          let root2 = self.root(*idx2);

          // Apply union-find if they are different
          if root1 != root2 {
            // Unify bounds
            let unified = self.unify(&self.tvars[root1].clone(),
                                     &self.tvars[root2].clone())?;
            // Store unified bound in root1
            self.tvars[root1] = unified;
            // Point root2 to root1
            self.tvars[root2] = TVar(root1);
          }

          // Return reference to new root
          TVar(root1)
        }
        (TVar(idx), ty) | (ty, TVar(idx)) => {
          // Find root node
          let root = self.root(*idx);

          // Unify bounds
          let unified = self.unify(&self.tvars[root].clone(), ty)?;
          // Store unified bound
          self.tvars[root] = unified;

          // Return reference to root
          TVar(root)
        }

        // Any type
        (BoundAny, ty) | (ty, BoundAny) => ty.clone(),

        // Numeric types
        (BoundNum, ty @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|
                          Uintn|Intn|Float|Double|BoundNum|BoundInt|BoundFlt)) |
        (ty @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|
              Uintn|Intn|Float|Double|BoundInt|BoundFlt), BoundNum) => {
          ty.clone()
        }

        // Integer types
        (BoundInt, ty @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|Uintn|Intn|BoundInt)) |
        (ty @ (Uint8|Int8|Uint16|Int16|Uint32|Int32|Uint64|Int64|Uintn|Intn), BoundInt) => {
          ty.clone()
        }

        // Floating types
        (BoundFlt, ty @ (Float|Double|BoundFlt)) |
        (ty @ (Float|Double), BoundFlt) => {
          ty.clone()
        }

        _ => break 'error,
      });
    }

    // Types cannot unify
    Err(Box::new(CannotUnifyError(ty1.clone(), ty2.clone())))
  }

  /// Obtain the literal type for a type expression

  pub(super) fn lit_ty(&mut self, ty: &Ty) -> Ty {
    use Ty::*;
    match ty {
      Bool => Bool,
      Uint8 => Uint8,
      Int8 => Int8,
      Uint16 => Uint16,
      Int16 => Int16,
      Uint32 => Uint32,
      Int32 => Int32,
      Uint64 => Uint64,
      Int64 => Int64,
      Uintn => Uintn,
      Intn => Intn,
      Float => Float,
      Double => Double,
      StructRef(name, (id, targs)) => {
        let targs = targs
          .iter()
          .map(|ty| self.lit_ty(ty))
          .collect();
        StructRef(*name, (*id, targs))
      }
      UnionRef(name, (id, targs)) => {
        let targs = targs
          .iter()
          .map(|ty| self.lit_ty(ty))
          .collect();
        UnionRef(*name, (*id, targs))
      }
      EnumRef(name, (id, targs)) => {
        let targs = targs
          .iter()
          .map(|ty| self.lit_ty(ty))
          .collect();
        EnumRef(*name, (*id, targs))
      }
      Ptr(is_mut, ty) => Ptr(*is_mut, Box::new(self.lit_ty(&**ty))),
      Func(params, va, ty) => {
        let params = params
          .iter()
          .map(|(name, ty)| (*name, self.lit_ty(ty)))
          .collect();
        Func(params, *va, Box::new(self.lit_ty(&**ty)))
      }
      Arr(cnt, ty) => Arr(*cnt, Box::new(self.lit_ty(&**ty))),
      Unit => {
        Unit
      }
      Tuple(params) => {
        let params = params
          .iter()
          .map(|(name, ty)| (*name, self.lit_ty(ty)))
          .collect();
        Tuple(params)
      }
      TVar(idx) => {
        // Find root element
        let root = self.root(*idx);
        // Obtain real type from its bound
        self.lit_ty(&self.tvars[root].clone())
      }
      BoundAny => Tuple(vec![]),
      BoundNum => Int32,
      BoundInt => Int32,
      BoundFlt => Float,
    }
  }

  /// Literalize the outermost part of a type expression
  pub(super) fn lit_ty_nonrecusrive(&mut self, ty: &Ty) -> Ty {
    match ty {
      Ty::TVar(idx) => {
        // Find root element
        let root = self.root(*idx);
        // Obtain real type from its bound
        self.lit_ty(&self.tvars[root].clone())
      }
      _ => ty.clone()
    }
  }


  pub(super) fn root_type_args(&mut self, type_args: &Vec<Ty>) -> Vec<Ty> {
    type_args.iter().map(|ty| self.root_ty(ty)).collect()
  }

  pub(super) fn root_ty(&mut self, ty: &Ty) -> Ty {
    use Ty::*;
    match ty {
      Bool => Bool,
      Uint8 => Uint8,
      Int8 => Int8,
      Uint16 => Uint16,
      Int16 => Int16,
      Uint32 => Uint32,
      Int32 => Int32,
      Uint64 => Uint64,
      Int64 => Int64,
      Uintn => Uintn,
      Intn => Intn,
      Float => Float,
      Double => Double,
      StructRef(name, (id, type_args)) => {
        StructRef(*name, (*id, self.root_type_args(type_args)))
      }
      UnionRef(name, (id, type_args)) => {
        UnionRef(*name, (*id, self.root_type_args(type_args)))
      }
      EnumRef(name, (id, type_args)) => {
        EnumRef(*name, (*id, self.root_type_args(type_args)))
      }
      Ptr(is_mut, ty) => {
        Ptr(*is_mut, Box::new(self.root_ty(ty)))
      }
      Func(params, va, ty) => {
        let params = params
          .iter()
          .map(|(name, ty)| (*name, self.root_ty(ty)))
          .collect();
        Func(params, *va, Box::new(self.root_ty(ty)))
      }
      Arr(cnt, ty) => {
        Arr(*cnt, Box::new(self.root_ty(ty)))
      }
      Unit => {
        Unit
      }
      Tuple(params) => {
        let params = params
          .iter()
          .map(|(name, ty)| (*name, self.root_ty(ty)))
          .collect();
        Tuple(params)
      }
      TVar(idx) => {
        TVar(self.root(*idx))
      }
      BoundAny => BoundAny,
      BoundNum => BoundNum,
      BoundInt => BoundInt,
      BoundFlt => BoundFlt
    }
  }
}

