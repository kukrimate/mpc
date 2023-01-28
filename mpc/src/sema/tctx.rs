/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

//
// Type inference engine
//
// The algorithm used is similar to "Algorithm J" from the paper
// "A Theory of Type Polymorphism in Programming" by Robin Milner,
// but with the typing rules extended with type constructors for
// additional types supported that are irrelevant to lambda calculus.
//
// A type is a term containing literal types and type variables, nested in
// a variety of type constructors. Type variables are held in a context that
// has a variety of methods for enforcing equality or other constraints on
// types, which are called by `infer.rs` according to the typing rules.
//
// The most important operation is enforcing equality of two types. This is
// done using Robinson's first order unification. The most challenging case of
// this arises when the unification algorithm finds that two type variables must
// be equal. Type variables are represented as a "disjoint-set forest", where each
// set is a set of type variables that are deemed equal. When two type variables
// are found to be equal during unification, the union of the sets they
// represent is computed using the union-find algorithm.
//


use std::fmt::Formatter;
use super::*;

pub struct TVarCtx {
  tvars: Vec<Bound>
}

#[derive(Clone,Debug)]
pub enum Bound {
  Is(Ty),
  Any,
  Eq,
  Num,
  Int,
  Flt
}

impl TVarCtx {
  pub fn new() -> Self {
    Self {
      tvars: vec![],
    }
  }

  pub fn new_var(&mut self, bound: Bound) -> Ty {
    let ty = Ty::Var(self.tvars.len());
    self.tvars.push(bound);
    ty
  }

  fn root(&mut self, idx: usize) -> (usize, Bound) {
    match &self.tvars[idx] {
      Bound::Is(Ty::Var(parent)) => {
        let parent = *parent;
        let (root, bound) = self.root(parent);
        self.tvars[idx] = Bound::Is(Ty::Var(root));
        (root, bound)
      }
      bound => {
        (idx, bound.clone())
      }
    }
  }

  /// Unify two type expressions
  pub fn unify(&mut self, ty1: &Ty, ty2: &Ty) -> MRes<Ty> {
    match (ty1, ty2) {
      (Ty::Bool, Ty::Bool) => Ok(Ty::Bool),
      (Ty::Uint8, Ty::Uint8) => Ok(Ty::Uint8),
      (Ty::Int8, Ty::Int8) => Ok(Ty::Int8),
      (Ty::Uint16, Ty::Uint16) => Ok(Ty::Uint16),
      (Ty::Int16, Ty::Int16) => Ok(Ty::Int16),
      (Ty::Uint32, Ty::Uint32) => Ok(Ty::Uint32),
      (Ty::Int32, Ty::Int32) => Ok(Ty::Int32),
      (Ty::Uint64, Ty::Uint64) => Ok(Ty::Uint64),
      (Ty::Int64, Ty::Int64) => Ok(Ty::Int64),
      (Ty::Uintn, Ty::Uintn) => Ok(Ty::Uintn),
      (Ty::Intn, Ty::Intn) => Ok(Ty::Intn),
      (Ty::Float, Ty::Float) => Ok(Ty::Float),
      (Ty::Double, Ty::Double) => Ok(Ty::Double),
      (Ty::StructRef(name, (def_id, targs1)), Ty::StructRef(_, (def_id2, targs2))) if def_id == def_id2 => {
        let targs = targs1
          .iter()
          .zip(targs2.iter())
          .map(|(ty1, ty2)| self.unify(ty1, ty2))
          .monadic_collect()?;
        Ok(Ty::StructRef(*name, (*def_id, targs)))
      }
      (Ty::UnionRef(name, (def_id, targs1)), Ty::UnionRef(_, (def_id2, targs2))) if def_id == def_id2 => {
        let targs = targs1
          .iter()
          .zip(targs2.iter())
          .map(|(ty1, ty2)| self.unify(ty1, ty2))
          .monadic_collect()?;
        Ok(Ty::UnionRef(*name, (*def_id, targs)))
      }
      (Ty::EnumRef(name, (def_id, targs1)), Ty::EnumRef(_, (def_id2, targs2))) if def_id == def_id2 => {
        let targs = targs1
          .iter()
          .zip(targs2.iter())
          .map(|(ty1, ty2)| self.unify(ty1, ty2))
          .monadic_collect()?;
        Ok(Ty::EnumRef(*name, (*def_id, targs)))
      }
      (Ty::Func(par1, va1, ret1), Ty::Func(par2, va2, ret2)) if par1.len() == par2.len() && va1 == va2 => {
        let mut par = Vec::new();
        for ((n1, t1), (n2, t2)) in par1.iter().zip(par2.iter()) {
          if n1 != n2 {
            Err(Box::new(CannotUnifyError::Types(ty1.clone(), ty2.clone())))?
          }
          par.push((*n1, self.unify(t1, t2)?));
        }
        Ok(Ty::Func(par, *va1,Box::new(self.unify(ret1, ret2)?)))
      }
      (Ty::Ptr(is_mut1, base1), Ty::Ptr(is_mut2, base2)) => {
        let is_mut = if *is_mut1 == IsMut::Yes
          && *is_mut2 == IsMut::Yes { IsMut::Yes } else { IsMut::No };
        Ok(Ty::Ptr(is_mut, Box::new(self.unify(base1, base2)?)))
      }
      (Ty::Arr(siz1, elem1), Ty::Arr(siz2, elem2)) if siz1 == siz2 => {
        Ok(Ty::Arr(*siz1, Box::new(self.unify(elem1, elem2)?)))
      }
      (Ty::Unit, Ty::Unit) => {
        Ok(Ty::Unit)
      }
      (Ty::Tuple(par1), Ty::Tuple(par2)) if par1.len() == par2.len() => {
        let mut par = Vec::new();
        for ((n1, t1), (n2, t2)) in par1.iter().zip(par2.iter()) {
          if n1 != n2 {
            Err(Box::new(CannotUnifyError::Types(ty1.clone(), ty2.clone())))?
          }
          par.push((*n1, self.unify(t1, t2)?));
        }
        Ok(Ty::Tuple(par))
      }
      (Ty::Var(idx1), Ty::Var(idx2)) => {
        // Find root nodes
        let (root1, bound1) = self.root(*idx1);
        let (root2, bound2) = self.root(*idx2);

        // Apply union-find if they are different
        if root1 != root2 {
          // Unify bounds
          let unified = self.unify_bounds(&bound1, &bound2)?;
          // Store unified bound in root1
          self.tvars[root1] = unified;
          // Point root2 to root1
          self.tvars[root2] = Bound::Is(Ty::Var(root1));
        }
        // Return reference to new root
        Ok(Ty::Var(root1))
      }
      (Ty::Var(idx), ty) | (ty, Ty::Var(idx)) => {
        // Find root node
        let (root, prev) = self.root(*idx);
        // Unify bounds
        let unified = self.unify_bounds(&prev, &Bound::Is(ty.clone()))?;
        // Store unified bound
        self.tvars[root] = unified;
        // Return reference to root
        Ok(Ty::Var(root))
      }
      _ => Err(Box::new(CannotUnifyError::Types(ty1.clone(), ty2.clone())))?
    }
  }

  /// Bound a type expression
  pub fn bound(&mut self, ty: &Ty, bound: &Bound) -> MRes<Ty> {
    match ty {
      Ty::Var(idx) => {
        // Find root node
        let (root, prev) = self.root(*idx);
        // Unify bounds
        let unified = self.unify_bounds(&prev, bound)?;
        // Store unified bound
        self.tvars[root] = unified;
        // Return reference to root
        Ok(Ty::Var(root))
      }
      _ => {
        // Check type against bound
        self.unify_bounds(&Bound::Is(ty.clone()), bound)?;
        // Return clone of type
        Ok(ty.clone())
      }
    }
  }

  fn unify_bounds(&mut self, b1: &Bound, b2: &Bound) -> MRes<Bound> {
    match (b1, b2) {
      // Compare two literal types
      (Bound::Is(ty1), Bound::Is(ty2)) => Ok(Bound::Is(self.unify(ty1, ty2)?)),

      // Check literal type for bound
      (Bound::Is(ty), bound) |
      (bound, Bound::Is(ty)) => {
        match (bound, ty) {
          (_, Ty::Var(..)) => unreachable!(),

          (Bound::Any, _) |
          (Bound::Eq,  Ty::Bool|
          Ty::Int8|Ty::Int16|Ty::Int32|Ty::Int64|Ty::Intn|
          Ty::Uint8|Ty::Uint16|Ty::Uint32|Ty::Uint64|Ty::Uintn|
          Ty::Float|Ty::Double|
          Ty::Ptr(..)|Ty::Func(..)) |
          (Bound::Num, Ty::Int8|Ty::Int16|Ty::Int32|Ty::Int64|Ty::Intn|
          Ty::Uint8|Ty::Uint16|Ty::Uint32|Ty::Uint64|Ty::Uintn|
          Ty::Float|Ty::Double) |
          (Bound::Int, Ty::Int8|Ty::Int16|Ty::Int32|Ty::Int64|Ty::Intn|
          Ty::Uint8|Ty::Uint16|Ty::Uint32|Ty::Uint64|Ty::Uintn) |
          (Bound::Flt, Ty::Float|Ty::Double)

          => Ok(Bound::Is(ty.clone())),

          _ => Err(Box::new(CannotUnifyError::TypeDoesNotHaveBound(ty.clone(), bound.clone())))
        }
      }

      // Choose the narrower of two bounds
      // The following subset relations exist between bounds:
      // Any > Eq > Num > Int
      //                > Flt
      (Bound::Any, bound) | (bound, Bound::Any) |

      (Bound::Eq, bound @ (Bound::Eq | Bound::Num | Bound::Int | Bound::Flt)) |
      (bound @ (Bound::Num | Bound::Int | Bound::Flt), Bound::Eq) |

      (Bound::Num, bound @ (Bound::Num | Bound::Int | Bound::Flt)) |
      (bound @ (Bound::Int | Bound::Flt), Bound::Num) |

      (bound @ Bound::Int, Bound::Int) |

      (bound @ Bound::Flt, Bound::Flt)

      => Ok(bound.clone()),

      _ => Err(Box::new(CannotUnifyError::Bounds(b1.clone(), b1.clone())))
    }
  }

  /// Find the canonical form of a type expression
  pub fn canonical_ty(&mut self, ty: &Ty) -> Ty {
    match ty {
      Ty::Bool => Ty::Bool,
      Ty::Uint8 => Ty::Uint8,
      Ty::Int8 => Ty::Int8,
      Ty::Uint16 => Ty::Uint16,
      Ty::Int16 => Ty::Int16,
      Ty::Uint32 => Ty::Uint32,
      Ty::Int32 => Ty::Int32,
      Ty::Uint64 => Ty::Uint64,
      Ty::Int64 => Ty::Int64,
      Ty::Uintn => Ty::Uintn,
      Ty::Intn => Ty::Intn,
      Ty::Float => Ty::Float,
      Ty::Double => Ty::Double,
      Ty::StructRef(name, (def_id, type_args)) => {
        let type_args = type_args
          .iter()
          .map(|ty| self.canonical_ty(ty))
          .collect();
        Ty::StructRef(*name, (*def_id, type_args))
      }
      Ty::UnionRef(name, (def_id, type_args)) => {
        let type_args = type_args
          .iter()
          .map(|ty| self.canonical_ty(ty))
          .collect();
        Ty::UnionRef(*name, (*def_id, type_args))
      }
      Ty::EnumRef(name, (def_id, type_args)) => {
        let type_args = type_args
          .iter()
          .map(|ty| self.canonical_ty(ty))
          .collect();
        Ty::EnumRef(*name, (*def_id, type_args))
      }
      Ty::Func(params, va, ret) => {
        let params = params
          .iter()
          .map(|(name, ty)| (*name, self.canonical_ty(ty)))
          .collect();
        Ty::Func(params, *va, Box::new(self.canonical_ty(ret)))
      }
      Ty::Ptr(is_mut, base) => {
        Ty::Ptr(*is_mut, Box::new(self.canonical_ty(base)))
      }
      Ty::Arr(size, elem) => {
        Ty::Arr(*size, Box::new(self.canonical_ty(elem)))
      }
      Ty::Unit => {
        Ty::Unit
      }
      Ty::Tuple(params) => {
        let params = params
          .iter()
          .map(|(name, ty)| (*name, self.canonical_ty(ty)))
          .collect();
        Ty::Tuple(params)
      }
      Ty::Var(idx) => {
        let (root, bound) = self.root(*idx);
        match bound {
          Bound::Is(ty) => self.canonical_ty(&ty),
                            _ => Ty::Var(root)
        }
      }
    }
  }


  /// Find the canonical form of a list of type expressions
  pub fn canonical_type_args(&mut self, type_args: &Vec<Ty>) -> Vec<Ty> {
    type_args.iter().map(|ty| self.canonical_ty(ty)).collect()
  }

  /// Find the final bound of a type expression
  pub fn final_ty(&mut self, ty: &Ty) -> Ty {
    match ty {
      Ty::Bool => Ty::Bool,
      Ty::Uint8 => Ty::Uint8,
      Ty::Int8 => Ty::Int8,
      Ty::Uint16 => Ty::Uint16,
      Ty::Int16 => Ty::Int16,
      Ty::Uint32 => Ty::Uint32,
      Ty::Int32 => Ty::Int32,
      Ty::Uint64 => Ty::Uint64,
      Ty::Int64 => Ty::Int64,
      Ty::Uintn => Ty::Uintn,
      Ty::Intn => Ty::Intn,
      Ty::Float => Ty::Float,
      Ty::Double => Ty::Double,
      Ty::StructRef(name, (def_id, type_args)) => {
        let type_args = type_args
          .iter()
          .map(|ty| self.final_ty(ty))
          .collect();
        Ty::StructRef(*name, (*def_id, type_args))
      }
      Ty::UnionRef(name, (def_id, type_args)) => {
        let type_args = type_args
          .iter()
          .map(|ty| self.final_ty(ty))
          .collect();
        Ty::UnionRef(*name, (*def_id, type_args))
      }
      Ty::EnumRef(name, (def_id, type_args)) => {
        let type_args = type_args
          .iter()
          .map(|ty| self.final_ty(ty))
          .collect();
        Ty::EnumRef(*name, (*def_id, type_args))
      }
      Ty::Func(params, va, ret) => {
        let params = params
          .iter()
          .map(|(name, ty)| (*name, self.final_ty(ty)))
          .collect();
        Ty::Func(params, *va, Box::new(self.final_ty(ret)))
      }
      Ty::Ptr(is_mut, base) => {
        Ty::Ptr(*is_mut, Box::new(self.final_ty(base)))
      }
      Ty::Arr(size, elem) => {
        Ty::Arr(*size, Box::new(self.final_ty(elem)))
      }
      Ty::Unit => {
        Ty::Unit
      }
      Ty::Tuple(params) => {
        let params = params
          .iter()
          .map(|(name, ty)| (*name, self.final_ty(ty)))
          .collect();
        Ty::Tuple(params)
      }
      Ty::Var(idx) => {
        let (_, bound) = self.root(*idx);
        match bound {
          Bound::Is(ty) => self.final_ty(&ty),
          Bound::Any => Ty::Unit,
          Bound::Num => Ty::Int32,
          Bound::Int => Ty::Int32,
          Bound::Flt => Ty::Float,
          Bound::Eq => Ty::Int32,
        }
      }
    }
  }

  /// Find the final bounds of a list of type expressions
  pub fn final_type_args(&mut self, type_args: &Vec<Ty>) -> Vec<Ty> {
    type_args.iter().map(|ty| self.final_ty(ty)).collect()
  }
}

impl fmt::Debug for TVarCtx {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write_comma_separated(f, self.tvars.iter().enumerate(), |f, (index, bound)| {
      write!(f, "'{}: {:?}", index, bound)
    })
  }
}

#[derive(Debug)]
enum CannotUnifyError {
  // Cannot unify two bounds
  Bounds(Bound, Bound),
  // Cannot unify two types
  Types(Ty, Ty),
  // Type does not have bound
  TypeDoesNotHaveBound(Ty, Bound)
}

impl fmt::Display for CannotUnifyError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      CannotUnifyError::Bounds(b1, b2) => {
        write!(f, "Incompatible type bounds {:?} and {:?}", b1, b2)
      }
      CannotUnifyError::Types(ty1, ty2) => {
        write!(f, "Cannot unify types {:?} and {:?}", ty1, ty2)
      }
      CannotUnifyError::TypeDoesNotHaveBound(ty, bound) => {
        write!(f, "Cannot bound type {:?} by {:?}", ty, bound)
      }
    }
  }
}

impl error::Error for CannotUnifyError {}