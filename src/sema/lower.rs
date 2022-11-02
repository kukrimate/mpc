// SPDX-License-Identifier: GPL-2.0-only

use super::*;
use llvm_sys::core::*;
use llvm_sys::target::*;

// Strings describing the target and data layout for LLVM
// These match AMD64 clang on Linux for now
const TRIPLE: &str = "x86_64-pc-linux-gnu";
const DATALAYOUT: &str = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128";

struct LowerCtx {
  l_context: LLVMContextRef,
  l_module: LLVMModuleRef,
  l_builder: LLVMBuilderRef,
  l_value: LLVMValueRef,
  l_block: LLVMBasicBlockRef,
}

impl LowerCtx {
  unsafe fn new(module_id: RefStr) -> Self {
    let l_context = LLVMGetGlobalContext();
    let l_module = LLVMModuleCreateWithNameInContext(module_id.borrow_c(),
                                                      l_context);
    LLVMSetTarget(l_module, RefStr::new(TRIPLE).borrow_c());
    LLVMSetDataLayout(l_module, RefStr::new(DATALAYOUT).borrow_c());
    let l_builder = LLVMCreateBuilderInContext(l_context);
    LowerCtx { l_context, l_module, l_builder,
        l_value: std::ptr::null_mut(), l_block: std::ptr::null_mut() }
  }

  unsafe fn align_of(&mut self, l_type: LLVMTypeRef) -> usize {
    let l_layout = LLVMGetModuleDataLayout(self.l_module);
    LLVMPreferredAlignmentOfType(l_layout, l_type) as usize
  }

  unsafe fn size_of(&mut self, l_type: LLVMTypeRef) -> usize {
    let l_layout = LLVMGetModuleDataLayout(self.l_module);
    LLVMStoreSizeOfType(l_layout, l_type) as usize
  }

  unsafe fn params_to_llvm(&mut self, params: &Vec<(RefStr, Ty)>) -> Vec<LLVMTypeRef> {
    let mut l_params = vec![];
    for (name, ty) in params {
      l_params.push(self.ty_to_llvm(ty));
    }
    l_params
  }

  unsafe fn ty_to_llvm(&mut self, ty: &Ty) -> LLVMTypeRef {
    use Ty::*;

    match ty {
      Bool => LLVMInt1TypeInContext(self.l_context),
      Uint8 | Int8 => LLVMInt8TypeInContext(self.l_context),
      Uint16 | Int16 => LLVMInt16TypeInContext(self.l_context),
      Uint32 | Int32 => LLVMInt32TypeInContext(self.l_context),
      Uint64 | Int64 => LLVMInt64TypeInContext(self.l_context),
      // FIXME: make the width of Uintn and Intn per target
      Uintn | Intn => LLVMInt64TypeInContext(self.l_context),
      Float => LLVMFloatTypeInContext(self.l_context),
      Double => LLVMDoubleTypeInContext(self.l_context),
      Ref(_, def) => {
        def.l_type
      }
      Fn(params, ret_ty) => {
        let mut l_params = self.params_to_llvm(params);
        LLVMFunctionType(self.ty_to_llvm(ret_ty),
          l_params.get_unchecked_mut(0) as _, l_params.len() as u32, 0)
      }
      Ptr(_, base_ty) => {
        LLVMPointerType(self.ty_to_llvm(base_ty), 0)
      }
      Arr(siz, elem_ty) => {
        LLVMArrayType(self.ty_to_llvm(elem_ty), *siz as u32)
      }
      Tuple(params) => {
        let mut l_params = self.params_to_llvm(params);
        LLVMStructTypeInContext(self.l_context,
          l_params.get_unchecked_mut(0) as _, l_params.len() as u32, 0)
      }
      ClassAny | ClassNum | ClassInt => {
        // FIXME: make sure this never happens
        panic!("Error: non-deduced type reached lowering")
      }
    }
  }

  unsafe fn lower_ty_defs(&mut self, ty_defs: &mut IndexMap<RefStr, Own<TyDef>>) {
    // Create named LLVM structure for each type definition
    for (name, ty_def) in ty_defs.iter_mut() {
      ty_def.l_type = LLVMStructCreateNamed(self.l_context, name.borrow_c());
    }
    // Resolve bodies in a second pass (types might be out of order and mutually recursive)
    for (name, ty_def) in ty_defs.iter_mut() {
      let mut l_params = match &ty_def.kind {
        TyDefKind::ToBeFilled => unreachable!(),
        TyDefKind::Struct(params) => {
          // This is the simplest case, LLVM has native support for structures
          self.params_to_llvm(params)
        }
        TyDefKind::Union(params) => {
          // The union lowering code is shared with enums thus it's in 'lower_union'
          let l_params = self.params_to_llvm(params);
          self.lower_union(l_params)
        }
        TyDefKind::Enum(variants) => {
          // Enum lowering is done by adding a discriminant (always a dword for now)
          // Followed by the variants lowered as if they were parameters of a union

          // Convert struct-like variants into LLVM types
          let mut l_variant_types = vec![];
          for (_, variant) in variants {
            match variant {
              Variant::Unit(_) => (),
              Variant::Struct(_, params) => {
                let mut l_params = self.params_to_llvm(params);
                l_variant_types.push(LLVMStructTypeInContext(self.l_context,
                  l_params.get_unchecked_mut(0) as _, l_params.len() as u32, 0));
              }
            }
          }

          // Create actual enum parameters
          let mut l_params = vec![ LLVMInt32TypeInContext(self.l_context) ];
          l_params.extend(self.lower_union(l_variant_types));
          l_params
        }
      };
      // Resolve body
      LLVMStructSetBody(ty_def.l_type,
        l_params.get_unchecked_mut(0) as _, l_params.len() as u32, 0);
    }
  }

  unsafe fn lower_union(&mut self, l_params: Vec<LLVMTypeRef>) -> Vec<LLVMTypeRef> {
    // Union lowering is done clang style, we take the highest alignment
    // element, and pad it to have the expected size of the union
    let mut union_align = 0;
    let mut union_size = 0;
    let mut l_max_align_type = std::ptr::null_mut();
    for l_param in l_params {
      if self.align_of(l_param) > union_align {
        union_align = self.align_of(l_param);
        l_max_align_type = l_param;
      }
      if self.size_of(l_param) > union_size {
        union_size = self.size_of(l_param);
      }
    }

    // Start with the highest alignment type then add byte array with
    // the length of the required padding
    let mut l_params = vec![ l_max_align_type ];
    let padding_size = union_size - self.size_of(l_max_align_type);
    if padding_size > 0 {
      l_params.push(LLVMArrayType(
        LLVMInt8TypeInContext(self.l_context), padding_size as u32));
    }
    l_params
  }

/*
  fn new_block(&mut self) -> LLVMBasicBlockRef {
    assert!(self.l_value != std::ptr::null_mut());
    unsafe { LLVMAppendBasicBlock(self.l_value, empty_cstr()) }
  }

  fn enter_block(&mut self, block: LLVMBasicBlockRef) {
    unsafe { LLVMPositionBuilderAtEnd(self.l_builder, block) }
  }
*/

  // LLVMAddFunction(self.l_module, name.borrow_c(), self.ty_to_llvm(ty))
  // LLVMAddGlobal(self.l_module, self.ty_to_llvm(ty), name.borrow_c())

  unsafe fn lower_defs(&mut self, defs: &mut IndexMap<RefStr, Own<Def>>) {
    for (name, def) in defs {
      match &def.kind {
        DefKind::Data(_) | DefKind::ExternData => {
          LLVMAddGlobal(
            self.l_module,
            self.ty_to_llvm(&def.ty),
            name.borrow_c());
        }
        _ => ()
      }
    }
  }

  unsafe fn lower_module(&mut self, module: &mut Module) {
    self.lower_ty_defs(&mut module.ty_defs);
    self.lower_defs(&mut module.defs[0]);
  }

  unsafe fn dump(&self) {
    LLVMDumpModule(self.l_module)
  }
}

impl Drop for LowerCtx {
  fn drop(&mut self) {
    unsafe { LLVMDisposeModule(self.l_module) }
  }
}

pub fn lower_module(module: &mut Module) -> MRes<()> {
  unsafe {
    let mut ctx = LowerCtx::new(RefStr::new(""));
    ctx.lower_module(module);
    ctx.dump();
    Ok(())
  }
}
