// SPDX-License-Identifier: GPL-2.0-only

use super::*;
use llvm_sys::prelude::*;
use llvm_sys::core::*;

pub struct GenCtx {
  l_module: LLVMModuleRef,
  l_builder: LLVMBuilderRef,
  l_value: LLVMValueRef,
  l_block: LLVMBasicBlockRef,
}

#[derive(Clone,Copy)]
pub struct GenVal(LLVMValueRef);

impl GenCtx {
  pub fn new(module_id: RefStr) -> Self {
    GenCtx {
      l_module: unsafe { LLVMModuleCreateWithName(module_id.borrow_c()) },
      l_builder: unsafe { LLVMCreateBuilder() },
      l_value: std::ptr::null_mut(),
      l_block: std::ptr::null_mut(),
    }
  }

/*
  fn ty_to_llvm(&mut self, ty: Ty) -> LLVMTypeRef {
    unsafe {
      use TyS::*;
      match &*ty {
        Bool => LLVMInt1Type(),
        Uint8 | Int8 => LLVMInt8Type(),
        Uint16 | Int16 => LLVMInt16Type(),
        Uint32 | Int32 => LLVMInt32Type(),
        // FIXME: make the width of Uintn and Intn per target
        Uint64 | Int64 | Uintn | Intn => LLVMInt64Type(),
        Float => LLVMFloatType(),
        Double => LLVMDoubleType(),
        Fn(params, ret_ty) => {
          let mut l_params = vec![];
          for (name, ty) in params {
            l_params.push(self.ty_to_llvm(*ty));
          }
          let l_ret_ty = self.ty_to_llvm(*ret_ty);
          LLVMFunctionType(l_ret_ty,
                            l_params.get_unchecked_mut(0) as _,
                            l_params.len() as u32,
                            0)
        }
        Tuple(params) => {
          LLVMStructType(std::ptr::null_mut(), 0, 0)
        }
        _ => todo!(),
      }
    }
  }
*/

/*
  fn new_block(&mut self) -> LLVMBasicBlockRef {
    assert!(self.l_value != std::ptr::null_mut());
    unsafe { LLVMAppendBasicBlock(self.l_value, empty_cstr()) }
  }

  fn enter_block(&mut self, block: LLVMBasicBlockRef) {
    unsafe { LLVMPositionBuilderAtEnd(self.l_builder, block) }
  }
*/

  fn lower_def(&mut self) {
    // LLVMAddFunction(self.l_module, name.borrow_c(), self.ty_to_llvm(ty))
    // LLVMAddGlobal(self.l_module, self.ty_to_llvm(ty), name.borrow_c())
  }

  pub fn dump(&self) {
    unsafe { LLVMDumpModule(self.l_module) }
  }
}

impl Drop for GenCtx {
  fn drop(&mut self) {
    unsafe { LLVMDisposeModule(self.l_module) }
  }
}
