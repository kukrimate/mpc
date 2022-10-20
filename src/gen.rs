use crate::check::*;
use crate::util::*;
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

  /// Functions

  fn new_block(&mut self) -> LLVMBasicBlockRef {
    assert!(self.l_value != std::ptr::null_mut());
    unsafe { LLVMAppendBasicBlock(self.l_value, empty_cstr()) }
  }

  fn enter_block(&mut self, block: LLVMBasicBlockRef) {
    unsafe { LLVMPositionBuilderAtEnd(self.l_builder, block) }
  }

  pub fn begin_func(&mut self, name: RefStr, ty: Ty) {
    self.l_value = unsafe {
      LLVMAddFunction(self.l_module, name.borrow_c(), self.ty_to_llvm(ty))
    };
    let entry = self.new_block();
    self.enter_block(entry);
  }

  pub fn get_param(&mut self, index: usize) -> GenVal {
    GenVal(unsafe { LLVMGetParam(self.l_value, index as u32) })
  }

  pub fn alloca(&mut self, ty: Ty) -> GenVal {
    GenVal(unsafe { LLVMBuildAlloca(self.l_builder, self.ty_to_llvm(ty), empty_cstr()) })
  }

  pub fn store(&mut self, val: GenVal, ptr: GenVal) {
    unsafe { LLVMBuildStore(self.l_builder, val.0, ptr.0); }
  }

  pub fn end_func(&mut self) {
    self.l_value = std::ptr::null_mut();
  }

  /// Global variables

  pub fn begin_data(&mut self, name: RefStr, ty: Ty) {
    self.l_value = unsafe {
      LLVMAddGlobal(self.l_module, self.ty_to_llvm(ty), name.borrow_c())
    };
  }

  pub fn end_data(&mut self) {
    self.l_value = std::ptr::null_mut();
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
