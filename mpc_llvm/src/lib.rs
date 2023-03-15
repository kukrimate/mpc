/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

//
// LLVM wrapper
//
// This file provides a Rust-esque wrapper for the subset of llvm-sys
// used by MPC.
//


use llvm_sys::*;
use llvm_sys::core::*;
use llvm_sys::prelude::*;
use llvm_sys::target::*;
use llvm_sys::target_machine::*;
pub use llvm_sys::{LLVMIntPredicate::*,
                   LLVMRealPredicate::*};

use std::ffi::{c_char, CString};
use std::io;
use std::marker::PhantomData;
use std::path::Path;

pub struct Target {
  l_machine: LLVMTargetMachineRef,
  l_layout: LLVMTargetDataRef,
  l_triple: *mut c_char,
  l_layout_str: *mut c_char
}

pub struct Context {
  l_context: LLVMContextRef,
}

#[repr(transparent)]
pub struct Builder<'ctx> {
  l_builder: LLVMBuilderRef,
  lifetime: PhantomData<&'ctx Context>,
}

#[repr(transparent)]
pub struct Module<'ctx> {
  l_module: LLVMModuleRef,
  lifetime: PhantomData<&'ctx Context>,
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Type<'ctx> {
  l_type: LLVMTypeRef,
  lifetime: PhantomData<&'ctx Context>,
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Block<'ctx> {
  l_block: LLVMBasicBlockRef,
  lifetime: PhantomData<&'ctx Context>,
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Value<'ctx> {
  l_value: LLVMValueRef,
  lifetime: PhantomData<&'ctx Context>,
}

impl Drop for Target {
  fn drop(&mut self) {
    unsafe {
      LLVMDisposeTargetMachine(self.l_machine);
      LLVMDisposeTargetData(self.l_layout);
      LLVMDisposeMessage(self.l_triple);
      LLVMDisposeMessage(self.l_layout_str);
    }
  }
}

impl Drop for Context {
  fn drop(&mut self) {
    unsafe {
      LLVMContextDispose(self.l_context)
    }
  }
}

impl<'ctx> Drop for Module<'ctx> {
  fn drop(&mut self) {
    unsafe {
      LLVMDisposeModule(self.l_module)
    }
  }
}


impl<'ctx> Drop for Builder<'ctx> {
  fn drop(&mut self) {
    unsafe {
      LLVMDisposeBuilder(self.l_builder)
    }
  }
}

impl Target {
  pub fn native() -> Target {
    unsafe {
      LLVM_InitializeAllTargetInfos();
      LLVM_InitializeAllTargets();
      LLVM_InitializeAllTargetMCs();
      LLVM_InitializeAllAsmParsers();
      LLVM_InitializeAllAsmPrinters();

      let l_triple = LLVMGetDefaultTargetTriple();
      let l_cpu_name = LLVMGetHostCPUName();
      let l_cpu_features = LLVMGetHostCPUFeatures();

      let mut l_target = std::ptr::null_mut();
      let mut l_errors = std::ptr::null_mut();
      LLVMGetTargetFromTriple(l_triple, &mut l_target, &mut l_errors);
      assert!(l_errors.is_null());

      let l_machine = LLVMCreateTargetMachine(
        l_target,
        l_triple,
        l_cpu_name,
        l_cpu_features,
        LLVMCodeGenOptLevel::LLVMCodeGenLevelDefault,
        LLVMRelocMode::LLVMRelocPIC,
        LLVMCodeModel::LLVMCodeModelDefault);

      LLVMDisposeMessage(l_cpu_name);
      LLVMDisposeMessage(l_cpu_features);

      let l_layout = LLVMCreateTargetDataLayout(l_machine);
      let l_layout_str = LLVMCopyStringRepOfTargetData(l_layout);

      Target {
        l_machine,
        l_layout,
        l_triple,
        l_layout_str
      }
    }
  }

  pub fn from_triplet(triple: &str) -> Option<Target> {
    unsafe {
      LLVM_InitializeAllTargetInfos();
      LLVM_InitializeAllTargets();
      LLVM_InitializeAllTargetMCs();
      LLVM_InitializeAllAsmParsers();
      LLVM_InitializeAllAsmPrinters();


      let c_triple = CString::new(triple).unwrap();
      let l_triple = LLVMCreateMessage(c_triple.as_ptr());

      let mut l_target = std::ptr::null_mut();
      let mut l_errors = std::ptr::null_mut();
      LLVMGetTargetFromTriple(l_triple, &mut l_target, &mut l_errors);
      if !l_errors.is_null() { return None }

      let l_machine = LLVMCreateTargetMachine(
        l_target,
        l_triple,
        empty_cstr(),
        empty_cstr(),
        LLVMCodeGenOptLevel::LLVMCodeGenLevelDefault,
        LLVMRelocMode::LLVMRelocPIC,
        LLVMCodeModel::LLVMCodeModelDefault);

      let l_layout = LLVMCreateTargetDataLayout(l_machine);
      let l_layout_str = LLVMCopyStringRepOfTargetData(l_layout);

      Some(Target {
        l_machine,
        l_layout,
        l_triple,
        l_layout_str
      })
    }
  }

  pub fn align_of(&mut self, ty: Type<'_>) -> usize {
    unsafe {
      LLVMPreferredAlignmentOfType(self.l_layout, ty.l_type) as _
    }
  }

  pub fn size_of(&mut self, ty: Type<'_>) -> usize {
    unsafe {
      LLVMStoreSizeOfType(self.l_layout, ty.l_type) as _
    }
  }

  pub fn write_llvm_ir(&self, module: Module<'_>, path: &Path) -> Result<(), io::Error> {
    unsafe {
      // Create string representation of module
      let module_str = LLVMPrintModuleToString(module.l_module);

      // Write string to file
      let data: &[u8] = std::slice::from_raw_parts(
        module_str as *const u8,
        c_strlen(module_str));
      std::fs::write(path, data)?;

      // Free string
      LLVMDisposeMessage(module_str);

      // We are okay
      Ok(())
    }
  }

  pub fn write_machine_code(&self, module: Module<'_>, textual: bool, path: &Path) -> Result<(), io::Error> {
    unsafe {
      let file_type = if textual {
        LLVMCodeGenFileType::LLVMAssemblyFile
      } else {
        LLVMCodeGenFileType::LLVMObjectFile
      };

      let mut errors = std::ptr::null_mut();
      let mut buffer = std::ptr::null_mut();

      // Ask LLVM put the data into a buffer for us
      LLVMTargetMachineEmitToMemoryBuffer(
        self.l_machine,
        module.l_module,
        file_type,
        &mut errors,
        &mut buffer);

      // NOTE: Generating un-compilable IR is considered a bug
      assert!(errors.is_null());

      // Write the data from above to the output file
      let data: &[u8] = std::slice::from_raw_parts(
        LLVMGetBufferStart(buffer) as *const u8,
        LLVMGetBufferSize(buffer));
      std::fs::write(path, data)?;

      // Free buffer
      LLVMDisposeMemoryBuffer(buffer);

      // We are all okay
      Ok(())
    }
  }
}

impl<'ctx> Context {
  pub fn new() -> Context {
    unsafe {
      Context {
        l_context: LLVMContextCreate()
      }
    }
  }

  pub fn builder(&'ctx self) -> Builder<'ctx> {
    unsafe {
      Builder {
        l_builder: LLVMCreateBuilderInContext(self.l_context),
        lifetime: PhantomData
      }
    }
  }

  pub fn module(&'ctx self, name: *const c_char) -> Module<'ctx> {
    unsafe {
      Module {
        l_module: LLVMModuleCreateWithNameInContext(name,
                                                    self.l_context),
        lifetime: PhantomData
      }
    }
  }

  pub fn ty_void(&'ctx self) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMVoidTypeInContext(self.l_context),
        lifetime: PhantomData
      }
    }
  }

  pub fn ty_int1(&'ctx self) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMInt1TypeInContext(self.l_context),
        lifetime: PhantomData
      }
    }
  }

  pub fn ty_int8(&'ctx self) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMInt8TypeInContext(self.l_context),
        lifetime: PhantomData
      }
    }
  }

  pub fn ty_int16(&'ctx self) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMInt16TypeInContext(self.l_context),
        lifetime: PhantomData
      }
    }
  }

  pub fn ty_int32(&'ctx self) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMInt32TypeInContext(self.l_context),
        lifetime: PhantomData
      }
    }
  }

  pub fn ty_int64(&'ctx self) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMInt64TypeInContext(self.l_context),
        lifetime: PhantomData
      }
    }
  }

  pub fn ty_float(&'ctx self) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMFloatTypeInContext(self.l_context),
        lifetime: PhantomData
      }
    }
  }

  pub fn ty_double(&'ctx self) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMDoubleTypeInContext(self.l_context),
        lifetime: PhantomData
      }
    }
  }

  pub fn ty_ptr(&'ctx self) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMPointerTypeInContext(self.l_context, 0),
        lifetime: PhantomData
      }
    }
  }

  pub fn ty_array(&'ctx self, element: Type<'ctx>, count: usize) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMArrayType(element.l_type, count as _),
        lifetime: PhantomData
      }
    }
  }

  pub fn ty_struct(&'ctx self, fields: &[Type<'ctx>]) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMStructTypeInContext(self.l_context,
                                        fields.as_ptr() as _,
                                        fields.len() as _,
                                        0),
        lifetime: PhantomData
      }
    }
  }

  pub fn ty_function(&'ctx self, ret: Type<'ctx>, params: &[Type<'ctx>], va: bool) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMFunctionType(ret.l_type,
                                 params.as_ptr() as _,
                                 params.len() as _,
                                 va as _),
        lifetime: PhantomData
      }
    }
  }

  pub fn const_zeroed(&'ctx self, ty: Type<'ctx>) -> Value<'ctx> {
    unsafe {
      Value {
        l_value: LLVMConstNull(ty.l_type),
        lifetime: PhantomData
      }
    }
  }

  pub fn const_int(&'ctx self, ty: Type<'ctx>, val: usize) -> Value<'ctx> {
    assert!(ty.is_int());

    unsafe {
      Value {
        l_value: LLVMConstInt(ty.l_type, val as _, 0),
        lifetime: PhantomData
      }
    }
  }

  pub fn const_flt(&'ctx self, ty: Type<'ctx>, val: f64) -> Value<'ctx> {
    assert!(ty.is_flt());

    unsafe {
      Value {
        l_value: LLVMConstReal(ty.l_type, val),
        lifetime: PhantomData
      }
    }
  }

  pub fn const_gep(&'ctx self, ty: Type<'ctx>, base: Value<'ctx>, indices: &[Value<'ctx>]) -> Value<'ctx> {
    unsafe {
      assert_eq!(LLVMIsConstant(base.l_value), 1);
      indices.iter().for_each(|x| assert_eq!(LLVMIsConstant(x.l_value), 1));
      Value {
        l_value: LLVMConstInBoundsGEP2(ty.l_type,
                                       base.l_value,
                                       indices.as_ptr() as _,
                                       indices.len() as _),
        lifetime: PhantomData
      }
    }
  }

  pub fn const_null_terminated_string(&'ctx self, data: &[u8]) -> Value<'ctx> {
    unsafe {
      Value {
        l_value: LLVMConstStringInContext(self.l_context,
                                          data.as_ptr() as _,
                                          data.len() as _,
                                          0),
        lifetime: PhantomData
      }

    }
  }

  pub fn const_struct(&'ctx self, fields: &[Value<'ctx>]) -> Value<'ctx> {
    unsafe {
      fields.iter().for_each(|x| assert_eq!(LLVMIsConstant(x.l_value), 1));
      Value {
        l_value: LLVMConstStructInContext(self.l_context,
                                          fields.as_ptr() as _,
                                          fields.len() as _,
                                          0),
        lifetime: PhantomData
      }
    }
  }
}

impl<'ctx> Builder<'ctx> {
  pub fn get_block(&self) -> Option<Block<'ctx>> {
    unsafe {
      let ptr = LLVMGetInsertBlock(self.l_builder);
      if ptr.is_null() {
        None
      } else {
        Some(Block {
          l_block: LLVMGetInsertBlock(self.l_builder),
          lifetime: PhantomData
        })
      }
    }
  }

  pub fn set_block(&self, block: Block<'ctx>) {
    unsafe {
      LLVMPositionBuilderAtEnd(self.l_builder, block.l_block)
    }
  }

  pub fn alloca(&self, ty: Type<'ctx>) -> Value<'ctx> {
    unsafe {
      Value {
        l_value: LLVMBuildAlloca(self.l_builder,
                                 ty.l_type,
                                 empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn gep(&self, ty: Type<'ctx>, base: Value<'ctx>, indices: &[Value<'ctx>]) -> Value<'ctx> {
    unsafe {
      Value {
        l_value: LLVMBuildGEP2(self.l_builder,
                               ty.l_type,
                               base.l_value,
                               indices.as_ptr() as _,
                               indices.len() as _,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn load(&self, ty: Type<'ctx>, ptr: Value<'ctx>) -> Value<'ctx> {
    assert!(ptr.ty().is_ptr());

    unsafe {
      Value {
        l_value: LLVMBuildLoad2(self.l_builder,
                                ty.l_type,
                                ptr.l_value,
                                empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn store(&self, ptr: Value<'ctx>, val: Value<'ctx>) {
    assert!(ptr.ty().is_ptr());

    unsafe {
      LLVMBuildStore(self.l_builder,
                     val.l_value,
                     ptr.l_value);
    }
  }

  pub fn memcpy(&self, dest: Value<'ctx>, src: Value<'ctx>, align: usize, size: Value<'ctx>) {
    assert!(dest.ty().is_ptr());
    assert!(src.ty().is_ptr());

    unsafe {
      LLVMBuildMemCpy(self.l_builder,
                      dest.l_value,
                      align as _,
                      src.l_value,
                      align as _,
                      size.l_value);
    }
  }

  pub fn call(&self, func_ty: Type<'ctx>, func_ptr: Value<'ctx>, args: &[Value<'ctx>]) -> Value<'ctx> {
    assert!(func_ty.is_function());
    assert!(func_ptr.ty().is_ptr());

    unsafe {
      Value {
        l_value: LLVMBuildCall2(self.l_builder,
                                func_ty.l_type,
                                func_ptr.l_value,
                                args.as_ptr() as _,
                                args.len() as _,
                                empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn neg(&self, val: Value<'ctx>) -> Value<'ctx> {
    assert!(val.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildNeg(self.l_builder,
                              val.l_value,
                              empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn not(&self, val: Value<'ctx>) -> Value<'ctx> {
    assert!(val.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildNot(self.l_builder,
                              val.l_value,
                              empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn add(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildAdd(self.l_builder,
                              lhs.l_value,
                              rhs.l_value,
                              empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn sub(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildSub(self.l_builder,
                              lhs.l_value,
                              rhs.l_value,
                              empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn mul(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildMul(self.l_builder,
                              lhs.l_value,
                              rhs.l_value,
                              empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn udiv(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildUDiv(self.l_builder,
                               lhs.l_value,
                               rhs.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn sdiv(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildSDiv(self.l_builder,
                               lhs.l_value,
                               rhs.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn urem(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildURem(self.l_builder,
                               lhs.l_value,
                               rhs.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn srem(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildSRem(self.l_builder,
                               lhs.l_value,
                               rhs.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn shl(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildShl(self.l_builder,
                              lhs.l_value,
                              rhs.l_value,
                              empty_cstr()),
        lifetime: PhantomData
      }
    }
  }


  pub fn lshr(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildLShr(self.l_builder,
                               lhs.l_value,
                               rhs.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn ashr(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildAShr(self.l_builder,
                               lhs.l_value,
                               rhs.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn and(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildAnd(self.l_builder,
                              lhs.l_value,
                              rhs.l_value,
                              empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn or(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildOr(self.l_builder,
                             lhs.l_value,
                             rhs.l_value,
                             empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn xor(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildXor(self.l_builder,
                              lhs.l_value,
                              rhs.l_value,
                              empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn icmp(&self, pred: LLVMIntPredicate, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_int());
    assert!(rhs.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildICmp(self.l_builder,
                               pred,
                               lhs.l_value,
                               rhs.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn fneg(&self, val: Value<'ctx>) -> Value<'ctx> {
    assert!(val.ty().is_flt());

    unsafe {
      Value {
        l_value: LLVMBuildFNeg(self.l_builder,
                               val.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn fadd(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_flt());
    assert!(rhs.ty().is_flt());

    unsafe {
      Value {
        l_value: LLVMBuildFAdd(self.l_builder,
                               lhs.l_value,
                               rhs.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn fsub(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_flt());
    assert!(rhs.ty().is_flt());

    unsafe {
      Value {
        l_value: LLVMBuildFSub(self.l_builder,
                               lhs.l_value,
                               rhs.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn fmul(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_flt());
    assert!(rhs.ty().is_flt());

    unsafe {
      Value {
        l_value: LLVMBuildFMul(self.l_builder,
                               lhs.l_value,
                               rhs.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn fdiv(&self, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_flt());
    assert!(rhs.ty().is_flt());

    unsafe {
      Value {
        l_value: LLVMBuildFDiv(self.l_builder,
                               lhs.l_value,
                               rhs.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn fcmp(&self, pred: LLVMRealPredicate, lhs: Value<'ctx>, rhs: Value<'ctx>) -> Value<'ctx> {
    assert!(lhs.ty().is_flt());
    assert!(rhs.ty().is_flt());

    unsafe {
      Value {
        l_value: LLVMBuildFCmp(self.l_builder,
                               pred,
                               lhs.l_value,
                               rhs.l_value,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }


  pub fn int_to_ptr(&self, dest_ty: Type<'ctx>, val: Value<'ctx>) -> Value<'ctx> {
    assert!(dest_ty.is_ptr());
    assert!(val.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildIntToPtr(self.l_builder,
                                   val.l_value,
                                   dest_ty.l_type,
                                   empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn ptr_to_int(&self, dest_ty: Type<'ctx>, val: Value<'ctx>) -> Value<'ctx> {
    assert!(dest_ty.is_int());
    assert!(val.ty().is_ptr());

    unsafe {
      Value {
        l_value: LLVMBuildPtrToInt(self.l_builder,
                                   val.l_value,
                                   dest_ty.l_type,
                                   empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn trunc(&self, dest_ty: Type<'ctx>, val: Value<'ctx>) -> Value<'ctx> {
    assert!(dest_ty.is_int());
    assert!(val.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildTrunc(self.l_builder,
                                val.l_value,
                                dest_ty.l_type,
                                empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn zext(&self, dest_ty: Type<'ctx>, val: Value<'ctx>) -> Value<'ctx> {
    assert!(dest_ty.is_int());
    assert!(val.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildZExt(self.l_builder,
                               val.l_value,
                               dest_ty.l_type,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn sext(&self, dest_ty: Type<'ctx>, val: Value<'ctx>) -> Value<'ctx> {
    assert!(dest_ty.is_int());
    assert!(val.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildSExt(self.l_builder,
                               val.l_value,
                               dest_ty.l_type,
                               empty_cstr()),
        lifetime: PhantomData
      }
    }
  }


  pub fn fp_trunc(&self, dest_ty: Type<'ctx>, val: Value<'ctx>) -> Value<'ctx> {
    assert!(dest_ty.is_flt());
    assert!(val.ty().is_flt());

    unsafe {
      Value {
        l_value: LLVMBuildFPTrunc(self.l_builder,
                                  val.l_value,
                                  dest_ty.l_type,
                                  empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn fp_ext(&self, dest_ty: Type<'ctx>, val: Value<'ctx>) -> Value<'ctx> {
    assert!(dest_ty.is_flt());
    assert!(val.ty().is_flt());

    unsafe {
      Value {
        l_value: LLVMBuildFPExt(self.l_builder,
                                val.l_value,
                                dest_ty.l_type,
                                empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn fp_to_ui(&self, dest_ty: Type<'ctx>, val: Value<'ctx>) -> Value<'ctx> {
    assert!(dest_ty.is_int());
    assert!(val.ty().is_flt());

    unsafe {
      Value {
        l_value: LLVMBuildFPToUI(self.l_builder,
                                 val.l_value,
                                 dest_ty.l_type,
                                 empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn fp_to_si(&self, dest_ty: Type<'ctx>, val: Value<'ctx>) -> Value<'ctx> {
    assert!(dest_ty.is_int());
    assert!(val.ty().is_flt());

    unsafe {
      Value {
        l_value: LLVMBuildFPToSI(self.l_builder,
                                 val.l_value,
                                 dest_ty.l_type,
                                 empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn ui_to_fp(&self, dest_ty: Type<'ctx>, val: Value<'ctx>) -> Value<'ctx> {
    assert!(dest_ty.is_flt());
    assert!(val.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildUIToFP(self.l_builder,
                                 val.l_value,
                                 dest_ty.l_type,
                                 empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn si_to_fp(&self, dest_ty: Type<'ctx>, val: Value<'ctx>) -> Value<'ctx> {
    assert!(dest_ty.is_flt());
    assert!(val.ty().is_int());

    unsafe {
      Value {
        l_value: LLVMBuildSIToFP(self.l_builder,
                                 val.l_value,
                                 dest_ty.l_type,
                                 empty_cstr()),
        lifetime: PhantomData
      }
    }
  }

  pub fn phi(&self, ty: Type<'ctx>, values: &[Value<'ctx>], blocks: &[Block<'ctx>]) -> Value<'ctx> {
    // Each value must have the result's type
    values.iter().for_each(|x| assert_eq!(ty.l_type, x.ty().l_type));
    // Must have the same number of blocks and values
    assert_eq!(values.len(), blocks.len());

    unsafe {
      let l_phi = LLVMBuildPhi(self.l_builder, ty.l_type, empty_cstr());
      LLVMAddIncoming(l_phi,
                      values.as_ptr() as _,
                      blocks.as_ptr() as _,
                      values.len() as _);
      Value {
        l_value: l_phi,
        lifetime: PhantomData
      }
    }
  }

  pub fn br(&self, dest: Block<'ctx>) {
    unsafe {
      LLVMBuildBr(self.l_builder, dest.l_block);
    }
  }

  pub fn cond_br(&self, cond: Value<'ctx>, true_dest: Block<'ctx>, false_dest: Block<'ctx>) {
    unsafe {
      LLVMBuildCondBr(self.l_builder,
                      cond.l_value,
                      true_dest.l_block,
                      false_dest.l_block);
    }
  }

  pub fn ret(&self, val: Value<'ctx>) {
    unsafe {
      LLVMBuildRet(self.l_builder, val.l_value);
    }
  }

  pub fn ret_void(&self) {
    unsafe {
      LLVMBuildRetVoid(self.l_builder);
    }
  }

  pub fn switch(&self, ctrl: Value<'ctx>,
                cases: &[(Value<'ctx>, Block<'ctx>)],
                default: Block<'ctx>) {
    unsafe {
      let l_switch = LLVMBuildSwitch(self.l_builder,
                                     ctrl.l_value,
                                     default.l_block,
                                     cases.len() as _);
      for (on_val, block) in cases.iter() {
        LLVMAddCase(l_switch, on_val.l_value, block.l_block);
      }
    }
  }
}

impl<'ctx> Module<'ctx> {
  pub fn set_target(&self, target: &Target) {
    unsafe {
      LLVMSetTarget(self.l_module, target.l_triple);
      LLVMSetDataLayout(self.l_module, target.l_layout_str);
    }
  }

  pub fn add_global(&self, name: *const c_char, ty: Type<'ctx>) -> Value<'ctx> {
    unsafe {
      Value {
        l_value: LLVMAddGlobal(self.l_module, ty.l_type, name),
        lifetime: PhantomData
      }
    }
  }

  pub fn add_function(&self, name: *const c_char, ty: Type<'ctx>) -> Value<'ctx> {
    assert!(ty.is_function());

    unsafe {
      Value {
        l_value: LLVMAddFunction(self.l_module, name, ty.l_type),
        lifetime: PhantomData
      }
    }
  }

  pub fn dump(&self) {
    unsafe {
      LLVMDumpModule(self.l_module);
    }
  }
}

impl<'ctx> Type<'ctx> {
  fn is_int(&self) -> bool {
    unsafe {
      LLVMGetTypeKind(self.l_type) == LLVMTypeKind::LLVMIntegerTypeKind
    }
  }

  fn is_flt(&self) -> bool {
    unsafe {
      LLVMGetTypeKind(self.l_type) == LLVMTypeKind::LLVMFloatTypeKind
        || LLVMGetTypeKind(self.l_type) == LLVMTypeKind::LLVMDoubleTypeKind
    }
  }

  fn is_ptr(&self) -> bool {
    unsafe {
      LLVMGetTypeKind(self.l_type) == LLVMTypeKind::LLVMPointerTypeKind
    }
  }

  fn is_function(&self) -> bool {
    unsafe {
      LLVMGetTypeKind(self.l_type) == LLVMTypeKind::LLVMFunctionTypeKind
    }
  }
}

impl<'ctx> Value<'ctx> {
  pub fn ty(&self) -> Type<'ctx> {
    unsafe {
      Type {
        l_type: LLVMTypeOf(self.l_value),
        lifetime: PhantomData
      }
    }
  }

  pub fn set_initializer(&self, init: Value<'ctx>) {
    unsafe {
      assert!(!LLVMIsAGlobalVariable(self.l_value).is_null());
      assert!(!LLVMIsAConstant(init.l_value).is_null());
      assert_eq!(LLVMGlobalGetValueType(self.l_value), LLVMTypeOf(init.l_value));
      LLVMSetInitializer(self.l_value, init.l_value);
    }
  }

  pub fn get_param(&self, index: usize) -> Value<'ctx> {
    unsafe {
      assert!(!LLVMIsAFunction(self.l_value).is_null());
      Value {
        l_value: LLVMGetParam(self.l_value, index as _),
        lifetime: PhantomData
      }
    }
  }

  pub fn add_block(&self) -> Block<'ctx> {
    unsafe {
      assert!(!LLVMIsAFunction(self.l_value).is_null());
      Block {
        l_block: LLVMAppendBasicBlock(self.l_value, empty_cstr()),
        lifetime: PhantomData
      }
    }
  }
}

/// Empty NUL-terminated C string
fn empty_cstr() -> *mut c_char {
  b"\0".as_ptr() as _
}

/// Calculate the length of a C-style string (in bytes)
unsafe fn c_strlen(s: *const c_char) -> usize {
  let mut end = s;
  while end.read() != 0 {
    end = end.add(1);
  }
  end.offset_from(s) as _
}
