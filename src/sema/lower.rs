// SPDX-License-Identifier: GPL-2.0-only

use super::*;
use llvm_sys::core::*;
use llvm_sys::LLVMIntPredicate::*;
use llvm_sys::LLVMRealPredicate::*;
use llvm_sys::prelude::*;
use llvm_sys::target::*;
use llvm_sys::target_machine::*;

type BB = LLVMBasicBlockRef;
type Val = LLVMValueRef;

/// Constant expressions

unsafe fn lower_const_lvalue(lvalue: &LValue, ctx: &mut LowerCtx) -> Val {
  match lvalue {
    LValue::DataRef { def, .. } => {
      *ctx.values.get(def).unwrap()
    }
    LValue::Str { val, .. } => {
      ctx.build_string_lit(*val)
    }
    LValue::Dot { arg, idx, .. } => {
      let addr = lower_const_lvalue(arg, ctx);
      ctx.build_const_dot(addr, *idx)
    }
    LValue::Index { arg, idx, .. } => {
      let addr = lower_const_lvalue(arg, ctx);
      let idx = lower_const_rvalue(idx, ctx);
      ctx.build_const_index(addr, idx)
    }
    LValue::Ind { arg, .. } => {
      lower_const_rvalue(arg, ctx)
    }
  }
}

unsafe fn lower_const_rvalue(rvalue: &RValue, ctx: &mut LowerCtx) -> Val {
  match rvalue {
    RValue::Null { .. } => {
      ctx.build_void()
    }
    RValue::ConstRef { def, .. } => {
      *ctx.values.get(def).unwrap()
    }
    RValue::FuncRef { def, .. } => {
      *ctx.values.get(def).unwrap()
    }
    RValue::Bool { val, .. } => {
      ctx.build_bool(*val)
    }
    RValue::Int { ty, val, .. } => {
      ctx.build_int(ty, *val)
    }
    RValue::Flt { ty, val, .. } => {
      ctx.build_flt(ty, *val)
    }
    RValue::Char { .. } => {
      todo!() // TODO
    }
    RValue::Adr { arg, .. } => {
      lower_const_lvalue(arg, ctx)
    }
    RValue::Un { op, arg, .. } => {
      let l_arg = lower_const_rvalue(arg, ctx);
      ctx.build_const_un(arg.ty(), *op, l_arg)
    }
    RValue::LNot { arg, .. } => {
      let arg = lower_const_rvalue(arg, ctx);
      ctx.build_const_lnot(arg)
    }
    RValue::Cast { .. } => {
      todo!()
    }
    RValue::Bin { op, lhs, rhs, .. } => {
      let l_lhs = lower_const_rvalue(lhs, ctx);
      let l_rhs = lower_const_rvalue(rhs, ctx);
      ctx.build_const_bin(lhs.ty(), *op, l_lhs, l_rhs)
    }
    RValue::LAnd { .. } => {
      todo!() // TODO
    }
    RValue::LOr { .. } => {
      todo!() // TODO
    }
    RValue::If { .. } => {
      todo!() // TODO
    }
    _ => {
      unreachable!()
    }
  }
}

/// Runtime expressions

unsafe fn lower_lvalue(lvalue: &LValue, ctx: &mut LowerCtx) -> Val {
  match lvalue {
    LValue::DataRef { def, .. } => {
      *ctx.values.get(def).unwrap()
    }
    LValue::Str { val, .. } => {
      ctx.build_string_lit(*val)
    }
    LValue::Dot { arg, idx, .. } => {
      let addr = lower_lvalue(arg, ctx);
      ctx.build_dot(addr, *idx)
    }
    LValue::Index { arg, idx, .. } => {
      let addr = lower_lvalue(arg, ctx);
      let idx = lower_rvalue(idx, ctx);
      ctx.build_index(addr, idx)
    }
    LValue::Ind { arg, .. } => {
      lower_rvalue(arg, ctx)
    }
  }
}

unsafe fn lower_rvalue(rvalue: &RValue, ctx: &mut LowerCtx) -> Val {
  match rvalue {
    RValue::Null { .. } => {
      ctx.build_void()
    }
    RValue::ConstRef { def, .. } => {
      *ctx.values.get(def).unwrap()
    }
    RValue::FuncRef { def, .. } => {
      *ctx.values.get(def).unwrap()
    }
    RValue::Load { ty, arg, .. } => {
      let addr = lower_lvalue(arg, ctx);
      ctx.build_load(ty, addr)
    }
    RValue::Bool { val, .. } => {
      ctx.build_bool(*val)
    }
    RValue::Int { ty, val, .. } => {
      ctx.build_int(ty, *val)
    }
    RValue::Flt { ty, val, .. } => {
      ctx.build_flt(ty, *val)
    }
    RValue::Char { .. } => {
      todo!() // TODO
    }
    RValue::Call { arg, args, .. } => {
      let arg = lower_rvalue(arg, ctx);
      let args = args.iter()
        .map(|(_, arg)| lower_rvalue(arg, ctx))
        .collect();
      ctx.build_call(arg, args)
    }
    RValue::Adr { arg, .. } => {
      lower_lvalue(arg, ctx)
    }
    RValue::Un { op, arg, .. } => {
      let l_arg = lower_rvalue(arg, ctx);
      ctx.build_un(arg.ty(), *op, l_arg)
    }
    RValue::LNot { arg, .. } => {
      let arg = lower_rvalue(arg, ctx);
      ctx.build_lnot(arg)
    }
    RValue::Cast { .. } => {
      todo!() // TODO
    }
    RValue::Bin { op, lhs, rhs, .. } => {
      let l_lhs = lower_rvalue(lhs, ctx);
      let l_rhs = lower_rvalue(rhs, ctx);
      ctx.build_bin(lhs.ty(), *op, l_lhs, l_rhs)
    }
    RValue::LAnd { .. } => {
      todo!() // TODO
    }
    RValue::LOr { .. } => {
      todo!() // TODO
    }
    RValue::Block { body, .. } => {
      let mut val = ctx.build_void();
      for expr in body.iter() {
        val = lower_rvalue(expr, ctx);
      }
      val
    }
    RValue::As { lhs, rhs, .. } => {
      let dest = lower_lvalue(lhs, ctx);
      let src = lower_rvalue(rhs, ctx);
      ctx.build_store(lhs.ty(), dest, src);
      // Void value
      ctx.build_void()
    }
    RValue::Rmw { op, lhs, rhs, .. } => {
      // LHS: We need both the address and value
      let dest_addr = lower_lvalue(lhs, ctx);
      let lhs_val = ctx.build_load(lhs.ty(), dest_addr);
      // RHS: We need only the value
      let rhs_val = lower_rvalue(rhs, ctx);
      // Then we can perform the computation and do the store
      let tmp_val = ctx.build_bin(lhs.ty(), *op, lhs_val, rhs_val);
      ctx.build_store(lhs.ty(), dest_addr, tmp_val);
      // Void value
      ctx.build_void()
    }
    RValue::Continue { .. } => {
      todo!() // TODO
    }
    RValue::Break { .. } => {
      todo!() // TODO
    }
    RValue::Return { .. } => {
      todo!() // TODO
    }
    RValue::Let { def, init, .. } => {
      // Allocate stack slot for local variable
      let l_alloca = ctx.build_alloca(def.name, &def.ty);
      ctx.values.insert(*def, l_alloca);
      // Store initializer in stack slot
      let init = lower_rvalue(init, ctx);
      ctx.build_store(&def.ty, l_alloca, init);
      // Void value
      ctx.build_void()
    }
    RValue::If { cond, tbody, ebody, .. } => {
      let then_block = ctx.new_block();
      let else_block = ctx.new_block();
      let end_block = ctx.new_block();

      lower_bool(cond, ctx, then_block, else_block);

      ctx.enter_block(then_block);
      lower_rvalue(tbody, ctx);
      ctx.exit_block_br(end_block);

      ctx.enter_block(else_block);
      lower_rvalue(ebody, ctx);
      ctx.exit_block_br(end_block);

      ctx.enter_block(end_block);
      ctx.build_void()
    }
    RValue::While { cond, body, .. } => {
      let test_block = ctx.new_block();
      let body_block = ctx.new_block();
      let end_block = ctx.new_block();

      ctx.exit_block_br(test_block);

      // Initial block is the test as a demorgan expr
      ctx.enter_block(test_block);
      lower_bool(cond, ctx, body_block, end_block);

      // Next block is the loop body
      ctx.enter_block(body_block);
      lower_rvalue(body, ctx);
      ctx.exit_block_br(test_block);

      // End of the loop
      ctx.enter_block(end_block);

      // Void value
      ctx.build_void()
    }
    RValue::Loop { body, .. } => {
      let body_block = ctx.new_block();

      ctx.exit_block_br(body_block);

      // Loop body in one block
      ctx.enter_block(body_block);
      lower_rvalue(body, ctx);
      ctx.exit_block_br(body_block);

      // Void value
      ctx.build_void()
    }
  }
}

unsafe fn lower_bool(rvalue: &RValue, ctx: &mut LowerCtx, next1: BB, next2: BB) {
  match rvalue {
    RValue::LNot { arg, .. } => {
      lower_bool(arg, ctx, next2, next1);
    }
    RValue::LAnd { lhs, rhs, .. } => {
      let mid_block = ctx.new_block();
      lower_bool(lhs, ctx, mid_block, next2);
      ctx.enter_block(mid_block);
      lower_bool(rhs, ctx, next1, next2);
    }
    RValue::LOr { lhs, rhs, .. } => {
      let mid_block = ctx.new_block();
      lower_bool(lhs, ctx, next1, mid_block);
      ctx.enter_block(mid_block);
      lower_bool(rhs, ctx, next1, next2);
    }
    _ => {
      let cond = lower_rvalue(rvalue, ctx);
      ctx.exit_block_cond_br(cond, next1, next2);
    }
  }
}

pub(super) struct LowerCtx {
  // Target machine
  l_machine: LLVMTargetMachineRef,
  l_layout: LLVMTargetDataRef,

  // LLVM handles
  l_context: LLVMContextRef,
  l_builder: LLVMBuilderRef,
  l_module: LLVMModuleRef,
  l_func: LLVMValueRef,

  // Types
  types: IndexMap<Ptr<TyDef>, LLVMTypeRef>,

  // Values
  values: IndexMap<Ptr<Def>, LLVMValueRef>,

  // String literals
  string_lits: IndexMap<RefStr, LLVMValueRef>,
}

impl LowerCtx {
  unsafe fn new(module_id: RefStr) -> Self {
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
      LLVMRelocMode::LLVMRelocDefault,
      LLVMCodeModel::LLVMCodeModelDefault);

    let l_layout = LLVMCreateTargetDataLayout(l_machine);

    let l_context = LLVMGetGlobalContext();
    let l_builder = LLVMCreateBuilderInContext(l_context);
    let l_module = LLVMModuleCreateWithNameInContext(module_id.borrow_c(), l_context);

    LLVMSetTarget(l_module, l_triple);
    let l_layout_str = LLVMCopyStringRepOfTargetData(l_layout);
    LLVMSetDataLayout(l_module, l_layout_str);
    LLVMDisposeMessage(l_layout_str);

    LLVMDisposeMessage(l_triple);
    LLVMDisposeMessage(l_cpu_name);
    LLVMDisposeMessage(l_cpu_features);

    LowerCtx {
      l_machine,
      l_layout,
      l_context,
      l_builder,
      l_module,
      l_func: std::ptr::null_mut(),

      types: IndexMap::new(),
      values: IndexMap::new(),
      string_lits: IndexMap::new()
    }
  }

  unsafe fn align_of(&mut self, l_type: LLVMTypeRef) -> usize {
    LLVMPreferredAlignmentOfType(self.l_layout, l_type) as usize
  }

  unsafe fn size_of(&mut self, l_type: LLVMTypeRef) -> usize {
    LLVMStoreSizeOfType(self.l_layout, l_type) as usize
  }

  unsafe fn lower_params(&mut self, params: &Vec<(RefStr, Ty)>) -> Vec<LLVMTypeRef> {
    let mut l_params = vec![];
    for (_, ty) in params {
      l_params.push(self.lower_ty(ty));
    }
    l_params
  }

  unsafe fn lower_ty(&mut self, ty: &Ty) -> LLVMTypeRef {
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
        *self.types.get(def).unwrap()
      }
      Ptr(_, base_ty) => {
        LLVMPointerType(self.lower_ty(base_ty), 0)
      }
      Func(params, ret_ty) => {
        let mut l_params = self.lower_params(params);
        LLVMFunctionType(self.lower_ty(ret_ty),
          l_params.get_unchecked_mut(0) as _, l_params.len() as u32, 0)
      }
      Arr(siz, elem_ty) => {
        LLVMArrayType(self.lower_ty(elem_ty), *siz as u32)
      }
      Tuple(params) => {
        let mut l_params = self.lower_params(params);
        LLVMStructTypeInContext(self.l_context,
          l_params.get_unchecked_mut(0) as _, l_params.len() as u32, 0)
      }
      ClassAny | ClassNum | ClassInt | ClassFlt => {
        // FIXME: make sure this never happens
        panic!("Error: non-deduced type reached lowering")
      }
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

  unsafe fn lower_ty_defs(&mut self, ty_defs: &IndexMap<RefStr, Own<TyDef>>) {
    // Pass 1: Create named LLVM structure for each type definition
    for (name, ty_def) in ty_defs.iter() {
      self.types.insert(ty_def.ptr(),
        LLVMStructCreateNamed(self.l_context, name.borrow_c()));
    }
    // Pass 2: Resolve bodies
    for (_, ty_def) in ty_defs.iter() {
      let mut l_params = match &ty_def.kind {
        TyDefKind::ToBeFilled => unreachable!(),
        TyDefKind::Struct(params) => {
          // This is the simplest case, LLVM has native support for structures
          self.lower_params(params)
        }
        TyDefKind::Union(params) => {
          // The union lowering code is shared with enums thus it's in 'lower_union'
          let l_params = self.lower_params(params);
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
                let mut l_params = self.lower_params(params);
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
      LLVMStructSetBody(*self.types.get(&ty_def.ptr()).unwrap(),
        l_params.get_unchecked_mut(0) as _, l_params.len() as u32, 0);
    }
  }

  unsafe fn new_block(&mut self) -> LLVMBasicBlockRef {
    assert!(self.l_func != std::ptr::null_mut());
    LLVMAppendBasicBlock(self.l_func, empty_cstr())
  }

  unsafe fn enter_block(&mut self, block: LLVMBasicBlockRef) {
    LLVMPositionBuilderAtEnd(self.l_builder, block);
  }

  unsafe fn exit_block_br(&mut self, dest: LLVMBasicBlockRef) {
    LLVMBuildBr(self.l_builder, dest);
  }

  unsafe fn exit_block_cond_br(&mut self, cond: LLVMValueRef,
                                dest1: LLVMBasicBlockRef,
                                dest2: LLVMBasicBlockRef) {
    LLVMBuildCondBr(self.l_builder, cond, dest1, dest2);
  }

  unsafe fn build_void(&mut self) -> LLVMValueRef {
    LLVMConstNull(LLVMStructTypeInContext(
      self.l_context, std::ptr::null_mut(), 0, 0))
  }

  unsafe fn build_string_lit(&mut self, s: RefStr) -> LLVMValueRef {
    // Borrow checker :/
    let l_module = self.l_module;
    let l_context = self.l_context;
    let index = self.string_lits.len();

    *self.string_lits.entry(s).or_insert_with(|| {
      // Create name
      let name = RefStr::new(&format!(".str.{}", index));

      // Create global
      let len = s.borrow_rs().len() as u32;
      let val = LLVMAddGlobal(l_module,
                  LLVMArrayType(LLVMInt8TypeInContext(l_context), len),
                  name.borrow_c());

      // Set initializer
      // NOTE: for now these are NUL-terminated
      LLVMSetInitializer(val, LLVMConstStringInContext(l_context, s.borrow_c(), len, 0));

      val
    })
  }

  unsafe fn build_bool(&mut self, val: bool) -> LLVMValueRef {
    LLVMConstInt(LLVMInt1TypeInContext(self.l_context), val as u64, 0)
  }

  unsafe fn build_int(&mut self, ty: &Ty, val: usize) -> LLVMValueRef {
    LLVMConstInt(self.lower_ty(ty), val as u64, 0)
  }

  unsafe fn build_flt(&mut self, ty: &Ty, val: f64) -> LLVMValueRef {
    LLVMConstReal(self.lower_ty(ty), val)
  }

  unsafe fn build_const_dot(&mut self, l_addr: LLVMValueRef, idx: usize) -> LLVMValueRef {
    let mut indices = [
      LLVMConstInt(LLVMInt8TypeInContext(self.l_context), 0, 0),
      // NOTE: this is not documented in many places, but struct field
      // indices have to be Int32 otherwise LLVM crashes :(
      LLVMConstInt(LLVMInt32TypeInContext(self.l_context), idx as u64, 0)
    ];
    LLVMConstInBoundsGEP(l_addr,
      &mut indices as *mut LLVMValueRef,
      indices.len() as u32)

  }

  unsafe fn build_const_index(&mut self, l_addr: LLVMValueRef, l_idx: LLVMValueRef) -> LLVMValueRef {
    let mut indices = [
      LLVMConstInt(LLVMInt8TypeInContext(self.l_context), 0, 0),
      l_idx
    ];
    LLVMConstInBoundsGEP(l_addr,
      &mut indices as *mut LLVMValueRef,
      indices.len() as u32)
  }

  unsafe fn build_const_un(&mut self, ty: &Ty, op: UnOp, arg: LLVMValueRef) -> LLVMValueRef {
    use Ty::*;
    use UnOp::*;

    match (op, ty) {
      (UPlus, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn | Float | Double) => {
        arg
      }
      (UMinus, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMConstNeg(arg)
      }
      (UMinus, Float | Double) => {
        LLVMConstFNeg(arg)
      }
      (Not, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMConstNot(arg)
      }
      _ => unreachable!()
    }
  }

  unsafe fn build_const_lnot(&mut self, l_arg: LLVMValueRef) -> LLVMValueRef {
    if LLVMIsNull(l_arg) == 1 {
      self.build_bool(true)
    } else {
      self.build_bool(false)
    }
  }

  unsafe fn build_const_bin(&mut self, ty: &Ty, op: BinOp, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
    use Ty::*;
    use BinOp::*;

    match (op, ty) {
      // Integer multiply
      (Mul, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMConstMul(lhs, rhs)
      }
      // Floating point multiply
      (Mul, Float | Double) => {
        LLVMConstFMul(lhs, rhs)
      }
      // Unsigned integer divide
      (Div, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMConstUDiv(lhs, rhs)
      }
      // Signed integer divide
      (Div, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMConstSDiv(lhs, rhs)
      }
      // Floating point divide
      (Div, Float | Double) => {
        LLVMConstFDiv(lhs, rhs)
      }
      // Unsigned integer modulo
      (Mod, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMConstURem(lhs, rhs)
      }
      // Signed integer modulo
      (Mod, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMConstSRem(lhs, rhs)
      }
      // Integer addition
      (Add, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMConstAdd(lhs, rhs)
      }
      // Floating point addition
      (Add, Float | Double) => {
        LLVMConstFAdd(lhs, rhs)
      }
      // Integer substraction
      (Sub, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMConstSub(lhs, rhs)
      }
      // Floating point substraction
      (Sub, Float | Double) => {
        LLVMConstFSub(lhs, rhs)
      }
      // Left shift
      (Lsh, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMConstShl(lhs, rhs)
      }
      // Unsigned (logical) right shift
      (Rsh, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMConstLShr(lhs, rhs)
      }
      // Signed (arithmetic) right shift
      (Rsh, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMConstAShr(lhs, rhs)
      }
      // Bitwise and
      (And, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMConstAnd(lhs, rhs)
      }
      // Bitwise xor
      (Xor, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMConstXor(lhs, rhs)
      }
      // Bitwise or
      (Or, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMConstOr(lhs, rhs)
      }
      // Integer equality and inequality
      (Eq, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMConstICmp(LLVMIntEQ, lhs, rhs)
      }
      (Ne, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMConstICmp(LLVMIntNE, lhs, rhs)
      }
      // Unsigned integer comparisons
      (Lt, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMConstICmp(LLVMIntULT, lhs, rhs)
      }
      (Gt, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMConstICmp(LLVMIntUGT, lhs, rhs)
      }
      (Le, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMConstICmp(LLVMIntULE, lhs, rhs)
      }
      (Ge, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMConstICmp(LLVMIntUGE, lhs, rhs)
      }
      // Signed integer comparisons
      (Lt, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMConstICmp(LLVMIntSLT, lhs, rhs)
      }
      (Gt, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMConstICmp(LLVMIntSGT, lhs, rhs)
      }
      (Le, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMConstICmp(LLVMIntSLE, lhs, rhs)
      }
      (Ge, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMConstICmp(LLVMIntSGE, lhs, rhs)
      }
      // Float Comparisons
      (Eq, Float | Double) => {
        LLVMConstFCmp(LLVMRealOEQ, lhs, rhs)
      }
      (Ne, Float | Double) => {
        LLVMConstFCmp(LLVMRealONE, lhs, rhs)
      }
      (Lt, Float | Double) => {
        LLVMConstFCmp(LLVMRealOLT, lhs, rhs)
      }
      (Gt, Float | Double) => {
        LLVMConstFCmp(LLVMRealOGT, lhs, rhs)
      }
      (Le, Float | Double) => {
        LLVMConstFCmp(LLVMRealOLE, lhs, rhs)
      }
      (Ge, Float | Double) => {
        LLVMConstFCmp(LLVMRealOGE, lhs, rhs)
      }
      _ => unreachable!()
    }
  }

  /// Determine if a type should use value or pointer semantics

  fn backend_value_semantics(ty: &Ty) -> bool {
    use Ty::*;
    match ty {
      Bool | Uint8 | Int8 | Uint16 |
      Int16 |Uint32 | Int32 | Uint64 |
      Int64 | Uintn | Intn | Float |
      Double | Ptr(..) | Func(..) => true,
      Ref(..) | Arr(..) | Tuple(..) => false,
      ClassAny | ClassNum | ClassInt | ClassFlt => unreachable!()
    }
  }

  unsafe fn build_alloca(&mut self, name: RefStr, ty: &Ty) -> LLVMValueRef {
    LLVMBuildAlloca(self.l_builder, self.lower_ty(ty), name.borrow_c())
  }

  unsafe fn build_load(&mut self, ty: &Ty, l_src: LLVMValueRef) -> LLVMValueRef {
    if Self::backend_value_semantics(ty) {
      LLVMBuildLoad(self.l_builder, l_src, empty_cstr())
    } else {
      l_src
    }
  }

  unsafe fn build_store(&mut self, ty: &Ty, l_dest: LLVMValueRef, l_src: LLVMValueRef) {
    if Self::backend_value_semantics(ty) {
      LLVMBuildStore(self.l_builder, l_src, l_dest);
    } else {
      let l_type = self.lower_ty(ty);
      let align = self.align_of(l_type) as u32;
      let size = LLVMConstInt(LLVMInt32TypeInContext(self.l_context),
                                self.size_of(l_type) as u64, 0);
      LLVMBuildMemCpy(self.l_builder, l_dest, align, l_src, align, size);
    }
  }

  unsafe fn build_dot(&mut self, l_addr: LLVMValueRef, idx: usize) -> LLVMValueRef {
    let mut indices = [
      LLVMConstInt(LLVMInt8TypeInContext(self.l_context), 0, 0),
      // NOTE: this is not documented in many places, but struct field
      // indices have to be Int32 otherwise LLVM crashes :(
      LLVMConstInt(LLVMInt32TypeInContext(self.l_context), idx as u64, 0)
    ];
    LLVMBuildInBoundsGEP(self.l_builder, l_addr,
      &mut indices as *mut LLVMValueRef,
      indices.len() as u32,
      empty_cstr())
  }

  unsafe fn build_index(&mut self, l_addr: LLVMValueRef, l_idx: LLVMValueRef) -> LLVMValueRef {
    let mut indices = [
      LLVMConstInt(LLVMInt8TypeInContext(self.l_context), 0, 0),
      l_idx
    ];
    LLVMBuildInBoundsGEP(self.l_builder, l_addr,
      &mut indices as *mut LLVMValueRef,
      indices.len() as u32,
      empty_cstr())
  }

  unsafe fn build_call(&mut self, l_func: LLVMValueRef, mut l_args: Vec<LLVMValueRef>) -> LLVMValueRef {
    LLVMBuildCall(self.l_builder, l_func,
                  &mut l_args[0] as *mut Val,
                  l_args.len() as u32,
                  empty_cstr())
  }

  unsafe fn build_lnot(&mut self, l_arg: LLVMValueRef) -> LLVMValueRef {
    LLVMBuildIsNull(self.l_builder, l_arg, empty_cstr())
  }

  unsafe fn build_un(&mut self, ty: &Ty, op: UnOp, l_arg: LLVMValueRef) -> LLVMValueRef {
    use Ty::*;
    use UnOp::*;

    match (op, ty) {
      (UPlus, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn | Float | Double) => {
        l_arg
      }
      (UMinus, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMBuildNeg(self.l_builder, l_arg, empty_cstr())
      }
      (UMinus, Float | Double) => {
        LLVMBuildFNeg(self.l_builder, l_arg, empty_cstr())
      }
      (Not, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMBuildNot(self.l_builder, l_arg, empty_cstr())
      }
      _ => unreachable!()
    }
  }

  unsafe fn build_bin(&mut self, ty: &Ty, op: BinOp, l_lhs: LLVMValueRef, l_rhs: LLVMValueRef) -> LLVMValueRef {
    use Ty::*;
    use BinOp::*;

    match (op, ty) {
      // Integer multiply
      (Mul, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMBuildMul(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Floating point multiply
      (Mul, Float | Double) => {
        LLVMBuildFMul(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Unsigned integer divide
      (Div, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMBuildUDiv(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Signed integer divide
      (Div, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMBuildSDiv(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Floating point divide
      (Div, Float | Double) => {
        LLVMBuildFDiv(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Unsigned integer modulo
      (Mod, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMBuildURem(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Signed integer modulo
      (Mod, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMBuildSRem(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Integer addition
      (Add, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMBuildAdd(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Floating point addition
      (Add, Float | Double) => {
        LLVMBuildFAdd(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Integer substraction
      (Sub, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMBuildSub(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Floating point substraction
      (Sub, Float | Double) => {
        LLVMBuildFSub(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Left shift
      (Lsh, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMBuildShl(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Unsigned (logical) right shift
      (Rsh, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMBuildLShr(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Signed (arithmetic) right shift
      (Rsh, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMBuildAShr(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Bitwise and
      (And, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMBuildAnd(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Bitwise xor
      (Xor, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMBuildXor(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Bitwise or
      (Or, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMBuildOr(self.l_builder, l_lhs, l_rhs, empty_cstr())
      }
      // Integer equality and inequality
      (Eq, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMBuildICmp(self.l_builder, LLVMIntEQ, l_lhs, l_rhs, empty_cstr())
      }
      (Ne, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        LLVMBuildICmp(self.l_builder, LLVMIntNE, l_lhs, l_rhs, empty_cstr())
      }
      // Unsigned integer comparisons
      (Lt, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMBuildICmp(self.l_builder, LLVMIntULT, l_lhs, l_rhs, empty_cstr())
      }
      (Gt, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMBuildICmp(self.l_builder, LLVMIntUGT, l_lhs, l_rhs, empty_cstr())
      }
      (Le, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMBuildICmp(self.l_builder, LLVMIntULE, l_lhs, l_rhs, empty_cstr())
      }
      (Ge, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        LLVMBuildICmp(self.l_builder, LLVMIntUGE, l_lhs, l_rhs, empty_cstr())
      }
      // Signed integer comparisons
      (Lt, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMBuildICmp(self.l_builder, LLVMIntSLT, l_lhs, l_rhs, empty_cstr())
      }
      (Gt, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMBuildICmp(self.l_builder, LLVMIntSGT, l_lhs, l_rhs, empty_cstr())
      }
      (Le, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMBuildICmp(self.l_builder, LLVMIntSLE, l_lhs, l_rhs, empty_cstr())
      }
      (Ge, Int8 | Int16 | Int32 | Int64 | Intn) => {
        LLVMBuildICmp(self.l_builder, LLVMIntSGE, l_lhs, l_rhs, empty_cstr())
      }
      // Float Comparisons
      (Eq, Float | Double) => {
        LLVMBuildFCmp(self.l_builder, LLVMRealOEQ, l_lhs, l_rhs, empty_cstr())
      }
      (Ne, Float | Double) => {
        LLVMBuildFCmp(self.l_builder, LLVMRealONE, l_lhs, l_rhs, empty_cstr())
      }
      (Lt, Float | Double) => {
        LLVMBuildFCmp(self.l_builder, LLVMRealOLT, l_lhs, l_rhs, empty_cstr())
      }
      (Gt, Float | Double) => {
        LLVMBuildFCmp(self.l_builder, LLVMRealOGT, l_lhs, l_rhs, empty_cstr())
      }
      (Le, Float | Double) => {
        LLVMBuildFCmp(self.l_builder, LLVMRealOLE, l_lhs, l_rhs, empty_cstr())
      }
      (Ge, Float | Double) => {
        LLVMBuildFCmp(self.l_builder, LLVMRealOGE, l_lhs, l_rhs, empty_cstr())
      }
      _ => unreachable!()
    }
  }

  unsafe fn lower_defs(&mut self, defs: &IndexMap<RefStr, Own<Def>>) {
    // Pass 1: Create LLVM values for each definition
    for (name, def) in defs.iter() {
      let l_value = match &def.kind {
        DefKind::Const(val) => {
          lower_const_rvalue(val, self)
        }
        DefKind::Data(..) | DefKind::ExternData => {
          LLVMAddGlobal(self.l_module, self.lower_ty(&def.ty),
                                      name.borrow_c())
        }
        DefKind::Func(..) | DefKind::ExternFunc => {
          LLVMAddFunction(self.l_module, name.borrow_c(),
                                        self.lower_ty(&def.ty))
        }
        _ => continue
      };

      self.values.insert(def.ptr(), l_value);
    }
    // Pass 2: Lower initializers and function bodies
    for (_, def) in defs.iter() {
      let l_value = *self.values.get(&def.ptr()).unwrap();

      match &def.kind {
        DefKind::Data(init) => {
          LLVMSetInitializer(l_value, lower_const_rvalue(init, self));
        }
        DefKind::Func(params, body) => {
          // Entry point
          self.l_func = l_value;
          let entry_block = self.new_block();
          self.enter_block(entry_block);

          // Spill parameters
          for (_, def) in params.iter() {
            let index = match &def.kind {
              DefKind::Param(index) => *index,
              _ => unreachable!(),
            };

            let l_alloca = self.build_alloca(def.name, &def.ty);
            self.values.insert(def.ptr(), l_alloca);
            LLVMBuildStore(self.l_builder, LLVMGetParam(l_value, index as u32), l_alloca);
          }

          // Lower function body
          LLVMBuildRet(self.l_builder, lower_rvalue(body, self));
        }
        _ => ()
      }
    }
  }

  unsafe fn lower_module(&mut self, module: &Module) {
    self.lower_ty_defs(&module.ty_defs);
    self.lower_defs(&module.defs[0]);
  }

  unsafe fn dump(&self) {
    LLVMDumpModule(self.l_module)
  }

  unsafe fn write_ir(&self, output_path: &str) {
    let errors = std::ptr::null_mut();
    LLVMPrintModuleToFile(self.l_module, RefStr::new(output_path).borrow_c(), errors);
    assert!(errors.is_null());
  }

  unsafe fn write_asm(&self, output_path: &str) {
    let errors = std::ptr::null_mut();
    LLVMTargetMachineEmitToFile(
      self.l_machine,
      self.l_module,
      // NOTE: this transmute is borked, but LLVMTargetMachineEmitToFile
      // should take a const pointer anyways, so it seems like the Rust FFI
      // bindings are at fault here.
      std::mem::transmute(RefStr::new(output_path).borrow_c()),
      LLVMCodeGenFileType::LLVMAssemblyFile,
      errors);
    assert!(errors.is_null());
  }

  unsafe fn write_obj(&self, output_path: &str) {
    let errors = std::ptr::null_mut();
    LLVMTargetMachineEmitToFile(
      self.l_machine,
      self.l_module,
      std::mem::transmute(RefStr::new(output_path).borrow_c()),
      LLVMCodeGenFileType::LLVMObjectFile,
      errors);
    assert!(errors.is_null());
  }
}

impl Drop for LowerCtx {
  fn drop(&mut self) {
    unsafe {
      LLVMDisposeTargetMachine(self.l_machine);
      LLVMDisposeTargetData(self.l_layout);
      LLVMDisposeBuilder(self.l_builder);
      LLVMDisposeModule(self.l_module);
      LLVMContextDispose(self.l_context);
    }
  }
}

pub enum CompileTo {
  LLVMIr,
  Assembly,
  Object,
}


pub fn lower_module(module: &mut Module, path: &str, compile_to: CompileTo) -> MRes<()> {
  unsafe {
    let mut ctx = LowerCtx::new(RefStr::new(""));
    ctx.lower_module(module);
    ctx.dump();
    match compile_to {
      CompileTo::LLVMIr => ctx.write_ir(path),
      CompileTo::Assembly => ctx.write_asm(path),
      CompileTo::Object => ctx.write_obj(path),
    };
    Ok(())
  }
}
