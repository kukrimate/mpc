// SPDX-License-Identifier: GPL-2.0-only

use super::*;
use llvm_sys::core::*;
use llvm_sys::target::*;
use llvm_sys::target_machine::*;
use llvm_sys::LLVMIntPredicate::*;
use llvm_sys::LLVMRealPredicate::*;

fn needs_load(ty: &Ty) -> bool {
  use Ty::*;
  match ty {
    Bool | Uint8 | Int8 | Uint16 |
    Int16 |Uint32 | Int32 | Uint64 |
    Int64 | Uintn | Intn | Float |
    Double | Ptr(..) => true,
    Fn(..) | Ref(..) | Arr(..) | Tuple(..) => false,
    ClassAny | ClassNum | ClassInt | ClassFlt => unreachable!()
  }
}

unsafe fn const_un(ty: &Ty, op: UnOp, arg: LLVMValueRef) -> LLVMValueRef {
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

unsafe fn const_bin(ty: &Ty, op: BinOp, lhs: LLVMValueRef, rhs: LLVMValueRef) -> LLVMValueRef {
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

pub(super) struct LowerCtx {
  // Target machine
  l_machine: LLVMTargetMachineRef,
  l_layout: LLVMTargetDataRef,

  // LLVM handles
  l_context: LLVMContextRef,
  l_builder: LLVMBuilderRef,
  l_module: LLVMModuleRef,
  l_func: LLVMValueRef,


  // String literals
  string_lits: IndexMap<RefStr, LLVMValueRef>,
}

pub(super) trait LowerExpr: ExprT {
  unsafe fn lower_const_addr(&self, _: &mut LowerCtx) -> LLVMValueRef { unreachable!() }
  unsafe fn lower_const_value(&self, _: &mut LowerCtx) -> LLVMValueRef { unreachable!() }

  unsafe fn lower_addr(&mut self, _: &mut LowerCtx) -> LLVMValueRef { unreachable!() }

  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    if needs_load(self.ty()) {
      LLVMBuildLoad(ctx.l_builder, self.lower_addr(ctx), empty_cstr())
    } else {
      self.lower_addr(ctx)
    }
  }

  unsafe fn lower_bool(&mut self, ctx: &mut LowerCtx,
                        true_block: LLVMBasicBlockRef,
                        false_block: LLVMBasicBlockRef) {
    LLVMBuildCondBr(ctx.l_builder, self.lower_value(ctx), true_block, false_block);
  }
}

impl LowerExpr for ExprNull {
  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    ctx.void_value()
  }
}

impl LowerExpr for ExprRef {
  unsafe fn lower_const_addr(&self, _: &mut LowerCtx) -> LLVMValueRef {
    self.def.l_value
  }

  unsafe fn lower_addr(&mut self, _: &mut LowerCtx) -> LLVMValueRef {
    self.def.l_value
  }
}

impl LowerExpr for ExprBool {
  unsafe fn lower_const_value(&self, ctx: &mut LowerCtx) -> LLVMValueRef {
    LLVMConstInt(ctx.ty_to_llvm(self.ty()), self.val as u64, 0)
  }

  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    LLVMConstInt(ctx.ty_to_llvm(self.ty()), self.val as u64, 0)
  }

  unsafe fn lower_bool(&mut self, ctx: &mut LowerCtx,
                        true_block: LLVMBasicBlockRef,
                        false_block: LLVMBasicBlockRef) {
    if self.val {
      LLVMBuildBr(ctx.l_builder, true_block);
    } else {
      LLVMBuildBr(ctx.l_builder, false_block);
    }
  }
}

impl LowerExpr for ExprInt {
  unsafe fn lower_const_value(&self, ctx: &mut LowerCtx) -> LLVMValueRef {
    LLVMConstInt(ctx.ty_to_llvm(self.ty()), self.val as u64, 0)
  }

  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    LLVMConstInt(ctx.ty_to_llvm(self.ty()), self.val as u64, 0)
  }
}

impl LowerExpr for ExprFlt {
  unsafe fn lower_const_value(&self, ctx: &mut LowerCtx) -> LLVMValueRef {
    LLVMConstReal(ctx.ty_to_llvm(self.ty()), self.val)
  }

  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    LLVMConstReal(ctx.ty_to_llvm(self.ty()), self.val)
  }
}

impl LowerExpr for ExprChar {}  // TODO

impl LowerExpr for ExprStr {
  unsafe fn lower_const_addr(&self, ctx: &mut LowerCtx) -> LLVMValueRef {
    ctx.build_string_lit(self.val)
  }

  unsafe fn lower_addr(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    ctx.build_string_lit(self.val)
  }
}

impl LowerExpr for ExprDot {
  unsafe fn lower_const_addr(&self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let ptr = self.arg.lower_const_addr(ctx);
    let mut indices = [
      LLVMConstInt(LLVMInt8TypeInContext(ctx.l_context), 0, 0),
      // NOTE: this is not documented in many places, but struct field
      // indices have to be Int32 otherwise LLVM crashes :(
      LLVMConstInt(LLVMInt32TypeInContext(ctx.l_context), self.idx as u64, 0)
    ];
    LLVMConstInBoundsGEP(ptr,
      &mut indices as *mut LLVMValueRef,
      indices.len() as u32)
  }

  unsafe fn lower_addr(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let ptr = self.arg.lower_addr(ctx);
    let mut indices = [
      LLVMConstInt(LLVMInt8TypeInContext(ctx.l_context), 0, 0),
      // NOTE: this is not documented in many places, but struct field
      // indices have to be Int32 otherwise LLVM crashes :(
      LLVMConstInt(LLVMInt32TypeInContext(ctx.l_context), self.idx as u64, 0)
    ];
    LLVMBuildInBoundsGEP(ctx.l_builder, ptr,
      &mut indices as *mut LLVMValueRef,
      indices.len() as u32,
      empty_cstr())
  }
}

impl LowerExpr for ExprCall {
  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let func = self.arg.lower_value(ctx);

    let mut args = vec![];
    for (_, arg) in self.args.iter_mut() {
      args.push(arg.lower_value(ctx));
    }

    LLVMBuildCall(ctx.l_builder, func,
                  &mut args[0] as *mut LLVMValueRef,
                  args.len() as u32,
                  empty_cstr())
  }
}

impl LowerExpr for ExprIndex {
  unsafe fn lower_const_addr(&self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let ptr = self.arg.lower_const_addr(ctx);
    let mut indices = [
      LLVMConstInt(LLVMInt8TypeInContext(ctx.l_context), 0, 0),
      self.idx.lower_const_value(ctx)
    ];
    LLVMConstInBoundsGEP(ptr,
      &mut indices as *mut LLVMValueRef,
      indices.len() as u32)
  }

  unsafe fn lower_addr(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let ptr = self.arg.lower_addr(ctx);
    let mut indices = [
      LLVMConstInt(LLVMInt8TypeInContext(ctx.l_context), 0, 0),
      self.idx.lower_value(ctx)
    ];
    LLVMBuildInBoundsGEP(ctx.l_builder, ptr,
      &mut indices as *mut LLVMValueRef,
      indices.len() as u32,
      empty_cstr())
  }
}

impl LowerExpr for ExprAdr {
  unsafe fn lower_const_value(&self, ctx: &mut LowerCtx) -> LLVMValueRef {
    self.arg.lower_const_addr(ctx)
  }

  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    self.arg.lower_addr(ctx)
  }
}

impl LowerExpr for ExprInd {
  unsafe fn lower_const_addr(&self, ctx: &mut LowerCtx) -> LLVMValueRef {
    self.arg.lower_const_value(ctx)
  }

  unsafe fn lower_addr(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    self.arg.lower_value(ctx)
  }
}

impl LowerExpr for ExprUn {
  unsafe fn lower_const_value(&self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let arg = self.arg.lower_const_value(ctx);
    const_un(self.ty(), self.op, arg)
  }

  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let arg = self.arg.lower_value(ctx);
    ctx.build_un(self.ty(), self.op, arg)
  }
}

impl LowerExpr for ExprLNot {
  unsafe fn lower_const_value(&self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let arg = self.arg.lower_const_value(ctx);
    if LLVMIsNull(arg) == 1 {
      LLVMConstInt(LLVMInt1TypeInContext(ctx.l_context), 1, 0)
    } else {
      LLVMConstInt(LLVMInt1TypeInContext(ctx.l_context), 0, 0)
    }
  }

  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let arg = self.arg.lower_value(ctx);
    LLVMBuildIsNull(ctx.l_builder, arg, empty_cstr())
  }

  unsafe fn lower_bool(&mut self, ctx: &mut LowerCtx,
                        true_block: LLVMBasicBlockRef,
                        false_block: LLVMBasicBlockRef) {
    self.arg.lower_bool(ctx, false_block, true_block);
  }
}

impl LowerExpr for ExprCast {}  // TODO

impl LowerExpr for ExprBin {
  unsafe fn lower_const_value(&self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let lhs = self.lhs.lower_const_value(ctx);
    let rhs = self.rhs.lower_const_value(ctx);
    const_bin(self.ty(), self.op, lhs, rhs)
  }

  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let lhs = self.lhs.lower_value(ctx);
    let rhs = self.rhs.lower_value(ctx);
    ctx.build_bin(self.lhs.ty(), self.op, lhs, rhs)
  }
}

impl LowerExpr for ExprLAnd {
  unsafe fn lower_value(&mut self, _: &mut LowerCtx) -> LLVMValueRef {
    todo!() // TODO
  }

  unsafe fn lower_bool(&mut self, ctx: &mut LowerCtx,
                        true_block: LLVMBasicBlockRef,
                        false_block: LLVMBasicBlockRef) {
    let mid_block = ctx.new_block();
    self.lhs.lower_bool(ctx, mid_block, false_block);
    ctx.enter_block(mid_block);
    self.rhs.lower_bool(ctx, true_block, false_block);
  }
}

impl LowerExpr for ExprLOr {
  unsafe fn lower_value(&mut self, _: &mut LowerCtx) -> LLVMValueRef {
    todo!() // TODO
  }

  unsafe fn lower_bool(&mut self, ctx: &mut LowerCtx,
                        true_block: LLVMBasicBlockRef,
                        false_block: LLVMBasicBlockRef) {
    let mid_block = ctx.new_block();
    self.lhs.lower_bool(ctx, true_block, mid_block);
    ctx.enter_block(mid_block);
    self.rhs.lower_bool(ctx, true_block, false_block);
  }
}

impl LowerExpr for ExprBlock {
  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let mut val = ctx.void_value();
    for expr in self.body.iter_mut() {
      val = expr.lower_value(ctx);
    }
    val
  }
}

impl LowerExpr for ExprAs {
  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let dest = self.lhs.lower_addr(ctx);
    let src = self.rhs.lower_value(ctx);
    ctx.build_store(self.lhs.ty(), dest, src);
    // Void value
    ctx.void_value()
  }
}

impl LowerExpr for ExprRmw {
  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    // LHS: We need both the address and value
    let dest = self.lhs.lower_addr(ctx);
    let lhs = LLVMBuildLoad(ctx.l_builder, dest, empty_cstr());
    // RHS: We need only the value
    let rhs = self.rhs.lower_value(ctx);
    // Then we can perform the computation and do the store
    let tmp = ctx.build_bin(self.lhs.ty(), self.op, lhs, rhs);
    ctx.build_store(self.lhs.ty(), dest, tmp);
    // Void value
    ctx.void_value()
  }
}

impl LowerExpr for ExprContinue {}
impl LowerExpr for ExprBreak {}
impl LowerExpr for ExprReturn {}

impl LowerExpr for ExprLet {
  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    // Allocate stack slot for local variable
    self.def.l_value = LLVMBuildAlloca(ctx.l_builder,
                                        ctx.ty_to_llvm(&self.def.ty),
                                        self.def.name.borrow_c());

    // Store initializer in stack slot
    let init = self.init.lower_value(ctx);
    ctx.build_store(&self.def.ty, self.def.l_value, init);

    // Void value
    ctx.void_value()
  }
}

impl LowerExpr for ExprIf {
  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let then_block = ctx.new_block();
    let else_block = ctx.new_block();
    let end_block = ctx.new_block();

    self.cond.lower_bool(ctx, then_block, else_block);

    ctx.enter_block(then_block);
    self.tbody.lower_value(ctx);
    LLVMBuildBr(ctx.l_builder, end_block);

    ctx.enter_block(else_block);
    self.ebody.lower_value(ctx);
    LLVMBuildBr(ctx.l_builder, end_block);

    ctx.enter_block(end_block);
    ctx.void_value()
  }
}

impl LowerExpr for ExprWhile {
  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let test_block = ctx.new_block();
    let body_block = ctx.new_block();
    let end_block = ctx.new_block();

    LLVMBuildBr(ctx.l_builder, test_block);

    // Initial block is the test as a demorgan expr
    ctx.enter_block(test_block);
    self.cond.lower_bool(ctx, body_block, end_block);

    // Next block is the loop body
    ctx.enter_block(body_block);
    self.body.lower_value(ctx);
    LLVMBuildBr(ctx.l_builder, test_block);

    // End of the loop
    ctx.enter_block(end_block);

    // Void value
    ctx.void_value()
  }
}

impl LowerExpr for ExprLoop {
  unsafe fn lower_value(&mut self, ctx: &mut LowerCtx) -> LLVMValueRef {
    let body_block = ctx.new_block();

    LLVMBuildBr(ctx.l_builder, body_block);

    // Loop body in one block
    ctx.enter_block(body_block);
    self.body.lower_value(ctx);
    LLVMBuildBr(ctx.l_builder, body_block);

    // Void value
    ctx.void_value()
  }
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
      string_lits: IndexMap::new()
    }
  }

  unsafe fn align_of(&mut self, l_type: LLVMTypeRef) -> usize {
    LLVMPreferredAlignmentOfType(self.l_layout, l_type) as usize
  }

  unsafe fn size_of(&mut self, l_type: LLVMTypeRef) -> usize {
    LLVMStoreSizeOfType(self.l_layout, l_type) as usize
  }

  unsafe fn params_to_llvm(&mut self, params: &Vec<(RefStr, Ty)>) -> Vec<LLVMTypeRef> {
    let mut l_params = vec![];
    for (_, ty) in params {
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

  unsafe fn lower_ty_defs(&mut self, ty_defs: &mut IndexMap<RefStr, Own<TyDef>>) {
    // Pass 1: Create named LLVM structure for each type definition
    for (name, ty_def) in ty_defs.iter_mut() {
      ty_def.l_type = LLVMStructCreateNamed(self.l_context, name.borrow_c());
    }
    // Pass 2: Resolve bodies
    for (_, ty_def) in ty_defs.iter_mut() {
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

  unsafe fn void_value(&mut self) -> LLVMValueRef {
    LLVMConstNull(LLVMStructTypeInContext(
      self.l_context, std::ptr::null_mut(), 0, 0))
  }

  unsafe fn new_block(&mut self) -> LLVMBasicBlockRef {
    assert!(self.l_func != std::ptr::null_mut());
    LLVMAppendBasicBlock(self.l_func, empty_cstr())
  }

  unsafe fn enter_block(&mut self, block: LLVMBasicBlockRef) {
    LLVMPositionBuilderAtEnd(self.l_builder, block);
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

  unsafe fn build_store(&mut self, ty: &Ty, l_dest: LLVMValueRef, l_src: LLVMValueRef) {
    if needs_load(ty) {
      LLVMBuildStore(self.l_builder, l_src, l_dest);
    } else {
      let l_type = self.ty_to_llvm(ty);
      let align = self.align_of(l_type) as u32;
      let size = LLVMConstInt(LLVMInt32TypeInContext(self.l_context),
                                self.size_of(l_type) as u64, 0);
      LLVMBuildMemCpy(self.l_builder, l_dest, align, l_src, align, size);
    }
  }

  unsafe fn lower_defs(&mut self, defs: &mut IndexMap<RefStr, Own<Def>>) {
    // Pass 1: Create LLVM values for each definition
    for (name, def) in defs.iter_mut() {
      match &def.kind {
        DefKind::Data(..) | DefKind::ExternData => {
          def.l_value = LLVMAddGlobal(self.l_module,
                                      self.ty_to_llvm(&def.ty),
                                      name.borrow_c());
        }
        DefKind::Func(..) | DefKind::ExternFunc => {
          def.l_value = LLVMAddFunction(self.l_module, name.borrow_c(),
                                        self.ty_to_llvm(&def.ty));
        }
        _ => ()
      }
    }
    // Pass 2: Lower initializers and function bodies
    for (_, def) in defs.iter_mut() {
      let def_value = def.l_value;
      match &mut def.kind {
        DefKind::Data(init) => {
          LLVMSetInitializer(def_value, init.lower_const_value(self));
        }
        DefKind::Func(params, body) => {
          // Entry point
          self.l_func = def_value;
          let entry_block = self.new_block();
          self.enter_block(entry_block);

          // Spill parameters
          for (_, param_def) in params.iter_mut() {
            let index = match &param_def.kind {
              DefKind::Param(index) => *index,
              _ => unreachable!(),
            };

            let l_type = self.ty_to_llvm(&param_def.ty);
            param_def.l_value = LLVMBuildAlloca(self.l_builder, l_type, param_def.name.borrow_c());
            LLVMBuildStore(self.l_builder, LLVMGetParam(def_value, index as u32), param_def.l_value);
          }

          // Lower function body
          LLVMBuildRet(self.l_builder, body.lower_value(self));
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
