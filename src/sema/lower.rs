// SPDX-License-Identifier: GPL-2.0-only

use super::*;
use llvm_sys::core::*;
use llvm_sys::target::*;
use llvm_sys::LLVMIntPredicate::*;
use llvm_sys::LLVMRealPredicate::*;

fn needs_load(ty: &Ty) -> bool {
  use Ty::*;
  match ty {
    Bool | Uint8 | Int8 | Uint16 |
    Int16 |Uint32 | Int32 | Uint64 |
    Int64 | Uintn | Intn | Float |
    Double | Fn(..) | Ptr(..) => true,
    Ref(..) | Arr(..) | Tuple(..) => false,
    ClassAny | ClassNum | ClassInt => unreachable!()
  }
}

// Strings describing the target and data layout for LLVM
// These match AMD64 clang on Linux for now
const TRIPLE: &str = "x86_64-pc-linux-gnu";
const DATALAYOUT: &str = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128";

struct LowerCtx {
  l_context: LLVMContextRef,
  l_builder: LLVMBuilderRef,
  l_module: LLVMModuleRef,
  l_func: LLVMValueRef,
}

impl LowerCtx {
  unsafe fn new(module_id: RefStr) -> Self {
    let l_context = LLVMGetGlobalContext();
    let l_builder = LLVMCreateBuilderInContext(l_context);
    let l_module = LLVMModuleCreateWithNameInContext(module_id.borrow_c(), l_context);
    LLVMSetTarget(l_module, RefStr::new(TRIPLE).borrow_c());
    LLVMSetDataLayout(l_module, RefStr::new(DATALAYOUT).borrow_c());

    LowerCtx { l_context, l_builder, l_module, l_func: std::ptr::null_mut() }
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

  unsafe fn lower_const_addr(&mut self, expr: &Expr) -> LLVMValueRef {
    use ExprKind::*;
    match &expr.kind {
      Ref(def) => def.l_value,
      Dot(_, arg, _, idx) => {
        let l_arg = self.lower_const_addr(arg);
        let mut l_idx = [
          LLVMConstInt(LLVMInt8TypeInContext(self.l_context), 0, 0),
          // NOTE: this is not documented in many places, but struct field
          // indices have to be Int32 otherwise LLVM crashes :(
          LLVMConstInt(LLVMInt32TypeInContext(self.l_context), *idx as u64, 0)
        ];
        LLVMConstInBoundsGEP(l_arg, &mut l_idx as *mut LLVMValueRef, l_idx.len() as u32)
      }
      Index(_, arg, idx) => {
        let l_arg = self.lower_const_addr(arg);
        let mut l_idx = [
          LLVMConstInt(LLVMInt8TypeInContext(self.l_context), 0, 0),
          self.lower_const(idx)
        ];
        LLVMConstInBoundsGEP(l_arg, &mut l_idx as *mut LLVMValueRef, l_idx.len() as u32)
      }
      Ind(_, arg) => self.lower_const(arg),
      _ => panic!("Expected constant initializer")
    }
  }

  unsafe fn lower_const(&mut self, expr: &Expr) -> LLVMValueRef {
    use ExprKind::*;
    match &expr.kind {
      Bool(val) => LLVMConstInt(self.ty_to_llvm(&expr.ty), *val as u64, 0),
      Int(val) => LLVMConstInt(self.ty_to_llvm(&expr.ty), *val as u64, 0),
      Char(val) => todo!(),
      Str(val) => todo!(),
      Adr(arg) => self.lower_const_addr(arg),
      Un(UnOp::UPlus, arg) => self.lower_const(arg),
      Un(UnOp::UMinus, arg) => LLVMConstNeg(self.lower_const(arg)),
      Un(UnOp::Not, arg) => LLVMConstNot(self.lower_const(arg)),
      // FIXME: we definitely want to support more constant expressions
      _ => panic!("Expected constant initializer")
    }
  }

  unsafe fn begin_block(&mut self) -> LLVMBasicBlockRef {
    assert!(self.l_func != std::ptr::null_mut());
    let block = LLVMAppendBasicBlock(self.l_func, empty_cstr());
    LLVMPositionBuilderAtEnd(self.l_builder, block);
    block
  }

  unsafe fn lower_addr(&mut self, expr: &mut Expr) -> LLVMValueRef {
    use ExprKind::*;
    match &mut expr.kind {
      Ref(def) => {
        def.l_value
      }
      Dot(_, arg, _, idx) => {
        let l_arg = self.lower_addr(arg);
        let mut l_idx = [
          LLVMConstInt(LLVMInt8TypeInContext(self.l_context), 0, 0),
          LLVMConstInt(LLVMInt32TypeInContext(self.l_context), *idx as u64, 0)
        ];
        LLVMBuildInBoundsGEP(self.l_builder,
          l_arg, &mut l_idx as *mut LLVMValueRef, l_idx.len() as u32,
          empty_cstr())
      }
      Index(_, arg, idx) => {
        let l_arg = self.lower_addr(arg);
        let mut l_idx = [
          LLVMConstInt(LLVMInt8TypeInContext(self.l_context), 0, 0),
          self.lower_const(idx)
        ];
        LLVMBuildInBoundsGEP(self.l_builder,
          l_arg, &mut l_idx as *mut LLVMValueRef, l_idx.len() as u32,
          empty_cstr())
      }
      Ind(_, arg) => {
        self.lower_expr(arg)
      }
      _ => panic!("Expected lvalue expression instead of {:?}", expr)
    }
  }

  unsafe fn lower_un(&mut self, ty: &Ty, op: UnOp, l_arg: LLVMValueRef) -> LLVMValueRef {
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

  unsafe fn lower_bin(&mut self, ty: &Ty, op: BinOp,
                      l_lhs: LLVMValueRef, l_rhs: LLVMValueRef) -> LLVMValueRef {
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

  unsafe fn lower_store(&mut self, ty: &Ty,
                                    l_type: LLVMTypeRef,
                                    l_dest: LLVMValueRef,
                                    l_src: LLVMValueRef) -> LLVMValueRef {
    if needs_load(ty) {
      LLVMBuildStore(self.l_builder, l_src, l_dest)
    } else {
      let align = self.align_of(l_type) as u32;
      let size = LLVMConstInt(LLVMInt32TypeInContext(self.l_context),
                                self.size_of(l_type) as u64, 0);
      LLVMBuildMemCpy(self.l_builder, l_dest, align, l_src, align, size)
    }
  }

  unsafe fn lower_expr(&mut self, expr: &mut Expr) -> LLVMValueRef {
    use ExprKind::*;
    match &mut expr.kind {
      Ref(def) => {
        // NOTE: unlike C, our Function types actually stand for the equivalent
        // of function *pointers* in C, identifiers referring to function names
        // are not lvalues, but instead stand for the addresses of their
        // corresponding functions
        match def.kind {
          DefKind::Func(..) | DefKind::ExternFunc => {
            def.l_value
          }
          _ => {
            if needs_load(&expr.ty) {
              LLVMBuildLoad(self.l_builder, self.lower_addr(expr), empty_cstr())
            } else {
              self.lower_addr(expr)
            }
          },
        }
      }
      Dot(..) | Index(..) | Ind(..) => {
        if needs_load(&expr.ty) {
          LLVMBuildLoad(self.l_builder, self.lower_addr(expr), empty_cstr())
        } else {
          self.lower_addr(expr)
        }
      }
      Bool(..) | Int(..) | Char(..) | Str(..) => {
        self.lower_const(expr)
      }
      Call(func, args) => {
        let l_func = self.lower_expr(func);
        let mut l_args = vec![];
        for (_, arg) in args.iter_mut() {
          l_args.push(self.lower_expr(arg));
        }
        LLVMBuildCall(self.l_builder, l_func,
                      &mut l_args[0] as *mut LLVMValueRef,
                      l_args.len() as u32,
                      empty_cstr())
      }
      Adr(arg) => {
        self.lower_addr(arg)
      }
      Un(op, arg) => {
        let l_arg = self.lower_expr(arg);
        self.lower_un(&arg.ty, *op, l_arg)
      }
      Cast(..) => {
        todo!()
      }
      Bin(op, lhs, rhs) => {
        let l_lhs = self.lower_expr(lhs);
        let l_rhs = self.lower_expr(rhs);
        self.lower_bin(&lhs.ty, *op, l_lhs, l_rhs)
      }
      Rmw(op, lhs, rhs) => {
        let l_type = self.ty_to_llvm(&lhs.ty);
        let l_lhs = self.lower_expr(lhs);
        let l_rhs = self.lower_expr(rhs);
        let tmp = self.lower_bin(&lhs.ty, *op, l_lhs, l_rhs);
        self.lower_store(&lhs.ty, l_type, l_lhs, tmp);
        tmp
      }
      As(lhs, rhs) => {
        let l_type = self.ty_to_llvm(&lhs.ty);
        let l_lhs = self.lower_expr(lhs);
        let l_rhs = self.lower_expr(rhs);
        self.lower_store(&lhs.ty, l_type, l_lhs, l_rhs)
      }
      Block(_, body) => {
        let mut val = LLVMConstNull(self.ty_to_llvm(&expr.ty));
        for expr in body {
          val = self.lower_expr(expr);
        }
        val
      }
      Continue => {
        todo!()
      }
      Break(arg) => {
        todo!()
      }
      Return(arg) => {
        todo!()
      }
      Let(def, init) => {
        let l_type = self.ty_to_llvm(&def.ty);
        def.l_value = LLVMBuildAlloca(self.l_builder,
                                        l_type, def.name.borrow_c());
        let l_init = self.lower_expr(init);
        self.lower_store(&def.ty, l_type, def.l_value, l_init)
      }
      If(cond, tbody, ebody) => {
        todo!()
      }
      While(cond, body) => {
        // FIXME: add control flow
        self.lower_expr(body)
      }
      Loop(body) => {
        // FIXME: add control flow
        self.lower_expr(body)
      }
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
    for (name, def) in defs.iter_mut() {
      let def_value = def.l_value;
      match &mut def.kind {
        DefKind::Data(init) => {
          LLVMSetInitializer(def_value, self.lower_const(&init));
        }
        DefKind::Func(params, body) => {
          // Entry point
          self.l_func = def_value;
          self.begin_block();

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
          LLVMBuildRet(self.l_builder, self.lower_expr(body));
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
