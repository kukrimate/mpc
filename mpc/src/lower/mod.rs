/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use crate::*;
use crate::sema::*;
use crate::parse::{DefId,BinOp,UnOp};
use mpc_llvm as llvm;
use std::collections::HashMap;

pub fn compile(collection: &mut Collection, output: &Path, compile_to: CompileTo) -> MRes<()> {
  let context = llvm::Context::new();
  let mut ctx = LowerCtx::new(
    &mut collection.tctx, &collection.insts, &context, RefStr::new(""));

  ctx.lower_defs();
  if let Some(_) = option_env!("MPC_SPEW") {
    ctx.module.dump();
  }
  match compile_to {
    CompileTo::LLVMIr => ctx.target.write_llvm_ir(ctx.module, output)?,
    CompileTo::Assembly => ctx.target.write_machine_code(ctx.module, true, output)?,
    CompileTo::Object => ctx.target.write_machine_code(ctx.module, false, output)?,
  };
  Ok(())
}

/// Semantics of a type
enum Semantics {
  Void,
  Value,
  Addr
}

struct LowerCtx<'a, 'ctx> {
  tctx: &'a mut TVarCtx,
  insts: &'a HashMap<(DefId, Vec<Ty>), Inst>,

  // Target machine
  target: llvm::Target,

  // LLVM handles
  context: &'ctx llvm::Context,
  builder: llvm::Builder<'ctx>,
  module: llvm::Module<'ctx>,

  l_func: Option<llvm::Value<'ctx>>,
  l_alloca_block: Option<llvm::Block<'ctx>>,

  // Types
  types: HashMap<(DefId, Vec<Ty>), llvm::Type<'ctx>>,

  // Values
  values: HashMap<(DefId, Vec<Ty>), llvm::Value<'ctx>>,

  // String literals
  string_lits: HashMap<Vec<u8>, llvm::Value<'ctx>>,

  // Function parameters and locals
  params: Vec<llvm::Value<'ctx>>,
  locals: Vec<llvm::Value<'ctx>>,
  bindings: Vec<llvm::Value<'ctx>>,

  // Break and continue blocks
  break_to: Vec<llvm::Block<'ctx>>,
  continue_to: Vec<llvm::Block<'ctx>>
}

impl<'a, 'ctx> LowerCtx<'a, 'ctx> {
  fn new(tctx: &'a mut TVarCtx,
         insts: &'a HashMap<(DefId, Vec<Ty>), Inst>,
         context: &'ctx llvm::Context,
         name: RefStr) -> Self {

    let target = llvm::Target::native();

    let builder = context.builder();
    let module = context.module(name.borrow_c());
    module.set_target(&target);

    LowerCtx {
      tctx,
      insts,

      target,

      context,
      builder,
      module,

      l_func: None,
      l_alloca_block: None,

      types: HashMap::new(),
      values: HashMap::new(),

      string_lits: HashMap::new(),

      params: Vec::new(),
      locals: Vec::new(),
      bindings: Vec::new(),

      break_to: Vec::new(),
      continue_to: Vec::new()
    }
  }

  fn get_type(&mut self, id: &(DefId, Vec<Ty>)) -> llvm::Type<'ctx> {
    let id = (id.0, self.tctx.canonical_type_args(&id.1));
    if let Some(ty) = self.types.get(&id) {
      *ty
    } else {
      let inst = self.insts.get(&id).unwrap();
      let ty = self.lower_ty_def(inst);
      self.types.insert(id, ty);
      ty
    }
  }

  fn lower_ty_def(&mut self, inst: &Inst) -> llvm::Type<'ctx> {
    let fields = match inst {
      Inst::Struct { params: Some(params), .. } => {
        // This is the simplest case, LLVM has native support for structures
        params
          .iter()
          .map(|(_, ty)| self.lower_ty(ty))
          .collect()
      }
      Inst::Union { params: Some(params), .. } => {
        // The union lowering code is shared with enums thus it's in 'lower_union'
        let l_params: Vec<llvm::Type<'ctx>> = params
          .iter()
          .map(|(_, ty)| self.lower_ty(ty))
          .collect();

        self.lower_union(&l_params)
      }
      Inst::Enum { variants: Some(variants), .. } => {
        // Enum lowering is done by adding a discriminant (always a dword for now)
        // Followed by the variants lowered as if they were parameters of a union

        // Convert struct-like variants into LLVM types
        let mut variant_tys = vec![];
        for variant in variants {
          match variant {
            Variant::Unit(_) => (),
            Variant::Struct(_, params) => {
              let l_params: Vec<llvm::Type<'ctx>> = params
                .iter()
                .map(|(_, ty)| self.lower_ty(ty))
                .collect();
              variant_tys.push(self.lower_struct(&l_params));
            }
          }
        }

        // Create actual enum parameters
        concat(
          vec![ self.context.ty_int32() ],
          self.lower_union(&variant_tys)
        )
      }
      _ => unreachable!(),
    };

    self.context.ty_struct(&fields)
  }

  fn lower_union(&mut self, l_params: &[llvm::Type<'ctx>]) -> Vec<llvm::Type<'ctx>> {
    // NOTE: this special case is needed otherwise bad things (NULL-derefs happen)
    if l_params.len() == 0 {
      return vec![]
    }

    let union_size = l_params
      .iter()
      .map(|ty| self.size_of(*ty))
      .max()
      .unwrap();

    let max_align_ty = l_params
      .iter()
      .cloned()
      .max_by_key(|ty| self.align_of(*ty))
      .unwrap();

    // Start with the highest alignment type then add byte array with
    // the length of the required padding
    let mut l_params = vec![max_align_ty];
    let padding_size = union_size - self.size_of(max_align_ty);
    if padding_size > 0 {
      let int8 = self.context.ty_int8();
      l_params.push(self.context.ty_array(int8, padding_size));
    }

    l_params
  }

  fn align_of(&mut self, ty: llvm::Type<'ctx>) -> usize {
    self.target.align_of(ty)
  }

  fn size_of(&mut self, ty: llvm::Type<'ctx>) -> usize {
    self.target.size_of(ty)
  }

  fn lower_ty(&mut self, ty: &Ty) -> llvm::Type<'ctx> {
    use Ty::*;

    match self.tctx.bound_to_ty(ty) {
      Bool => self.context.ty_int1(),
      Uint8 | Int8 => self.context.ty_int8(),
      Uint16 | Int16 => self.context.ty_int16(),
      Uint32 | Int32 => self.context.ty_int32(),
      Uint64 | Int64 => self.context.ty_int64(),
      Uintn | Intn => self.lower_intn(),
      Float => self.context.ty_float(),
      Double => self.context.ty_double(),
      StructRef(_, id) |
      UnionRef(_, id) |
      EnumRef(_, id) => {
        self.get_type(&id)
      }
      Ptr(..) |
      Func(..) => {
        self.context.ty_ptr()
      }
      Arr(count, element) => {
        let element = self.lower_ty(&element);
        self.context.ty_array(element, count)
      }
      Unit => {
        self.lower_struct(&[])
      }
      Tuple(params) => {
        let l_params: Vec<llvm::Type<'ctx>> = params
          .iter()
          .map(|(_, ty)| self.lower_ty(ty))
          .collect();
        self.lower_struct(&l_params)
      }
      _ => unreachable!()
    }
  }

  fn lower_intn(&mut self) -> llvm::Type<'ctx> {
    // FIXME: make the width of Uintn and Intn per target
    self.context.ty_int64()
  }

  fn lower_struct(&mut self, fields: &[llvm::Type<'ctx>]) -> llvm::Type<'ctx> {
    self.context.ty_struct(fields)
  }

  fn lower_func_ty(&mut self, ty: &Ty) -> llvm::Type<'ctx> {
    let ty = self.tctx.bound_to_ty(ty);
    let (params, va, ret_ty) = ty.unwrap_func();

    let mut l_params = Vec::new();

    params.iter()
      .for_each(|(_, ty)| {
        match self.ty_semantics(ty) {
          Semantics::Void => (),
          Semantics::Value => l_params.push(self.lower_ty(ty)),
          Semantics::Addr => l_params.push(self.context.ty_ptr()),
        }
      });

    match self.ty_semantics(ret_ty) {
      Semantics::Void => {
        let ret_ty = self.context.ty_void();
        self.context.ty_function(ret_ty, &l_params, va)
      }
      Semantics::Value => {
        let ret_ty = self.lower_ty(ret_ty);
        self.context.ty_function(ret_ty, &l_params, va)
      }
      Semantics::Addr => {
        let ret_ty = self.context.ty_void();

        let l_params = concat(
          vec![ self.context.ty_ptr() ],
          l_params
        );

        self.context.ty_function(ret_ty, &l_params, va)
      }
    }
  }

  fn lower_defs(&mut self) {
    // Pass 1: Create LLVM values for each definition
    for (id, def) in self.insts.iter() {
      let l_value = match def {
        Inst::Data { name, init, .. } => {
          let ty = self.const_init_ty(init);
          self.module.add_global(name.borrow_c(), ty)
        }
        Inst::ExternData { name, ty, .. } => {
          let ty = self.lower_ty(ty);
          self.module.add_global(name.borrow_c(), ty)
        }
        Inst::Func { name, ty, .. } |
        Inst::ExternFunc { name, ty, .. } => {
          let ty = self.lower_func_ty(ty);
          self.module.add_function(name.borrow_c(), ty)
        }
        _ => continue
      };

      self.values.insert(id.clone(), l_value);
    }
    // Pass 2: Lower initializers and function bodies
    for (id, def) in self.insts.iter() {
      match def {
        Inst::Data { init, .. }  => {
          let global = self.get_value(id);
          let init = self.lower_const_val(init);
          global.set_initializer(init);
        }
        Inst::Func { params, locals, body: Some(body), .. } => {
          self.l_func = Some(self.get_value(id));

          // Create prelude block for allocas
          self.l_alloca_block = Some(self.new_block());
          self.enter_block(self.l_alloca_block.unwrap());

          // Spill arguments
          let mut lowered_index = if let Semantics::Addr
            = self.ty_semantics(body.ty()) { 1 } else { 0 };

          self.params.clear();
          for (_, ty) in params.iter() {
            let l_alloca = self.allocate_local(ty);
            self.params.push(l_alloca);

            match self.ty_semantics(ty) {
              Semantics::Void => (),
              _ => {
                let param = self.l_func.unwrap().get_param(lowered_index);
                lowered_index += 1;
                self.build_store(ty, l_alloca, param);
              }
            }
          }

          // Allocate locals
          self.locals.clear();
          for (_, ty) in locals.iter() {
            let l_alloca = self.allocate_local(ty);
            self.locals.push(l_alloca);
          }

          // Clear bindings
          self.bindings.clear();

          // Create LLVM function body
          let body_block = self.new_block();
          self.enter_block(body_block);
          let val = self.lower_rvalue(body);
          self.exit_block_ret(body.ty(), val);

          // Add branch from allocas to body
          self.enter_block(self.l_alloca_block.unwrap());
          self.exit_block_br(body_block);
        }
        _ => ()
      }
    }
  }

  /// Lower a constant value into an LLVM constant expression
  fn lower_const_val(&mut self, val: &ConstVal) -> llvm::Value<'ctx> {
    use ConstVal::*;
    match val {
      FuncPtr { id } => self.get_value(id),
      DataPtr { ptr } => self.lower_const_ptr(ptr),
      BoolLit { val } => self.build_bool(*val),
      IntLit { ty, val } => self.build_int(ty, *val as usize),
      FltLit { ty, val } => self.build_flt(ty, *val),
      ArrLit { vals, .. } |
      StructLit { vals, .. } => {
        let fields: Vec<llvm::Value<'ctx>> = vals
          .iter()
          .map(|val| self.lower_const_val(val))
          .collect();
        self.context.const_struct(&fields)
      }
      UnionLit { ty, val, .. } => {
        let ty = self.lower_ty(ty);
        let val = self.lower_const_val(val);

        let int8 = self.context.ty_int8();
        let pad_ty = self.context.ty_array(
          int8, self.size_of(ty) - self.size_of(val.ty()));

        self.context.const_struct(&[
          val,                            // Value
          self.context.const_zeroed(pad_ty)  // Padding
        ])
      }
      CStrLit { val } => {
        self.build_string_lit(val)
      }
    }
  }

  /// Predict the **LLVM** type of the constant expression returned by the above
  fn const_init_ty(&mut self, val: &ConstVal) -> llvm::Type<'ctx> {
    use ConstVal::*;
    match val {
      FuncPtr { .. } |
      DataPtr { .. } |
      CStrLit { .. } => self.context.ty_ptr(),

      BoolLit { .. } => self.context.ty_int1(),

      IntLit { ty, .. } |
      FltLit { ty, .. } => self.lower_ty(ty),

      ArrLit { vals, .. } |
      StructLit { vals, .. } => {
        let l_types: Vec<llvm::Type<'ctx>> = vals
          .iter()
          .map(|val| self.const_init_ty(val))
          .collect();

        self.lower_struct(&l_types)
      }

      UnionLit { ty, val, .. } => {
        let l_union_type = self.lower_ty(ty);
        let union_size = self.size_of(l_union_type);

        let val_ty = self.const_init_ty(val);

        let int8 = self.context.ty_int8();
        let l_types = [
          val_ty, // Value
          self.context.ty_array(int8, union_size - self.size_of(val_ty))  // Padding
        ];

        self.lower_struct(&l_types)
      }
    }
  }

  /// Lower a constant ptr to an LLVM constant pointer
  fn lower_const_ptr(&mut self, ptr: &ConstPtr) -> llvm::Value<'ctx> {
    match ptr {
      ConstPtr::Data { id, ..} => self.get_value(&(*id, vec![])),
      ConstPtr::StrLit { val, ..  } => self.build_string_lit(val),
      ConstPtr::ArrayElement { base, idx, .. } |
      ConstPtr::StructField { base, idx, .. } => {
        let l_ptr = self.lower_const_ptr(base);
        self.build_const_gep(base.ty(), l_ptr, *idx)
      }
      ConstPtr::UnionField { base, .. } => {
        self.lower_const_ptr(base)
      }
    }
  }

  /// Expressions

  fn lower_lvalue(&mut self, lvalue: &LValue) -> llvm::Value<'ctx> {
    match lvalue {
      LValue::DataRef { id, .. } => {
        self.get_value(&(*id, vec![]))
      }
      LValue::ParamRef { index, .. } => {
        self.params[*index]
      }
      LValue::LetRef { index, .. } => {
        self.locals[*index]
      }
      LValue::BindingRef { index, .. } => {
        self.bindings[*index]
      }
      LValue::StrLit { val, .. } => {
        self.build_string_lit(val)
      }
      LValue::ArrayLit { ty, elements, .. } => {
        let storage = self.allocate_local(ty);
        for (index, element) in elements.iter().enumerate() {
          let dest = self.build_gep(ty, storage, index);
          self.lower_rvalue(element)
            .map(|val| self.build_store(element.ty(), dest, val));
        }
        storage
      }
      LValue::UnionLit { ty, field, .. } => {
        let storage = self.allocate_local(ty);
        self.lower_rvalue(field)
          .map(|val| self.build_store(field.ty(), storage, val));
        storage
      }
      LValue::TupleLit { ty, fields, .. } |
      LValue::StructLit { ty, fields, .. } => {
        let storage = self.allocate_local(ty);
        for (index, field) in fields.iter().enumerate() {
          let dest = self.build_gep(ty, storage, index);
          self.lower_rvalue(field)
            .map(|val| self.build_store(field.ty(), dest, val));
        }
        storage
      }
      LValue::UnitVariantLit { ty, index, .. } => {
        let storage = self.allocate_local(ty);
        // Write tag
        let tag = self.build_int(&Ty::Int32, *index);
        self.build_store(&Ty::Int32, storage, tag);
        storage
      }
      LValue::StructVariantLit { ty, index, fields, .. } => {
        let storage = self.allocate_local(ty);
        // Write tag
        let l_tag = self.build_int(&Ty::Int32, *index);
        self.build_store(&Ty::Int32, storage, l_tag);

        // Get data pointer and type
        // NOTE: this is kind of hacky, we should be storing the pre-computed variant types
        //       during enum lowering
        let data_ty = Ty::Tuple(fields
          .iter()
          .map(|field| (RefStr::new(""), field.ty().clone()))
          .collect());
        let data_ptr = self.build_gep(ty, storage, 1);

        for (index, field) in fields.iter().enumerate() {
          let dest = self.build_gep(&data_ty, data_ptr, index);
          self.lower_rvalue(field)
            .map(|val| self.build_store(field.ty(), dest, val));
        }

        storage
      }
      LValue::StruDot { arg, idx, .. } => {
        let ptr = self.lower_lvalue(arg);
        self.build_gep(arg.ty(), ptr, *idx)
      }
      LValue::UnionDot { arg, .. } => {
        self.lower_lvalue(arg)
      }
      LValue::Index { arg, idx, .. } => {
        let base = self.lower_lvalue(arg);
        let index = self.lower_rvalue(idx).unwrap();
        self.build_index(arg.ty(), base, index)
      }
      LValue::Ind { arg, .. } => {
        self.lower_rvalue(arg).unwrap()
      }
    }
  }

  fn lower_rvalue(&mut self, rvalue: &RValue) -> Option<llvm::Value<'ctx>> {
    match rvalue {
      RValue::Unit { .. } => {
        None
      }
      RValue::FuncRef { id, .. } => {
        Some(self.get_value(id))
      }
      RValue::CStr { val, .. } => {
        Some(self.build_string_lit(val))
      }
      RValue::Load { ty, arg, .. } => {
        let addr = self.lower_lvalue(arg);
        self.build_load(ty, addr)
      }
      RValue::Nil { ty, .. } => {
        Some(self.context.const_zeroed(self.lower_ty(ty)))
      }
      RValue::Bool { val, .. } => {
        Some(self.build_bool(*val))
      }
      RValue::Int { ty, val, .. } => {
        Some(self.build_int(ty, *val))
      }
      RValue::Flt { ty, val, .. } => {
        Some(self.build_flt(ty, *val))
      }
      RValue::Call { ty, func, args, .. } => {
        let l_func = self.lower_rvalue(func).unwrap();
        let mut l_args = Vec::new();
        args.iter()
          .for_each(|arg| {
            self.lower_rvalue(arg)
              .map(|val| l_args.push(val));
          });

        match self.ty_semantics(ty) {
          Semantics::Void => {
            self.build_call(func.ty(), l_func, &l_args);
            None
          }
          Semantics::Value => {
            Some(self.build_call(func.ty(), l_func, &l_args))
          }
          Semantics::Addr => {
            let storage = self.allocate_local(ty);
            let args = concat(vec![storage], l_args);
            self.build_call(func.ty(), l_func, &args);
            Some(storage)
          }
        }
      }
      RValue::Adr { arg, .. } => {
        Some(self.lower_lvalue(arg))
      }
      RValue::Un { op, arg, .. } => {
        let val = self.lower_rvalue(arg).unwrap();
        Some(self.build_un(arg.ty(), *op, val))
      }
      RValue::Cast { ty, arg } => {
        let val = self.lower_rvalue(arg).unwrap();
        Some(self.build_cast(ty, arg.ty(), val))
      }
      RValue::Bin { op, lhs, rhs, .. } => {
        let ty = lhs.ty();
        let lhs = self.lower_rvalue(lhs).unwrap();
        let rhs = self.lower_rvalue(rhs).unwrap();
        Some(self.build_bin(ty, *op, lhs, rhs))
      }
      RValue::LNot { .. } |
      RValue::LAnd { .. } |
      RValue::LOr { .. } => {
        // Split based on the boolean value
        let true_block = self.new_block();
        let false_block = self.new_block();
        self.lower_bool(rvalue, true_block, false_block);

        // Both paths will merge in this block
        let phi_block = self.new_block();

        // Jump from true branch to phi block
        self.enter_block(true_block);
        self.exit_block_br(phi_block);

        // Jump from false branch to phi block
        self.enter_block(false_block);
        self.exit_block_br(phi_block);

        // Create phi to choose value
        self.enter_block(phi_block);

        let values = [self.build_bool(true), self.build_bool(false)];
        Some(self.builder.phi(self.context.ty_int1(), &values, &[true_block, false_block]))
      }
      RValue::Block { body, .. } => {
        let mut val = None;
        for expr in body.iter() {
          val = self.lower_rvalue(expr);
        }
        val
      }
      RValue::As { lhs, rhs, .. } => {
        let dest = self.lower_lvalue(lhs);
        self.lower_rvalue(rhs)
          .map(|src| self.build_store(lhs.ty(), dest, src));
        // Void value
        None
      }
      RValue::Rmw { op, lhs, rhs, .. } => {
        // LHS: We need both the address and value
        let dest_addr = self.lower_lvalue(lhs);
        let lhs_val = self.build_load(lhs.ty(), dest_addr).unwrap();
        // RHS: We need only the value
        let rhs_val = self.lower_rvalue(rhs).unwrap();
        // Then we can perform the computation and do the store
        let tmp_val = self.build_bin(lhs.ty(), *op, lhs_val, rhs_val);
        self.build_store(lhs.ty(), dest_addr, tmp_val);
        // Void value
        None
      }
      RValue::Continue { ty, .. } => {
        // Jump to continue point
        self.exit_block_br(*self.continue_to.last().unwrap());
        // Throw away code until next useful location
        let dead_block = self.new_block();
        self.enter_block(dead_block);
        // Unreachable value
        self.build_unreachable(ty)
      }
      RValue::Break { ty, .. } => {
        // Jump to break point
        self.exit_block_br(*self.break_to.last().unwrap());
        // Throw away code until next useful location
        let dead_block = self.new_block();
        self.enter_block(dead_block);
        // Unreachable value
        self.build_unreachable(ty)
      }
      RValue::Return { ty, arg, .. } => {
        let retval = self.lower_rvalue(&*arg);
        self.exit_block_ret(arg.ty(), retval);
        // Throw away code until next useful location
        let dead_block = self.new_block();
        self.enter_block(dead_block);
        // Unreachable value
        self.build_unreachable(ty)
      }
      RValue::Let { index, init, .. } => {
        let l_local = self.locals[*index];
        if let Some(init) = init {
          self.lower_rvalue(init)
            .map(|val| self.build_store(init.ty(), l_local, val));
        }
        // Void value
        None
      }
      RValue::If { ty, cond, tbody, ebody, .. } => {
        let mut then_block = self.new_block();
        let mut else_block = self.new_block();
        let end_block = self.new_block();

        self.lower_bool(cond, then_block, else_block);

        self.enter_block(then_block);
        let then_val = self.lower_rvalue(tbody);
        then_block = self.builder.get_block().unwrap();
        self.exit_block_br(end_block);

        self.enter_block(else_block);
        let else_val = self.lower_rvalue(ebody);
        else_block = self.builder.get_block().unwrap();
        self.exit_block_br(end_block);

        // Merge then and else values in a PHI
        self.enter_block(end_block);
        self.build_phi(ty, &[then_val, else_val], &[then_block, else_block])
      }
      RValue::While { cond, body, .. } => {
        let test_block = self.new_block();
        let body_block = self.new_block();
        let end_block = self.new_block();

        self.exit_block_br(test_block);

        // Initial block is the test as a demorgan expr
        self.enter_block(test_block);
        self.lower_bool(cond, body_block, end_block);

        // Next block is the loop body
        self.enter_block(body_block);
        self.continue_to.push(test_block);
        self.break_to.push(end_block);
        self.lower_rvalue(body);
        self.continue_to.pop();
        self.break_to.pop();
        self.exit_block_br(test_block);

        // End of the loop
        self.enter_block(end_block);

        None
      }
      RValue::Loop { ty, body, .. } => {
        let body_block = self.new_block();
        let end_block = self.new_block();

        self.exit_block_br(body_block);

        // Loop body in one block
        self.enter_block(body_block);
        self.continue_to.push(body_block);
        self.break_to.push(end_block);
        self.lower_rvalue(body);
        self.continue_to.pop();
        self.break_to.pop();
        self.exit_block_br(body_block);

        // End of the loop
        self.enter_block(end_block);

        // FIXME: this might very much need a phi if there are non-void break values
        assert!(matches!(self.ty_semantics(ty), Semantics::Void));
        // Yield void values for now
        None
      }
      RValue::Match { ty, cond, cases, .. } => {
        let start_block = self.builder.get_block().unwrap();
        let addr = self.lower_rvalue(cond).unwrap();

        let end_block = self.new_block();

        // Lower case bodies
        let mut tag_to_block = Vec::new();
        let mut values = Vec::new();
        let mut blocks = Vec::new();

        for (binding, val) in cases.iter() {
          let block = self.new_block();
          tag_to_block.push((
            self.build_int(&Ty::Int32, tag_to_block.len()),
            block
          ));

          self.enter_block(block);
          if let Some(binding) = binding {
            assert_eq!(*binding, self.bindings.len());
            let binding = self.build_gep(cond.ty(), addr, 1);
            self.bindings.push(binding);
          }
          values.push(self.lower_rvalue(val));
          blocks.push(self.builder.get_block().unwrap());
          self.exit_block_br(end_block);
        }

        // There are no cases => we are still in the start block and can just yield None
        if tag_to_block.len() == 0 { return None }

        // Go back to the start block and build a switch for the multi-way branch
        // NOTE: matches are always exhaustive, and LLVM always wants a default case,
        //       thus we just treat the last case as the default
        self.enter_block(start_block);
        let tag = self.build_load(&Ty::Int32, addr).unwrap();
        self.builder.switch(tag, &tag_to_block[..tag_to_block.len() - 1],
                                      tag_to_block[tag_to_block.len() - 1].1);

        // Build PHI to merge case values at the end
        self.enter_block(end_block);
        self.build_phi(ty, &values, &blocks)
      }
    }
  }

  fn lower_bool(&mut self, rvalue: &RValue, next1: llvm::Block<'ctx>, next2: llvm::Block<'ctx>) {
    match rvalue {
      RValue::LNot { arg, .. } => {
        self.lower_bool(arg, next2, next1);
      }
      RValue::LAnd { lhs, rhs, .. } => {
        let mid_block = self.new_block();
        self.lower_bool(lhs, mid_block, next2);
        self.enter_block(mid_block);
        self.lower_bool(rhs, next1, next2);
      }
      RValue::LOr { lhs, rhs, .. } => {
        let mid_block = self.new_block();
        self.lower_bool(lhs, next1, mid_block);
        self.enter_block(mid_block);
        self.lower_bool(rhs, next1, next2);
      }
      _ => {
        let cond = self.lower_rvalue(rvalue).unwrap();
        self.exit_block_cond_br(cond, next1, next2);
      }
    }
  }

  fn get_value(&mut self, id: &(DefId, Vec<Ty>)) -> llvm::Value<'ctx> {
    let tmp = (id.0, self.tctx.canonical_type_args(&id.1));
    *self.values.get(&tmp).unwrap()
  }

  fn build_string_lit(&mut self, data: &[u8]) -> llvm::Value<'ctx> {
    // Borrow checker :/
    let module = &self.module;
    let context = &self.context;
    let index = self.string_lits.len();

    *self.string_lits.raw_entry_mut().from_key(data).or_insert_with(|| {
      // Create name
      let name = RefStr::new(&format!(".str.{}", index));

      // Create global
      // NOTE: +1 for NUL terminator
      let int8 = context.ty_int8();
      let ty = context.ty_array(int8, data.len() + 1);
      let global = module.add_global(name.borrow_c(), ty);

      // Set initializer
      // NOTE: for now these are NUL-terminated
      global.set_initializer(context.const_null_terminated_string(data));

      (data.to_vec(), global)
    }).1
  }

  fn build_bool(&mut self, val: bool) -> llvm::Value<'ctx> {
    self.context.const_int(self.context.ty_int1(), val as _)
  }

  fn build_int(&mut self, ty: &Ty, val: usize) -> llvm::Value<'ctx> {
    self.context.const_int(self.lower_ty(ty), val)
  }

  fn build_flt(&mut self, ty: &Ty, val: f64) -> llvm::Value<'ctx> {
    self.context.const_flt(self.lower_ty(ty), val)
  }

  fn build_unreachable(&mut self, ty: &Ty) -> Option<llvm::Value<'ctx>> {
    match self.ty_semantics(ty) {
      Semantics::Void => None,
      Semantics::Value => {
        let ty = self.lower_ty(ty);
        Some(self.context.const_zeroed(ty))
      }
      Semantics::Addr => {
        let ty = self.context.ty_ptr();
        Some(self.context.const_zeroed(ty))
      }
    }
  }

  fn build_const_gep(&mut self, ty: &Ty, l_ptr: llvm::Value<'ctx>, idx: usize) -> llvm::Value<'ctx> {
    let indices = [
      self.build_int(&Ty::Int8, 0),
      // NOTE: this is not documented in many places, but struct field
      // indices have to be Int32 otherwise LLVM crashes :(
      self.build_int(&Ty::Int32, idx)
    ];

    self.context.const_gep(self.lower_ty(ty), l_ptr, &indices)
  }

  fn allocate_local(&mut self, ty: &Ty) -> llvm::Value<'ctx> {
    let prev = self.builder.get_block().unwrap();
    let ty = self.lower_ty(ty);
    self.enter_block(self.l_alloca_block.unwrap());
    let alloca = self.builder.alloca(ty);
    self.enter_block(prev);
    alloca
  }

  fn new_block(&mut self) -> llvm::Block<'ctx> {
    self.l_func.unwrap().add_block()
  }

  fn enter_block(&mut self, block: llvm::Block<'ctx>) {
    self.builder.set_block(block);
  }

  fn exit_block_br(&mut self, dest: llvm::Block<'ctx>) {
    self.builder.br(dest);
  }

  fn exit_block_cond_br(&mut self, cond: llvm::Value<'ctx>,
                               dest1: llvm::Block<'ctx>,
                               dest2: llvm::Block<'ctx>) {
    self.builder.cond_br(cond, dest1, dest2);
  }

  fn exit_block_ret(&mut self, ty: &Ty, val: Option<llvm::Value<'ctx>>) {
    match self.ty_semantics(ty) {
      Semantics::Void => {
        self.builder.ret_void();
      }
      Semantics::Value => {
        self.builder.ret(val.unwrap());
      }
      Semantics::Addr => {
        self.build_store(ty, self.l_func.unwrap().get_param(0), val.unwrap());
        self.builder.ret_void();
      }
    }
  }

  fn build_load(&mut self, ty: &Ty, ptr: llvm::Value<'ctx>) -> Option<llvm::Value<'ctx>> {
    match self.ty_semantics(ty) {
      Semantics::Void => None,
      Semantics::Addr => Some(ptr),
      Semantics::Value => {
        let ty = self.lower_ty(ty);
        Some(self.builder.load(ty, ptr))
      }
    }
  }

  fn build_store(&mut self, ty: &Ty, ptr: llvm::Value<'ctx>, src: llvm::Value<'ctx>) {
    match self.ty_semantics(ty) {
      Semantics::Void => {}
      Semantics::Addr => {
        let ty = self.lower_ty(ty);
        let align = self.align_of(ty);
        let size = self.size_of(ty);
        let size = self.build_int(&Ty::Int32, size);
        self.builder.memcpy(ptr, src, align, size);
      }
      Semantics::Value => {
        self.builder.store(ptr, src);
      }
    }
  }

  fn ty_semantics(&mut self, ty: &Ty) -> Semantics {
    use Ty::*;

    match self.tctx.bound_to_ty(&ty) {
      Unit => Semantics::Void,
      Bool | Uint8 | Int8 | Uint16 |
      Int16 |Uint32 | Int32 | Uint64 |
      Int64 | Uintn | Intn | Float |
      Double | Ptr(..) | Func(..) => Semantics::Value,
      Arr(..) |
      Tuple(..) |
      StructRef(..) |
      UnionRef(..) |
      EnumRef(..) => Semantics::Addr,
      _ => unreachable!()
    }
  }

  fn build_gep(&mut self, ty: &Ty, base: llvm::Value<'ctx>, index: usize) -> llvm::Value<'ctx> {
    let ty = self.lower_ty(ty);
    let indices = [
      self.build_int(&Ty::Int8, 0),
      // NOTE: this is not documented in many places, but struct field
      // indices have to be Int32 otherwise LLVM crashes :(
      self.build_int(&Ty::Int32, index),
    ];
    self.builder.gep(ty, base, &indices)
  }

  fn build_phi(&mut self, ty: &Ty, values: &[Option<llvm::Value<'ctx>>], blocks: &[llvm::Block<'ctx>]) -> Option<llvm::Value<'ctx>> {
    match self.ty_semantics(ty) {
      Semantics::Void => {
        None
      }
      Semantics::Value => {
        let ty = self.lower_ty(ty);
        let values: Vec<llvm::Value<'ctx>> = values
          .into_iter()
          .map(|x| x.unwrap())
          .collect();
        Some(self.builder.phi(ty, &values, &blocks))
      }
      Semantics::Addr => {
        let ty = self.context.ty_ptr();
        let values: Vec<llvm::Value<'ctx>> = values
          .into_iter()
          .map(|x| x.unwrap())
          .collect();
        Some(self.builder.phi(ty, &values, &blocks))
      }
    }
  }

  fn build_index(&mut self, ty: &Ty, base: llvm::Value<'ctx>, index: llvm::Value<'ctx>) -> llvm::Value<'ctx> {
    let ty = self.lower_ty(ty);
    let indices = [
      self.build_int(&Ty::Int8, 0),
      index
    ];
    self.builder.gep(ty, base, &indices)
  }

  fn build_call(&mut self, func_ty: &Ty, func_ptr: llvm::Value<'ctx>, args: &[llvm::Value<'ctx>]) -> llvm::Value<'ctx> {
    let func_ty = self.lower_func_ty(func_ty);
    self.builder.call(func_ty, func_ptr, args)
  }

  fn build_un(&mut self, ty: &Ty, op: UnOp, arg: llvm::Value<'ctx>) -> llvm::Value<'ctx> {
    use Ty::*;
    use UnOp::*;

    match (op, self.tctx.bound_to_ty(ty)) {
      (UPlus, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn | Float | Double) => {
        arg
      }
      (UMinus, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        self.builder.neg(arg)
      }
      (UMinus, Float | Double) => {
        self.builder.fneg(arg)
      }
      (Not, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        self.builder.not(arg)
      }
      _ => unreachable!()
    }
  }

  fn build_cast(&mut self, dest_ty: &Ty, src_ty: &Ty, val: llvm::Value<'ctx>) -> llvm::Value<'ctx> {
    use Ty::*;

    let lit_dest = self.tctx.bound_to_ty(dest_ty);
    let lit_src = self.tctx.bound_to_ty(src_ty);

    if lit_dest == lit_src { // Nothing to cast
      return val
    }

    let dest_ty = self.lower_ty(&lit_dest);
    let src_ty = self.lower_ty(&lit_src);

    match (&lit_dest, &lit_src) {
      // Pointer/function to pointer/function
      (Ptr(..)|Func(..), Ptr(..)|Func(..)) => {
        val
      }
      // Pointer to integer
      (Uint8 | Uint16 | Uint32 | Uint64 | Uintn | Int8 | Int16 | Int32 | Int64 | Intn, Ptr(..)) => {
        self.builder.ptr_to_int(dest_ty, val)
      }
      // Integer to pointer
      (Ptr(..), Uint8 | Uint16 | Uint32 | Uint64 | Uintn | Int8 | Int16 | Int32 | Int64 | Intn) => {
        self.builder.int_to_ptr(dest_ty, val)
      }
      // Truncate double to float
      (Float, Double) => {
        self.builder.fp_trunc(dest_ty, val)
      }
      // Extend float to double
      (Double, Float) => {
        self.builder.fp_ext(dest_ty, val)
      }
      // unsigned integer to floating point
      (Float | Double, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        self.builder.ui_to_fp(dest_ty, val)
      }
      // signed integer to floating point
      (Float | Double, Int8 | Int16 | Int32 | Int64 | Intn) => {
        self.builder.si_to_fp(dest_ty, val)
      }
      // floating point to unsigned integer
      (Uint8 | Uint16 | Uint32 | Uint64 | Uintn, Float | Double) => {
        self.builder.fp_to_ui(dest_ty, val)
      }
      // floating point to signed integer
      (Int8 | Int16 | Int32 | Int64 | Intn, Float | Double) => {
        self.builder.fp_to_si(dest_ty, val)
      }
      // integer to integer conversions
      (Uint8 | Uint16 | Uint32 | Uint64 | Uintn | Int8 | Int16 | Int32 | Int64 | Intn,
        Uint8 | Uint16 | Uint32 | Uint64 | Uintn | Int8 | Int16 | Int32 | Int64 | Intn) => {
        let dest_size = self.size_of(dest_ty);
        let src_size = self.size_of(src_ty);
        if dest_size == src_size {  // LLVM disregards signedness, so nothing to do
          val
        } else if dest_size < src_size {
          self.builder.trunc(dest_ty, val)
        } else {
          // Choose sign or zero extension based on destination type
          match &lit_dest {
            Uint8 | Uint16 | Uint32 | Uint64 | Uintn => self.builder.zext(dest_ty, val),
            Int8 | Int16 | Int32 | Int64 | Intn => self.builder.sext(dest_ty, val),
            _ => unreachable!()
          }
        }
      }
      _ => unreachable!()
    }
  }

  fn build_bin(&mut self, ty: &Ty, op: BinOp, lhs: llvm::Value<'ctx>, rhs: llvm::Value<'ctx>) -> llvm::Value<'ctx> {
    use Ty::*;
    use BinOp::*;

    match (op, self.tctx.bound_to_ty(ty)) {
      // Integer multiply
      (Mul, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        self.builder.mul(lhs, rhs)
      }
      // Floating point multiply
      (Mul, Float | Double) => {
        self.builder.fmul(lhs, rhs)
      }
      // Unsigned integer divide
      (Div, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        self.builder.udiv(lhs, rhs)
      }
      // Signed integer divide
      (Div, Int8 | Int16 | Int32 | Int64 | Intn) => {
        self.builder.sdiv(lhs, rhs)
      }
      // Floating point divide
      (Div, Float | Double) => {
        self.builder.fdiv(lhs, rhs)
      }
      // Unsigned integer modulo
      (Mod, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        self.builder.urem(lhs, rhs)
      }
      // Signed integer modulo
      (Mod, Int8 | Int16 | Int32 | Int64 | Intn) => {
        self.builder.srem(lhs, rhs)
      }
      // Integer addition
      (Add, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        self.builder.add(lhs, rhs)
      }
      // Floating point addition
      (Add, Float | Double) => {
        self.builder.fadd(lhs, rhs)
      }
      // Integer substraction
      (Sub, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        self.builder.sub(lhs, rhs)
      }
      // Floating point substraction
      (Sub, Float | Double) => {
        self.builder.fsub(lhs, rhs)
      }
      // Left shift
      (Lsh, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        self.builder.shl(lhs, rhs)
      }
      // Unsigned (logical) right shift
      (Rsh, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        self.builder.lshr(lhs, rhs)
      }
      // Signed (arithmetic) right shift
      (Rsh, Int8 | Int16 | Int32 | Int64 | Intn) => {
        self.builder.ashr(lhs, rhs)
      }
      // Bitwise and
      (And, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        self.builder.and(lhs, rhs)
      }
      // Bitwise xor
      (Xor, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        self.builder.xor(lhs, rhs)
      }
      // Bitwise or
      (Or, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        self.builder.or(lhs, rhs)
      }
      // Integer equality and inequality
      (Eq, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        self.builder.icmp(llvm::LLVMIntEQ, lhs, rhs)
      }
      (Ne, Uint8 | Int8 | Uint16 | Int16 | Uint32 | Int32 | Uint64 | Int64 | Uintn | Intn) => {
        self.builder.icmp(llvm::LLVMIntNE, lhs, rhs)
      }
      // Pointer/function pointer comparison
      (Eq | Ne, Ptr(..) | Func(..)) => {
        let ty = self.lower_intn();
        let lhs = self.builder.ptr_to_int(ty, lhs);
        let rhs = self.builder.ptr_to_int(ty, rhs);
        match op {
          Eq => self.builder.icmp(llvm::LLVMIntEQ, lhs, rhs),
          Ne => self.builder.icmp(llvm::LLVMIntNE, lhs, rhs),
          _ => unreachable!()
        }
      }
      // Unsigned integer comparisons
      (Lt, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        self.builder.icmp(llvm::LLVMIntULT, lhs, rhs)
      }
      (Gt, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        self.builder.icmp(llvm::LLVMIntUGT, lhs, rhs)
      }
      (Le, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        self.builder.icmp(llvm::LLVMIntULE, lhs, rhs)
      }
      (Ge, Uint8 | Uint16 | Uint32 | Uint64 | Uintn) => {
        self.builder.icmp(llvm::LLVMIntUGE, lhs, rhs)
      }
      // Signed integer comparisons
      (Lt, Int8 | Int16 | Int32 | Int64 | Intn) => {
        self.builder.icmp(llvm::LLVMIntSLT, lhs, rhs)
      }
      (Gt, Int8 | Int16 | Int32 | Int64 | Intn) => {
        self.builder.icmp(llvm::LLVMIntSGT, lhs, rhs)
      }
      (Le, Int8 | Int16 | Int32 | Int64 | Intn) => {
        self.builder.icmp(llvm::LLVMIntSLE, lhs, rhs)
      }
      (Ge, Int8 | Int16 | Int32 | Int64 | Intn) => {
        self.builder.icmp(llvm::LLVMIntSGE, lhs, rhs)
      }
      // Float Comparisons
      (Eq, Float | Double) => {
        self.builder.fcmp(llvm::LLVMRealOEQ, lhs, rhs)
      }
      (Ne, Float | Double) => {
        self.builder.fcmp(llvm::LLVMRealONE, lhs, rhs)
      }
      (Lt, Float | Double) => {
        self.builder.fcmp(llvm::LLVMRealOLT, lhs, rhs)
      }
      (Gt, Float | Double) => {
        self.builder.fcmp(llvm::LLVMRealOGT, lhs, rhs)
      }
      (Le, Float | Double) => {
        self.builder.fcmp(llvm::LLVMRealOLE, lhs, rhs)
      }
      (Ge, Float | Double) => {
        self.builder.fcmp(llvm::LLVMRealOGE, lhs, rhs)
      }
      _ => unreachable!()
    }
  }
}
