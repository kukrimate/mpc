/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use crate::util::*;
use super::*;
use super::lexer::*;

macro_rules! want {
  ($parser:path,$want:pat,$body:expr) => {
    match &$parser.look(0).1 {
      $want => {
        let tmp = $body;
        $parser.get();
        Ok(tmp)
      }
      _ => {
        let (loc, tok) = $parser.get();
        Err(CompileError::UnexpectedToken(loc, tok))
      }
    }
  }
}

macro_rules! want_with_loc {
  ($parser:path,$want:pat,$body:expr) => {
    match &$parser.look(0) {
      $want => {
        let tmp = $body;
        $parser.get();
        Ok(tmp)
      }
      _ => {
        let (loc, tok) = $parser.get();
        Err(CompileError::UnexpectedToken(loc, tok))
      }
    }
  }
}

macro_rules! maybe_want {
  ($parser:path,$want:pat) => {
    match &$parser.look(0).1 {
      $want => {
        $parser.get();
        true
      }
      _ => false
    }
  }
}

pub struct Parser<'repo> {
  /// Compiler repository
  repo: &'repo mut Repository,
  /// Current module ID
  module_id: DefId,
  /// Lexical analyzer
  lexer: Lexer,
  /// Token buffer
  fifo: FIFO<(SourceLocation, Token), 2>
}

impl<'repo> Parser<'repo> {
  pub fn new(repo: &'repo mut Repository, module_id: DefId, lexer: Lexer) -> Self {
    Parser { repo, module_id, lexer, fifo: FIFO::new() }
  }

  fn fill_nth(&mut self, i: usize) {
    while self.fifo.len() <= i {
      let tmp = self.lexer.next().unwrap(); // FIXME: propagate error
      self.fifo.push(tmp);
    }
  }

  fn look(&mut self, i: usize) -> &(SourceLocation, Token) {
    self.fill_nth(i);
    self.fifo.get(i).unwrap()
  }

  fn get(&mut self) -> (SourceLocation, Token) {
    self.fill_nth(1);
    self.fifo.pop().unwrap()
  }

  pub fn parse(&mut self) -> Result<(), CompileError> {
    // TODO: some sort of error recovery
    loop {
      match self.get() {
        // Read items
        (location, Token::KwType) => self.parse_type(location)?,
        (location, Token::KwStruct) => self.parse_struct(location)?,
        (location, Token::KwUnion) => self.parse_union(location)?,
        (location, Token::KwEnum) => self.parse_enum(location)?,
        (location, Token::KwConst) => self.parse_const(location)?,
        (location, Token::KwData) => self.parse_data(location)?,
        (location, Token::KwFunction) => self.parse_function(location)?,
        (location, Token::KwImport) => self.parse_import(location)?,
        (location, Token::KwExtern) => self.parse_extern(location)?,
        // End of file marker
        (_, Token::EndOfFile) => {
          break
        }
        // Invalid item
        (location, token) => {
          Err(CompileError::UnexpectedToken(location, token))?
        }
      }
    }
    Ok(())
  }

  fn parse_type(&mut self, loc: SourceLocation) -> Result<(), CompileError> {
    // Parse type definition
    let name = want!(self, Token::Ident(name), *name)?;
    let type_params = self.parse_type_params()?;
    want!(self, Token::Eq, ())?;
    let ty = self.parse_ty()?;

    // Add to repository
    let def_id = self.repo.def(Def::Type(TypeDef {
      loc: loc.clone(),
      parent_id: self.module_id,
      name,
      type_params,
      ty
    }));
    self.repo.sym(loc, self.module_id, name, def_id)
  }

  fn parse_struct(&mut self, loc: SourceLocation) -> Result<(), CompileError> {
    // Parse struct definition
    let name = want!(self, Token::Ident(name), *name)?;
    let type_params = self.parse_type_params()?;

    want!(self, Token::LParen, ())?;
    let params = self.parse_params()?;

    // Add to repository
    let def_id = self.repo.def(Def::Struct(StructDef {
      loc: loc.clone(),
      parent_id: self.module_id,
      name,
      type_params,
      params
    }));
    self.repo.sym(loc, self.module_id, name, def_id)
  }

  fn parse_union(&mut self, loc: SourceLocation) -> Result<(), CompileError> {
    // Parse union definition
    let name = want!(self, Token::Ident(name), *name)?;
    let type_params = self.parse_type_params()?;

    want!(self, Token::LParen, ())?;
    let params = self.parse_params()?;

    // Add to repository
    let def_id = self.repo.def(Def::Union(UnionDef {
      loc: loc.clone(),
      parent_id: self.module_id,
      name,
      type_params,
      params
    }));
    self.repo.sym(loc, self.module_id, name, def_id)
  }

  fn parse_enum(&mut self, loc: SourceLocation) -> Result<(), CompileError> {
    // Parse enum definition
    let name = want!(self, Token::Ident(name), *name)?;
    let type_params = self.parse_type_params()?;

    // Add to repository
    let def_id = self.repo.def(Def::Enum(EnumDef {
      loc: loc.clone(),
      parent_id: self.module_id,
      name,
      type_params,
      variants: Vec::new()
    }));
    self.repo.sym(loc, self.module_id, name, def_id)?;

    // Parse variants
    let variants = self.parse_variants(def_id)?;

    // Add variant list to EnumDef
    if let Some(Def::Enum(def)) = self.repo.parsed_defs.get_mut(&def_id) {
      def.variants = variants;
    } else {
      unreachable!()
    };

    Ok(())
  }

  fn parse_variants(&mut self, enum_id: DefId) -> Result<Vec<DefId>, CompileError> {
    let mut variants = Vec::new();

    want!(self, Token::LParen, ())?;
    if maybe_want!(self, Token::RParen) { return Ok(variants) }

    loop {
      let (loc, name) = want_with_loc!(self, (loc, Token::Ident(name)), (loc.clone(), *name))?;
      if maybe_want!(self, Token::LParen) {
        let params = self.parse_params()?;
        let def_id = self.repo.def(Def::StructVariant(StructVariantDef {
          loc: loc.clone(),
          parent_id: enum_id,
          variant_index: variants.len(),
          name,
          params
        }));
        variants.push(def_id);
        self.repo.sym(loc, enum_id, name, def_id)?;
      } else {
        let def_id = self.repo.def(Def::UnitVariant(UnitVariantDef {
          loc: loc.clone(),
          parent_id: enum_id,
          variant_index: variants.len(),
          name
        }));
        variants.push(def_id);
        self.repo.sym(loc, enum_id, name, def_id)?;
      }
      if maybe_want!(self, Token::RParen) { return Ok(variants) }
      want!(self, Token::Comma, ())?;
    }
  }

  fn parse_const(&mut self, loc: SourceLocation) -> Result<(), CompileError> {
    // Parse const definition
    let name = want!(self, Token::Ident(name), *name)?;
    want!(self, Token::Colon, ())?;
    let ty = self.parse_ty()?;
    want!(self, Token::Eq, ())?;
    let val = self.parse_expr()?;

    // Add to repository
    let def_id = self.repo.def(Def::Const(ConstDef {
      loc: loc.clone(),
      parent_id: self.module_id,
      name,
      ty,
      val
    }));
    self.repo.sym(loc, self.module_id, name, def_id)
  }

  fn parse_data(&mut self, loc: SourceLocation) -> Result<(), CompileError> {
    // Parse data definition
    let is_mut = self.parse_is_mut();
    let name = want!(self, Token::Ident(name), *name)?;
    want!(self, Token::Colon, ())?;
    let ty = self.parse_ty()?;
    want!(self, Token::Eq, ())?;
    let init = self.parse_expr()?;

    // Add to repository
    let def_id = self.repo.def(Def::Data(DataDef {
      loc: loc.clone(),
      parent_id: self.module_id,
      name,
      is_mut,
      ty,
      init
    }));
    self.repo.sym(loc, self.module_id, name, def_id)
  }

  fn parse_function(&mut self, loc: SourceLocation) -> Result<(), CompileError> {
    // Parse function definition
    let receiver = self.parse_receiver()?;
    let name = want!(self, Token::Ident(name), *name)?;
    let type_params = self.parse_type_params()?;
    let params = self.parse_param_defs()?;
    let ret_ty = self.parse_ret_ty()?;
    let body_loc = want_with_loc!(self, (loc, Token::LCurly), loc.clone())?;
    let body = self.parse_block_expr(body_loc)?;

    // Add to repository
    let def_id = self.repo.def(Def::Func(FuncDef {
      loc: loc.clone(),
      parent_id: self.module_id,
      name,
      type_params,
      receiver,
      params,
      ret_ty,
      body
    }));

    self.repo.sym(loc, self.module_id, name, def_id)
  }

  fn parse_import(&mut self, loc: SourceLocation) -> Result<(), CompileError> {
    // Imported module name
    let name = want!(self, Token::Ident(name), *name)?;

    // Process import
    self.repo.find_module(loc.clone(), name)
      .and_then(|path| self.repo.parse_module(&path))
      .and_then(|id| self.repo.sym(loc, self.module_id, name, id))
  }

  fn parse_extern(&mut self, _: SourceLocation) -> Result<(), CompileError> {
    want!(self, Token::LCurly, ())?;
    while !maybe_want!(self, Token::RCurly) {
      // Read extern definition
      match self.get() {
        (loc, Token::KwFunction) => {
          let name = want!(self, Token::Ident(name), *name)?;
          let (params, varargs) = self.parse_params_with_varargs()?;
          let ret_ty = self.parse_ret_ty()?;

          let def_id = self.repo.def(Def::ExternFunc(ExternFuncDef {
            loc: loc.clone(),
            parent_id: self.module_id,
            name,
            params,
            varargs,
            ret_ty
          }));
          self.repo.sym(loc, self.module_id, name, def_id)?;
        }
        (loc, Token::KwData) => {
          let is_mut = self.parse_is_mut();
          let name = want!(self, Token::Ident(name), *name)?;
          want!(self, Token::Colon, ())?;
          let ty = self.parse_ty()?;

          let def_id = self.repo.def(Def::ExternData(ExternDataDef {
            loc: loc.clone(),
            parent_id: self.module_id,
            name,
            is_mut,
            ty
          }));
          self.repo.sym(loc, self.module_id, name, def_id)?;
        }
        (location, token) => {
          Err(CompileError::UnexpectedToken(location, token))?
        }
      }
    }
    Ok(())
  }

  fn parse_ty(&mut self) -> Result<Ty, CompileError> {
    match self.get() {
      (loc, Token::TyBool) => Ok(Ty::Bool(loc)),
      (loc, Token::TyUint8) => Ok(Ty::Uint8(loc)),
      (loc, Token::TyInt8) => Ok(Ty::Int8(loc)),
      (loc, Token::TyUint16) => Ok(Ty::Uint16(loc)),
      (loc, Token::TyInt16) => Ok(Ty::Int16(loc)),
      (loc, Token::TyUint32) => Ok(Ty::Uint32(loc)),
      (loc, Token::TyInt32) => Ok(Ty::Int32(loc)),
      (loc, Token::TyUint64) => Ok(Ty::Uint64(loc)),
      (loc, Token::TyInt64) => Ok(Ty::Int64(loc)),
      (loc, Token::TyUintn) => Ok(Ty::Uintn(loc)),
      (loc, Token::TyIntn) => Ok(Ty::Intn(loc)),
      (loc, Token::TyFloat) => Ok(Ty::Float(loc)),
      (loc, Token::TyDouble) => Ok(Ty::Double(loc)),
      (loc, Token::TyFunction) => {
        want!(self, Token::LParen, ())?;
        let params = self.parse_params()?;
        let ret_ty = self.parse_ret_ty()?;
        Ok(Ty::Func(loc, params, Box::new(ret_ty)))
      }
      (loc, Token::Star) => {
        let is_mut = self.parse_is_mut();
        let base_ty = self.parse_ty()?;
        Ok(Ty::Ptr(loc, is_mut, Box::new(base_ty)))
      }
      (loc, Token::LSquare) => {
        let elem_cnt = self.parse_expr()?;
        want!(self, Token::RSquare, ())?;
        let elem_ty = self.parse_ty()?;
        Ok(Ty::Arr(loc, Box::new(elem_cnt), Box::new(elem_ty)))
      }
      (loc, Token::LParen) => {
        if maybe_want!(self, Token::RParen) {
          Ok(Ty::Unit(loc))
        } else {
          let params = self.parse_params()?;
          Ok(Ty::Tuple(loc, params))
        }
      }
      (loc, Token::Ident(name)) => {
        let mut crumbs = vec![name];
        while maybe_want!(self, Token::DColon) {
          crumbs.push(want!(self, Token::Ident(name), *name)?);
        }
        let type_args = self.parse_type_args()?;
        Ok(Ty::Inst(loc, Path(crumbs), type_args))
      }
      (location, token) => {
        Err(CompileError::UnexpectedToken(location, token))
      }
    }
  }

  fn parse_receiver(&mut self) -> Result<Option<(RefStr, IsMut, Ty)>, CompileError> {
    Ok(if maybe_want!(self, Token::LParen) {
      let is_mut = self.parse_is_mut();
      let name = want!(self, Token::Ident(name), *name)?;
      want!(self, Token::Colon, ())?;
      let ty = self.parse_ty()?;
      want!(self, Token::RParen, ())?;
      Some((name, is_mut, ty))
    } else {
      None
    })
  }

  fn parse_type_params(&mut self) -> Result<Vec<RefStr>, CompileError> {
    let mut type_params = Vec::new();
    // No type params
    if !maybe_want!(self, Token::LAngle) { return Ok(type_params) }
    // Empty type params
    if maybe_want!(self, Token::RAngle) { return Ok(type_params) }
    // Read list
    loop {
      // Read type param
      type_params.push(want!(self, Token::Ident(name), *name)?);
      // Check for end of list
      if maybe_want!(self, Token::RAngle) { return Ok(type_params) }
      want!(self, Token::Comma, ())?;
    }
  }

  fn parse_type_args(&mut self) -> Result<Vec<Ty>, CompileError> {
    let mut type_args = Vec::new();
    // No type args
    if !maybe_want!(self, Token::LAngle) { return Ok(type_args) }
    // Empty type args
    if maybe_want!(self, Token::RAngle) { return Ok(type_args) }
    // Read list
    loop {
      // Read type arg
      type_args.push(self.parse_ty()?);
      // Check for end of list
      if maybe_want!(self, Token::RAngle) { return Ok(type_args) }
      want!(self, Token::Comma, ())?;
    }
  }

  fn parse_params(&mut self) -> Result<Vec<(RefStr, Ty)>, CompileError> {
    let mut params = Vec::new();

    // Empty params
    if maybe_want!(self, Token::RParen) { return Ok(params) }

    // Read list
    loop {
      // Read parameter
      let name = want!(self, Token::Ident(name), *name)?;
      want!(self, Token::Colon, ())?;
      let ty = self.parse_ty()?;
      params.push((name, ty));
      // Check for end of list
      if maybe_want!(self, Token::RParen) { break }
      want!(self, Token::Comma, ())?;
    }
    Ok(params)
  }

  fn parse_params_with_varargs(&mut self) -> Result<(Vec<(RefStr, Ty)>, bool), CompileError> {
    let mut params = Vec::new();
    let mut varargs = false;

    want!(self, Token::LParen, ())?;

    // Empty params
    if maybe_want!(self, Token::RParen) { return Ok((params, varargs)) }

    // Read list
    loop {
      // Read parameter
      let name = want!(self, Token::Ident(name), *name)?;
      want!(self, Token::Colon, ())?;
      let ty = self.parse_ty()?;
      params.push((name, ty));
      // Check for end of list
      if maybe_want!(self, Token::RParen) { break }
      want!(self, Token::Comma, ())?;
      // Check for varargs
      if maybe_want!(self, Token::Varargs) {
        want!(self, Token::RParen, ())?;
        varargs = true;
        break;
      }
    }

    Ok((params, varargs))
  }

  fn parse_param_defs(&mut self) -> Result<Vec<(RefStr, IsMut, Ty)>, CompileError> {
    let mut param_defs = Vec::new();

    want!(self, Token::LParen, ())?;

    // Empty params
    if maybe_want!(self, Token::RParen) { return Ok(param_defs) }

    // Read list
    loop {
      // Read parameter definition
      let is_mut = self.parse_is_mut();
      let name = want!(self, Token::Ident(name), *name)?;
      want!(self, Token::Colon, ())?;
      let ty = self.parse_ty()?;
      param_defs.push((name, is_mut, ty));
      // Check for end of list
      if maybe_want!(self, Token::RParen) { break }
      want!(self, Token::Comma, ())?;
    }
    Ok(param_defs)
  }

  fn parse_ret_ty(&mut self) -> Result<Ty, CompileError> {
    if maybe_want!(self, Token::Arrow) {
      self.parse_ty()
    } else {
      // NOTE: any `loc` for this is questionable
      Ok(Ty::Unit(self.look(0).0.clone()))
    }
  }

  fn parse_is_mut(&mut self) -> IsMut {
    if maybe_want!(self, Token::KwMut) {
      IsMut::Yes
    } else {
      IsMut::No
    }
  }

  fn parse_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    let expr = self.parse_nonassign_expr()?;
    if maybe_want!(self, Token::Eq) {
      Ok(Expr::As(loc,
                  Box::new(expr),
                  Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwMul) {
      Ok(Expr::Rmw(loc,
                   BinOp::Mul,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwDiv) {
      Ok(Expr::Rmw(loc,
                   BinOp::Div,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwMod) {
      Ok(Expr::Rmw(loc,
                   BinOp::Mod,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwAdd) {
      Ok(Expr::Rmw(loc,
                   BinOp::Add,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwSub) {
      Ok(Expr::Rmw(loc,
                   BinOp::Sub,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwLShift) {
      Ok(Expr::Rmw(loc,
                   BinOp::Lsh,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwRShift) {
      Ok(Expr::Rmw(loc,
                   BinOp::Rsh,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwBitAnd) {
      Ok(Expr::Rmw(loc,
                   BinOp::And,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwBitXor) {
      Ok(Expr::Rmw(loc,
                   BinOp::Xor,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwBitOr) {
      Ok(Expr::Rmw(loc,
                   BinOp::Or,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else {
      Ok(expr)
    }
  }

  fn parse_nonassign_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    if maybe_want!(self, Token::LCurly) {
      self.parse_block_expr(loc)
    } else if maybe_want!(self, Token::KwIf) {
      self.parse_if_expr(loc)
    } else if maybe_want!(self, Token::KwLoop) {
      self.parse_loop_expr(loc)
    } else if maybe_want!(self, Token::KwWhile) {
      self.parse_while_expr(loc)
    } else if maybe_want!(self, Token::KwMatch) {
      self.parse_match_expr(loc)
    } else if maybe_want!(self, Token::KwLet) {
      let is_mut = self.parse_is_mut();
      let name = want!(self, Token::Ident(name), *name)?;
      let ty = if maybe_want!(self, Token::Colon) {
        Some(self.parse_ty()?)
      } else {
        None
      };
      want!(self, Token::Eq, ())?;
      let init = if maybe_want!(self, Token::Excl) {
        None
      } else {
        Some(Box::new(self.parse_expr()?))
      };
      Ok(Expr::Let(loc, name, is_mut, ty, init))
    } else if maybe_want!(self, Token::KwContinue) {
      Ok(Expr::Continue(loc))
    } else if maybe_want!(self, Token::KwBreak) {
      // NOTE: actually verify that these are the only valid terminators
      if let (_, Token::Comma | Token::Semi | Token::RAngle | Token::RSquare | Token::RCurly) = self.look(0) {
        // NOTE: the Expr::Unit here has no actual location
        Ok(Expr::Break(loc.clone(), Box::new(Expr::Unit(loc))))
      } else {
        Ok(Expr::Break(loc, Box::new(self.parse_expr()?)))
      }
    } else if maybe_want!(self, Token::KwReturn) {
      if let (_, Token::Comma | Token::Semi | Token::RAngle | Token::RSquare | Token::RCurly) = self.look(0) {
        Ok(Expr::Return(loc.clone(), Box::new(Expr::Unit(loc))))
      } else {
        Ok(Expr::Return(loc, Box::new(self.parse_expr()?)))
      }
    } else {
      self.parse_lor_expr()
    }
  }

  fn parse_block_expr(&mut self, loc: SourceLocation) -> Result<Expr, CompileError> {
    // Empty block
    if maybe_want!(self, Token::RCurly) { return Ok(Expr::Unit(loc)) }
    // Parse item list
    let mut exprs = Vec::new();
    loop {
      // FIXME: this is kind of hacky
      let mut had_semi = false;
      let semi_loc = self.look(0).0.clone();
      while maybe_want!(self, Token::Semi) {
        had_semi = true;
      }
      if maybe_want!(self, Token::RCurly) {
        if had_semi { exprs.push(Expr::Unit(semi_loc)); }
        break
      }
      exprs.push(self.parse_expr()?);
    }
    Ok(Expr::Block(loc, exprs))
  }

  fn parse_if_expr(&mut self, loc: SourceLocation) -> Result<Expr, CompileError> {
    let cond = self.parse_expr()?;

    // True body
    let tbody_loc = self.look(0).0.clone();
    want!(self, Token::LCurly, ())?;
    let tbody = self.parse_block_expr(tbody_loc)?;

    // Else body
    let ebody = if maybe_want!(self, Token::KwElse) {
      let ebody_loc = self.look(0).0.clone();
      if maybe_want!(self, Token::KwIf) {
        self.parse_if_expr(ebody_loc)?
      } else {
        want!(self, Token::LCurly, ())?;
        self.parse_block_expr(ebody_loc)?
      }
    } else {
      // NOTE: this has no real location again
      Expr::Unit(loc.clone())
    };

    Ok(Expr::If(loc.clone(), Box::new(cond), Box::new(tbody), Box::new(ebody)))
  }

  fn parse_loop_expr(&mut self, loc: SourceLocation) -> Result<Expr, CompileError> {
    let body_loc = want_with_loc!(self, (loc, Token::LCurly), loc.clone())?;
    let body = self.parse_block_expr(body_loc)?;
    Ok(Expr::Loop(loc, Box::new(body)))
  }

  fn parse_while_expr(&mut self, loc: SourceLocation) -> Result<Expr, CompileError> {
    let cond = self.parse_expr()?;

    let body_loc = want_with_loc!(self, (loc, Token::LCurly), loc.clone())?;
    let body = self.parse_block_expr(body_loc)?;

    Ok(Expr::While(loc, Box::new(cond), Box::new(body)))
  }

  fn parse_match_expr(&mut self, loc: SourceLocation) -> Result<Expr, CompileError> {
    let cond = self.parse_expr()?;
    want!(self, Token::LCurly, ())?;
    let pattern_list = self.parse_pattern_list()?;
    Ok(Expr::Match(loc, Box::new(cond), pattern_list))
  }

  fn parse_pattern_list(&mut self) -> Result<Vec<(Pattern, Expr)>, CompileError> {
    let mut pattern_list = Vec::new();
    // Empty list
    if maybe_want!(self, Token::RCurly) { return Ok(pattern_list) }
    // Read cases
    loop {
      pattern_list.push(self.parse_pattern()?);
      if maybe_want!(self, Token::RCurly) { break }
      want!(self, Token::Comma, ())?;
    }
    Ok(pattern_list)
  }

  fn parse_pattern(&mut self) -> Result<(Pattern, Expr), CompileError> {
    let pattern = if maybe_want!(self, Token::Star) {
      Pattern::Any
    } else {
      let name = want!(self, Token::Ident(name), *name)?;
      if maybe_want!(self, Token::LParen) {
        Pattern::Struct(name, self.parse_pattern_field_list()?)
      } else {
        Pattern::Unit(name)
      }
    };
    want!(self, Token::FatArrow, ())?;
    Ok((pattern, self.parse_expr()?))
  }

  fn parse_pattern_field_list(&mut self) -> Result<Vec<RefStr>, CompileError> {
    let mut fields = Vec::new();
    if maybe_want!(self, Token::RParen) { return Ok(fields) }
    loop {
      fields.push(want!(self, Token::Ident(name), *name)?);
      if maybe_want!(self, Token::RParen) { return Ok(fields) }
      want!(self, Token::Comma, ())?;
    }
  }

  fn parse_lor_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    let mut expr = self.parse_land_expr()?;
    while maybe_want!(self, Token::LogicOr) {
      expr = Expr::LOr(loc.clone(),
                       Box::new(expr),
                        Box::new(self.parse_land_expr()?));
    }
    Ok(expr)
  }

  fn parse_land_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    let mut expr = self.parse_cmp_expr()?;
    while maybe_want!(self, Token::LogicAnd) {
      expr = Expr::LAnd(loc.clone(),
                        Box::new(expr),
                        Box::new(self.parse_cmp_expr()?));
    }
    Ok(expr)
  }

  fn parse_cmp_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    let expr = self.parse_or_expr()?;
    if maybe_want!(self, Token::EqEq) {
      Ok(Expr::Bin(loc,
                   BinOp::Eq,
                   Box::new(expr),
                   Box::new(self.parse_or_expr()?)))
    } else if maybe_want!(self, Token::ExclEq) {
      Ok(Expr::Bin(loc,
                   BinOp::Ne,
                   Box::new(expr),
                   Box::new(self.parse_or_expr()?)))
    } else if maybe_want!(self, Token::LAngle) {
      Ok(Expr::Bin(loc,
                   BinOp::Lt,
                   Box::new(expr),
                   Box::new(self.parse_or_expr()?)))
    } else if maybe_want!(self, Token::RAngle) {
      Ok(Expr::Bin(loc,
                   BinOp::Gt,
                   Box::new(expr),
                   Box::new(self.parse_or_expr()?)))
    } else if maybe_want!(self, Token::LessEq) {
      Ok(Expr::Bin(loc,
                   BinOp::Le,
                   Box::new(expr),
                   Box::new(self.parse_or_expr()?)))
    } else if maybe_want!(self, Token::GreaterEq) {
      Ok(Expr::Bin(loc,
                   BinOp::Ge,
                   Box::new(expr),
                   Box::new(self.parse_or_expr()?)))
    } else {
      Ok(expr)
    }
  }

  fn parse_or_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    let mut expr = self.parse_xor_expr()?;
    while maybe_want!(self, Token::Pipe) {
      expr = Expr::Bin(loc.clone(),
                       BinOp::Or,
                       Box::new(expr),
                       Box::new(self.parse_xor_expr()?));
    }
    Ok(expr)
  }

  fn parse_xor_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    let mut expr = self.parse_and_expr()?;
    while maybe_want!(self, Token::Caret) {
      expr = Expr::Bin(loc.clone(),
                       BinOp::Xor,
                       Box::new(expr),
                       Box::new(self.parse_and_expr()?));
    }
    Ok(expr)
  }

  fn parse_and_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    let mut expr = self.parse_shift_expr()?;
    while maybe_want!(self, Token::Amp) {
      expr = Expr::Bin(loc.clone(),
                       BinOp::And,
                       Box::new(expr),
                       Box::new(self.parse_shift_expr()?));
    }
    Ok(expr)
  }

  fn parse_shift_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    let mut expr = self.parse_add_expr()?;
    loop {
      if maybe_want!(self, Token::LShift) {
        expr = Expr::Bin(loc.clone(),
                         BinOp::Lsh,
                         Box::new(expr),
                         Box::new(self.parse_add_expr()?));
      } else if maybe_want!(self, Token::RShift) {
        expr = Expr::Bin(loc.clone(),
                         BinOp::Rsh,
                         Box::new(expr),
                         Box::new(self.parse_add_expr()?));
      } else {
        break
      }
    }
    Ok(expr)
  }

  fn parse_add_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    let mut expr = self.parse_mul_expr()?;
    loop {
      if maybe_want!(self, Token::Plus) {
        expr = Expr::Bin(loc.clone(),
                         BinOp::Add,
                         Box::new(expr),
                         Box::new(self.parse_mul_expr()?));
      } else if maybe_want!(self, Token::Minus) {
        expr = Expr::Bin(loc.clone(),
                         BinOp::Sub,
                         Box::new(expr),
                         Box::new(self.parse_mul_expr()?));
      } else {
        break
      }
    }
    Ok(expr)
  }

  fn parse_mul_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    let mut expr = self.parse_cast_expr()?;
    loop {
      if maybe_want!(self, Token::Star) {
        expr = Expr::Bin(loc.clone(),
                         BinOp::Mul,
                         Box::new(expr),
                         Box::new(self.parse_cast_expr()?));
      } else if maybe_want!(self, Token::Slash) {
        expr = Expr::Bin(loc.clone(),
                         BinOp::Div,
                         Box::new(expr),
                         Box::new(self.parse_cast_expr()?));
      } else if maybe_want!(self, Token::Percent) {
        expr = Expr::Bin(loc.clone(),
                         BinOp::Mod,
                         Box::new(expr),
                         Box::new(self.parse_cast_expr()?));
      } else {
        break
      }
    }
    Ok(expr)
  }

  fn parse_cast_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    let mut expr = self.parse_pre_expr()?;
    while maybe_want!(self, Token::KwAs) {
      want!(self, Token::LAngle, ())?;
      expr = Expr::Cast(loc.clone(), Box::new(expr), self.parse_ty()?);
      want!(self, Token::RAngle, ())?;
    }
    Ok(expr)
  }

  fn parse_pre_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    if maybe_want!(self, Token::Amp) {
      Ok(Expr::Adr(loc, Box::new(self.parse_pre_expr()?)))
    } else if maybe_want!(self, Token::Star) {
      Ok(Expr::Ind(loc, Box::new(self.parse_pre_expr()?)))
    } else if maybe_want!(self, Token::Plus) {
      Ok(Expr::Un(loc, UnOp::UPlus, Box::new(self.parse_pre_expr()?)))
    } else if maybe_want!(self, Token::Minus) {
      Ok(Expr::Un(loc, UnOp::UMinus, Box::new(self.parse_pre_expr()?)))
    }  else if maybe_want!(self, Token::Tilde) {
      Ok(Expr::Un(loc, UnOp::Not, Box::new(self.parse_pre_expr()?)))
    }  else if maybe_want!(self, Token::Excl) {
      Ok(Expr::LNot(loc, Box::new(self.parse_pre_expr()?)))
    }else {
      self.parse_post_expr()
    }
  }

  fn parse_post_expr(&mut self) -> Result<Expr, CompileError> {
    let loc = self.look(0).0.clone();
    let mut expr = self.parse_prim_expr()?;
    loop {
      if maybe_want!(self, Token::Dot) {
        let field = want!(self, Token::Ident(name), *name)?;
        expr = Expr::Dot(loc.clone(), Box::new(expr), field);
      } else if maybe_want!(self, Token::LParen) {
        let args = self.parse_argument_list()?;
        expr = Expr::Call(loc.clone(), Box::new(expr), args);
      } else if maybe_want!(self, Token::LSquare) {
        let index = self.parse_expr()?;
        want!(self, Token::RSquare, ())?;
        expr = Expr::Index(loc.clone(), Box::new(expr), Box::new(index));
      } else {
        return Ok(expr)
      }
    }
  }

  fn parse_argument_list(&mut self) -> Result<Vec<(RefStr, Expr)>, CompileError> {
    let mut arguments = Vec::new();

    // Empty list
    if maybe_want!(self, Token::RParen) { return Ok(arguments) }

    // Read elements
    loop {
      if let ((_, Token::Ident(name)), (_, Token::Colon)) = (self.look(0).clone(), self.look(1)) {
        self.get();
        self.get();
        arguments.push((name, self.parse_expr()?));
      } else {
        arguments.push((RefStr::new(""), self.parse_expr()?));
      }

      if maybe_want!(self, Token::RParen) { break }
      want!(self, Token::Comma, ())?;
    }

    Ok(arguments)
  }

  fn parse_prim_expr(&mut self) -> Result<Expr, CompileError> {
    match self.get() {
      (loc, Token::LParen) => {
        if maybe_want!(self, Token::RParen) { // Unit
          Ok(Expr::Unit(loc))
        } else if let ((_, Token::Ident(..)), (_, Token::Colon)) = (self.look(0).clone(), self.look(1)) {
          Ok(Expr::Tuple(loc, self.parse_tuple_field_list()?))
        } else {
          let expr = self.parse_expr()?;
          want!(self, Token::RParen, ())?;
          Ok(expr)
        }
      }
      (loc, Token::Ident(s)) => {
        let mut crumbs = vec![s];
        let mut type_args = Vec::new();
        while maybe_want!(self, Token::DColon) {
          if let (_, Token::LAngle) = self.look(0) {
            type_args = self.parse_type_args()?;
            break;
          }
          crumbs.push(want!(self, Token::Ident(name), *name)?);
        }
        Ok(Expr::Inst(loc, Path(crumbs), type_args))
      }
      (loc, Token::KwNil) => {
        Ok(Expr::Nil(loc))
      }
      (loc, Token::KwTrue) => {
        Ok(Expr::Bool(loc, true))
      }
      (loc, Token::KwFalse) => {
        Ok(Expr::Bool(loc, false))
      }
      (loc, Token::LSquare) => {
        Ok(Expr::Arr(loc, self.parse_array_element_list()?))
      }
      (loc, Token::IntLit(val)) => {
        Ok(Expr::Int(loc, val))
      }
      (loc, Token::FltLit(val)) => {
        Ok(Expr::Flt(loc, val))
      }
      (loc, Token::StrLit(val)) => {
        Ok(Expr::Str(loc, val))
      }
      (loc, Token::CStrLit(val)) => {
        Ok(Expr::CStr(loc, val))
      }
      (location, token) => {
        Err(CompileError::UnexpectedToken(location, token))
      }
    }
  }

  fn parse_tuple_field_list(&mut self) -> Result<Vec<(RefStr, Expr)>, CompileError> {
    let mut fields = Vec::new();

    // Empty list
    if maybe_want!(self, Token::RParen) { return Ok(fields) }

    // Read elements
    loop {
      let name = want!(self, Token::Ident(name), *name)?;
      want!(self, Token::Colon, ())?;
      fields.push((name, self.parse_expr()?));

      if maybe_want!(self, Token::RParen) { break }
      want!(self, Token::Comma, ())?;
    }

    Ok(fields)
  }

  fn parse_array_element_list(&mut self) -> Result<Vec<Expr>, CompileError> {
    let mut elements = Vec::new();
    // Empty list
    if maybe_want!(self, Token::RSquare) { return Ok(elements) }
    // Read elements
    loop {
      elements.push(self.parse_expr()?);
      if maybe_want!(self, Token::RSquare) { break }
      want!(self, Token::Comma, ())?;
    }
    Ok(elements)
  }
}
