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
        Err(Error::UnexpectedToken(loc, tok))
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

pub struct Parser<'repo, 'input> {
  /// Compiler repository
  repo: &'repo mut Repository,
  /// Lexical analyzer
  lexer: Lexer<'input>,
  /// Token buffer
  fifo: FIFO<(Location, Token), 2>
}

impl<'repo, 'input> Parser<'repo, 'input> {
  pub fn new(repo: &'repo mut Repository, lexer: Lexer<'input>) -> Self {
    Parser { repo, lexer, fifo: FIFO::new() }
  }

  fn fill_nth(&mut self, i: usize) {
    while self.fifo.len() <= i {
      let location = self.lexer.location();
      let token = self.lexer.token().unwrap(); // FIXME: propagate error
      self.fifo.push((location, token));
    }
  }

  fn look(&mut self, i: usize) -> &(Location, Token) {
    self.fill_nth(i);
    self.fifo.get(i).unwrap()
  }

  fn get(&mut self) -> (Location, Token) {
    self.fill_nth(1);
    self.fifo.pop().unwrap()
  }

  pub fn parse(&mut self) -> Result<(), Error> {
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
          Err(Error::UnexpectedToken(location, token))?
        }
      }
    }
    Ok(())
  }

  fn parse_type(&mut self, location: Location) -> Result<(), Error> {
    // Parse type definition
    let name = want!(self, Token::Ident(name), *name)?;
    want!(self, Token::Eq, ())?;
    let ty = self.parse_ty()?;

    // Add to repository
    let def_id = self.repo.def(Def::Type(TypeDef { name, ty }));
    self.repo.sym(location, name, def_id)
  }

  fn parse_struct(&mut self, location: Location) -> Result<(), Error> {
    // Parse struct definition
    let name = want!(self, Token::Ident(name), *name)?;
    let type_params = self.parse_type_params()?;

    want!(self, Token::LParen, ())?;
    let params = self.parse_params()?;

    // Add to repository
    let def_id = self.repo.def(Def::Struct(StructDef { name, type_params, params }));
    self.repo.sym(location, name, def_id)
  }

  fn parse_union(&mut self, location: Location) -> Result<(), Error> {
    // Parse union definition
    let name = want!(self, Token::Ident(name), *name)?;
    let type_params = self.parse_type_params()?;

    want!(self, Token::LParen, ())?;
    let params = self.parse_params()?;

    // Add to repository
    let def_id = self.repo.def(Def::Union(UnionDef { name, type_params, params }));
    self.repo.sym(location, name, def_id)
  }

  fn parse_enum(&mut self, location: Location) -> Result<(), Error> {
    // Parse enum definition
    let name = want!(self, Token::Ident(name), *name)?;
    let type_params = self.parse_type_params()?;
    let variants = self.parse_variants()?;

    // Add to repository
    let def_id = self.repo.def(Def::Enum(EnumDef { name, type_params, variants: variants.clone() }));
    self.repo.sym(location, name, def_id)?;

    // Add variants to repository
    self.repo.current_scope.push(def_id);
    for (index, variant) in variants.iter().enumerate() {
      match variant {
        Variant::Unit(name) |
        Variant::Struct(name, ..) => {
          let variant_id = self.repo.def(Def::Variant(VariantDef {
            name: *name, parent_enum: def_id, variant_index: index
          }));
          self.repo.sym(location, *name, variant_id)?;
        }
      }
    }
    self.repo.current_scope.pop();

    Ok(())
  }

  fn parse_variants(&mut self) -> Result<Vec<Variant>, Error> {
    let mut variants = Vec::new();

    want!(self, Token::LParen, ())?;
    if maybe_want!(self, Token::RParen) { return Ok(variants) }

    loop {
      let name = want!(self, Token::Ident(name), *name)?;
      if maybe_want!(self, Token::LParen) {
        variants.push(Variant::Struct(name, self.parse_params()?));
      } else {
        variants.push(Variant::Unit(name));
      }
      if maybe_want!(self, Token::RParen) { break }
      want!(self, Token::Comma, ())?;
    }

    Ok(variants)
  }

  fn parse_const(&mut self, location: Location) -> Result<(), Error> {
    // Parse const definition
    let name = want!(self, Token::Ident(name), *name)?;
    want!(self, Token::Colon, ())?;
    let ty = self.parse_ty()?;
    want!(self, Token::Eq, ())?;
    let val = self.parse_expr()?;

    // Add to repository
    let def_id = self.repo.def(Def::Const(ConstDef { name, ty, val }));
    self.repo.sym(location, name, def_id)
  }

  fn parse_data(&mut self, location: Location) -> Result<(), Error> {
    // Parse data definition
    let is_mut = self.parse_is_mut();
    let name = want!(self, Token::Ident(name), *name)?;
    want!(self, Token::Colon, ())?;
    let ty = self.parse_ty()?;
    want!(self, Token::Eq, ())?;
    let init = self.parse_expr()?;

    // Add to repository
    let def_id = self.repo.def(Def::Data(DataDef { name, is_mut, ty, init }));
    self.repo.sym(location, name, def_id)
  }

  fn parse_function(&mut self, location: Location) -> Result<(), Error> {
    // Parse function definition
    let name = want!(self, Token::Ident(name), *name)?;
    let type_params = self.parse_type_params()?;
    let params = self.parse_param_defs()?;
    let ret_ty = self.parse_ret_ty()?;
    want!(self, Token::LCurly, ())?;
    let body = self.parse_block_expr()?;

    // Add to repository
    let def_id = self.repo.def(Def::Func(FuncDef { name, type_params, params, ret_ty, body }));
    self.repo.sym(location, name, def_id)
  }

  fn parse_import(&mut self, location: Location) -> Result<(), Error> {
    // Imported module name
    let name = want!(self, Token::Ident(name), *name)?;

    // Process import
    self.repo.find_module(location, name)
      .and_then(|path| self.repo.parse_module(&path))
      .and_then(|id| self.repo.sym(location, name, id))
  }

  fn parse_extern(&mut self, _: Location) -> Result<(), Error> {
    want!(self, Token::LCurly, ())?;
    while !maybe_want!(self, Token::RCurly) {
      // Read extern definition
      match self.get() {
        (location, Token::KwFunction) => {
          let name = want!(self, Token::Ident(name), *name)?;
          let (params, varargs) = self.parse_params_with_varargs()?;
          let ret_ty = self.parse_ret_ty()?;

          let def_id = self.repo.def(Def::ExternFunc(ExternFuncDef { name, params, varargs, ret_ty }));
          self.repo.sym(location, name, def_id)?;
        }
        (location, Token::KwData) => {
          let is_mut = self.parse_is_mut();
          let name = want!(self, Token::Ident(name), *name)?;
          want!(self, Token::Colon, ())?;
          let ty = self.parse_ty()?;

          let def_id = self.repo.def(Def::ExternData(ExternDataDef { name, is_mut, ty }));
          self.repo.sym(location, name, def_id)?;
        }
        (location, token) => {
          Err(Error::UnexpectedToken(location, token))?
        }
      }
    }
    Ok(())
  }

  fn parse_ty(&mut self) -> Result<Ty, Error> {
    match self.get() {
      (_, Token::TyBool) => Ok(Ty::Bool),
      (_, Token::TyUint8) => Ok(Ty::Uint8),
      (_, Token::TyInt8) => Ok(Ty::Int8),
      (_, Token::TyUint16) => Ok(Ty::Uint16),
      (_, Token::TyInt16) => Ok(Ty::Int16),
      (_, Token::TyUint32) => Ok(Ty::Uint32),
      (_, Token::TyInt32) => Ok(Ty::Int32),
      (_, Token::TyUint64) => Ok(Ty::Uint64),
      (_, Token::TyInt64) => Ok(Ty::Int64),
      (_, Token::TyUintn) => Ok(Ty::Uintn),
      (_, Token::TyIntn) => Ok(Ty::Intn),
      (_, Token::TyFloat) => Ok(Ty::Float),
      (_, Token::TyDouble) => Ok(Ty::Double),
      (_, Token::TyFunction) => {
        want!(self, Token::LParen, ())?;
        let params = self.parse_params()?;
        let ret_ty = self.parse_ret_ty()?;
        Ok(Ty::Func(params, Box::new(ret_ty)))
      }
      (_, Token::Star) => {
        let is_mut = self.parse_is_mut();
        let base_ty = self.parse_ty()?;
        Ok(Ty::Ptr(is_mut, Box::new(base_ty)))
      }
      (_, Token::LSquare) => {
        let elem_cnt = self.parse_expr()?;
        want!(self, Token::RSquare, ())?;
        let elem_ty = self.parse_ty()?;
        Ok(Ty::Arr(Box::new(elem_cnt), Box::new(elem_ty)))
      }
      (_, Token::LParen) => {
        if maybe_want!(self, Token::RParen) {
          Ok(Ty::Unit)
        } else {
          let params = self.parse_params()?;
          Ok(Ty::Tuple(params))
        }
      }
      (_, Token::Ident(name)) => {
        let mut crumbs = vec![name];
        while maybe_want!(self, Token::DColon) {
          crumbs.push(want!(self, Token::Ident(name), *name)?);
        }
        let type_args = self.parse_type_args()?;
        Ok(Ty::Inst(Path(crumbs), type_args))
      }
      (location, token) => {
        Err(Error::UnexpectedToken(location, token))
      }
    }
  }

  fn parse_type_params(&mut self) -> Result<Vec<RefStr>, Error> {
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

  fn parse_type_args(&mut self) -> Result<Vec<Ty>, Error> {
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

  fn parse_params(&mut self) -> Result<Vec<(RefStr, Ty)>, Error> {
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

  fn parse_params_with_varargs(&mut self) -> Result<(Vec<(RefStr, Ty)>, bool), Error> {
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

  fn parse_param_defs(&mut self) -> Result<Vec<(RefStr, IsMut, Ty)>, Error> {
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

  fn parse_ret_ty(&mut self) -> Result<Ty, Error> {
    if maybe_want!(self, Token::Arrow) {
      self.parse_ty()
    } else {
      Ok(Ty::Unit)
    }
  }

  fn parse_is_mut(&mut self) -> IsMut {
    if maybe_want!(self, Token::KwMut) {
      IsMut::Yes
    } else {
      IsMut::No
    }
  }

  fn parse_expr(&mut self) -> Result<Expr, Error> {
    let expr = self.parse_nonassign_expr()?;
    if maybe_want!(self, Token::Eq) {
      Ok(Expr::As(Box::new(expr),
                  Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwMul) {
      Ok(Expr::Rmw(BinOp::Mul,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwDiv) {
      Ok(Expr::Rmw(BinOp::Div,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwMod) {
      Ok(Expr::Rmw(BinOp::Mod,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwAdd) {
      Ok(Expr::Rmw(BinOp::Add,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwSub) {
      Ok(Expr::Rmw(BinOp::Sub,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwLShift) {
      Ok(Expr::Rmw(BinOp::Lsh,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwRShift) {
      Ok(Expr::Rmw(BinOp::Rsh,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwBitAnd) {
      Ok(Expr::Rmw(BinOp::And,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwBitXor) {
      Ok(Expr::Rmw(BinOp::Xor,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else if maybe_want!(self, Token::RmwBitOr) {
      Ok(Expr::Rmw(BinOp::Or,
                   Box::new(expr),
                   Box::new(self.parse_nonassign_expr()?)))
    } else {
      Ok(expr)
    }
  }

  fn parse_nonassign_expr(&mut self) -> Result<Expr, Error> {
    if maybe_want!(self, Token::LCurly) {
      self.parse_block_expr()
    } else if maybe_want!(self, Token::KwIf) {
      self.parse_if_expr()
    } else if maybe_want!(self, Token::KwLoop) {
      self.parse_loop_expr()
    } else if maybe_want!(self, Token::KwWhile) {
      self.parse_while_expr()
    } else if maybe_want!(self, Token::KwMatch) {
      self.parse_match_expr()
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
      Ok(Expr::Let(name, is_mut, ty, init))
    } else if maybe_want!(self, Token::KwContinue) {
      Ok(Expr::Continue)
    } else if maybe_want!(self, Token::KwBreak) {
      // NOTE: actually verify that these are the only valid terminators
      if let (_, Token::Comma | Token::Semi | Token::RAngle | Token::RSquare | Token::RCurly) = self.look(0) {
        Ok(Expr::Break(Box::new(Expr::Unit)))
      } else {
        Ok(Expr::Break(Box::new(self.parse_expr()?)))
      }
    } else if maybe_want!(self, Token::KwReturn) {
      if let (_, Token::Comma | Token::Semi | Token::RAngle | Token::RSquare | Token::RCurly) = self.look(0) {
        Ok(Expr::Return(Box::new(Expr::Unit)))
      } else {
        Ok(Expr::Return(Box::new(self.parse_expr()?)))
      }
    } else {
      self.parse_lor_expr()
    }
  }

  fn parse_block_expr(&mut self) -> Result<Expr, Error> {
    // Empty block
    if maybe_want!(self, Token::RCurly) { return Ok(Expr::Unit) }
    // Parse item list
    let mut exprs = Vec::new();
    loop {
      let mut had_semi = false;
      while maybe_want!(self, Token::Semi) {
        had_semi = true;
      }
      if maybe_want!(self, Token::RCurly) {
        if had_semi { exprs.push(Expr::Unit); }
        break
      }
      exprs.push(self.parse_expr()?);
    }
    Ok(Expr::Block(exprs))
  }

  fn parse_if_expr(&mut self) -> Result<Expr, Error> {
    let cond = self.parse_expr()?;

    // True body
    want!(self, Token::LCurly, ())?;
    let tbody = self.parse_block_expr()?;

    // Else body
    let ebody = if maybe_want!(self, Token::KwElse) {
      if maybe_want!(self, Token::KwIf) {
        self.parse_if_expr()?
      } else {
        want!(self, Token::LCurly, ())?;
        self.parse_block_expr()?
      }
    } else {
      Expr::Unit
    };

    Ok(Expr::If(Box::new(cond), Box::new(tbody), Box::new(ebody)))
  }

  fn parse_loop_expr(&mut self) -> Result<Expr, Error> {
    want!(self, Token::LCurly, ())?;
    let body = self.parse_block_expr()?;
    Ok(Expr::Loop(Box::new(body)))
  }

  fn parse_while_expr(&mut self) -> Result<Expr, Error> {
    let cond = self.parse_expr()?;
    want!(self, Token::LCurly, ())?;
    let body = self.parse_block_expr()?;
    Ok(Expr::While(Box::new(cond), Box::new(body)))
  }

  fn parse_match_expr(&mut self) -> Result<Expr, Error> {
    let cond = self.parse_expr()?;
    want!(self, Token::LCurly, ())?;
    let case_list = self.parse_match_case_list()?;
    Ok(Expr::Match(Box::new(cond), case_list))
  }

  fn parse_match_case_list(&mut self) -> Result<Vec<(Option<RefStr>, RefStr, Expr)>, Error> {
    let mut case_list = Vec::new();
    // Empty list
    if maybe_want!(self, Token::RCurly) { return Ok(case_list) }
    // Read cases
    loop {
      case_list.push(self.parse_match_case()?);
      if maybe_want!(self, Token::RCurly) { break }
      want!(self, Token::Comma, ())?;
    }
    Ok(case_list)
  }

  fn parse_match_case(&mut self) -> Result<(Option<RefStr>, RefStr, Expr), Error> {
    let binding = if let ((_, Token::Ident(name)), (_, Token::Colon)) = (self.look(0).clone(), self.look(1)) {
      self.get();
      self.get();
      Some(name)
    } else {
      None
    };
    let variant = want!(self, Token::Ident(name), *name)?;
    want!(self, Token::FatArrow, ())?;
    Ok((binding, variant, self.parse_expr()?))
  }

  fn parse_lor_expr(&mut self) -> Result<Expr, Error> {
    let mut expr = self.parse_land_expr()?;
    while maybe_want!(self, Token::LogicOr) {
      expr = Expr::LOr(Box::new(expr),
                        Box::new(self.parse_land_expr()?));
    }
    Ok(expr)
  }

  fn parse_land_expr(&mut self) -> Result<Expr, Error> {
    let mut expr = self.parse_cmp_expr()?;
    while maybe_want!(self, Token::LogicAnd) {
      expr = Expr::LAnd(Box::new(expr),
                        Box::new(self.parse_cmp_expr()?));
    }
    Ok(expr)
  }

  fn parse_cmp_expr(&mut self) -> Result<Expr, Error> {
    let expr = self.parse_or_expr()?;
    if maybe_want!(self, Token::EqEq) {
      Ok(Expr::Bin(BinOp::Eq,
                   Box::new(expr),
                   Box::new(self.parse_or_expr()?)))
    } else if maybe_want!(self, Token::ExclEq) {
      Ok(Expr::Bin(BinOp::Ne,
                   Box::new(expr),
                   Box::new(self.parse_or_expr()?)))
    } else if maybe_want!(self, Token::LAngle) {
      Ok(Expr::Bin(BinOp::Lt,
                   Box::new(expr),
                   Box::new(self.parse_or_expr()?)))
    } else if maybe_want!(self, Token::RAngle) {
      Ok(Expr::Bin(BinOp::Gt,
                   Box::new(expr),
                   Box::new(self.parse_or_expr()?)))
    } else if maybe_want!(self, Token::LessEq) {
      Ok(Expr::Bin(BinOp::Le,
                   Box::new(expr),
                   Box::new(self.parse_or_expr()?)))
    } else if maybe_want!(self, Token::GreaterEq) {
      Ok(Expr::Bin(BinOp::Ge,
                   Box::new(expr),
                   Box::new(self.parse_or_expr()?)))
    } else {
      Ok(expr)
    }
  }

  fn parse_or_expr(&mut self) -> Result<Expr, Error> {
    let mut expr = self.parse_xor_expr()?;
    while maybe_want!(self, Token::Pipe) {
      expr = Expr::Bin(BinOp::Or,
                       Box::new(expr),
                       Box::new(self.parse_xor_expr()?));
    }
    Ok(expr)
  }

  fn parse_xor_expr(&mut self) -> Result<Expr, Error> {
    let mut expr = self.parse_and_expr()?;
    while maybe_want!(self, Token::Caret) {
      expr = Expr::Bin(BinOp::Xor,
                       Box::new(expr),
                       Box::new(self.parse_and_expr()?));
    }
    Ok(expr)
  }

  fn parse_and_expr(&mut self) -> Result<Expr, Error> {
    let mut expr = self.parse_shift_expr()?;
    while maybe_want!(self, Token::Amp) {
      expr = Expr::Bin(BinOp::And,
                       Box::new(expr),
                       Box::new(self.parse_shift_expr()?));
    }
    Ok(expr)
  }

  fn parse_shift_expr(&mut self) -> Result<Expr, Error> {
    let mut expr = self.parse_add_expr()?;
    loop {
      if maybe_want!(self, Token::LShift) {
        expr = Expr::Bin(BinOp::Lsh,
                         Box::new(expr),
                         Box::new(self.parse_add_expr()?));
      } else if maybe_want!(self, Token::RShift) {
        expr = Expr::Bin(BinOp::Rsh,
                         Box::new(expr),
                         Box::new(self.parse_add_expr()?));
      } else {
        break
      }
    }
    Ok(expr)
  }

  fn parse_add_expr(&mut self) -> Result<Expr, Error> {
    let mut expr = self.parse_mul_expr()?;
    loop {
      if maybe_want!(self, Token::Plus) {
        expr = Expr::Bin(BinOp::Add,
                         Box::new(expr),
                         Box::new(self.parse_mul_expr()?));
      } else if maybe_want!(self, Token::Minus) {
        expr = Expr::Bin(BinOp::Sub,
                         Box::new(expr),
                         Box::new(self.parse_mul_expr()?));
      } else {
        break
      }
    }
    Ok(expr)
  }

  fn parse_mul_expr(&mut self) -> Result<Expr, Error> {
    let mut expr = self.parse_cast_expr()?;
    loop {
      if maybe_want!(self, Token::Star) {
        expr = Expr::Bin(BinOp::Mul,
                         Box::new(expr),
                         Box::new(self.parse_cast_expr()?));
      } else if maybe_want!(self, Token::Slash) {
        expr = Expr::Bin(BinOp::Div,
                         Box::new(expr),
                         Box::new(self.parse_cast_expr()?));
      } else if maybe_want!(self, Token::Percent) {
        expr = Expr::Bin(BinOp::Mod,
                         Box::new(expr),
                         Box::new(self.parse_cast_expr()?));
      } else {
        break
      }
    }
    Ok(expr)
  }

  fn parse_cast_expr(&mut self) -> Result<Expr, Error> {
    let mut expr = self.parse_pre_expr()?;
    while maybe_want!(self, Token::KwAs) {
      want!(self, Token::LAngle, ())?;
      expr = Expr::Cast(Box::new(expr), self.parse_ty()?);
      want!(self, Token::RAngle, ())?;
    }
    Ok(expr)
  }

  fn parse_pre_expr(&mut self) -> Result<Expr, Error> {
    if maybe_want!(self, Token::Amp) {
      Ok(Expr::Adr(Box::new(self.parse_pre_expr()?)))
    } else if maybe_want!(self, Token::Star) {
      Ok(Expr::Ind(Box::new(self.parse_pre_expr()?)))
    } else if maybe_want!(self, Token::Plus) {
      Ok(Expr::Un(UnOp::UPlus, Box::new(self.parse_pre_expr()?)))
    } else if maybe_want!(self, Token::Minus) {
      Ok(Expr::Un(UnOp::UMinus, Box::new(self.parse_pre_expr()?)))
    }  else if maybe_want!(self, Token::Tilde) {
      Ok(Expr::Un(UnOp::Not, Box::new(self.parse_pre_expr()?)))
    }  else if maybe_want!(self, Token::Excl) {
      Ok(Expr::LNot(Box::new(self.parse_pre_expr()?)))
    }else {
      self.parse_post_expr()
    }
  }

  fn parse_post_expr(&mut self) -> Result<Expr, Error> {
    let mut expr = self.parse_prim_expr()?;
    loop {
      if maybe_want!(self, Token::Dot) {
        let field = want!(self, Token::Ident(name), *name)?;
        expr = Expr::Dot(Box::new(expr), field);
      } else if maybe_want!(self, Token::LParen) {
        let args = self.parse_argument_list()?;
        expr = Expr::Call(Box::new(expr), args);
      } else if maybe_want!(self, Token::LSquare) {
        let index = self.parse_expr()?;
        want!(self, Token::RSquare, ())?;
        expr = Expr::Index(Box::new(expr), Box::new(index));
      } else {
        return Ok(expr)
      }
    }
  }

  fn parse_argument_list(&mut self) -> Result<Vec<(RefStr, Expr)>, Error> {
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

  fn parse_prim_expr(&mut self) -> Result<Expr, Error> {
    match self.get() {
      (_, Token::LParen) => {
        if maybe_want!(self, Token::RParen) { // Unit
          Ok(Expr::Unit)
        } else if let ((_, Token::Ident(..)), (_, Token::Colon)) = (self.look(0).clone(), self.look(1)) {
          Ok(Expr::Tuple(self.parse_tuple_field_list()?))
        } else {
          let expr = self.parse_expr()?;
          want!(self, Token::RParen, ())?;
          Ok(expr)
        }
      }
      (_, Token::Ident(s)) => {
        let mut crumbs = vec![s];
        while maybe_want!(self, Token::DColon) {
          crumbs.push(want!(self, Token::Ident(name), *name)?);
        }
        Ok(Expr::Path(Path(crumbs)))
      }
      (_, Token::KwNil) => {
        Ok(Expr::Nil)
      }
      (_, Token::KwTrue) => {
        Ok(Expr::Bool(true))
      }
      (_, Token::KwFalse) => {
        Ok(Expr::Bool(false))
      }
      (_, Token::LSquare) => {
        Ok(Expr::Arr(self.parse_array_element_list()?))
      }
      (_, Token::IntLit(val)) => {
        Ok(Expr::Int(val))
      }
      (_, Token::FltLit(val)) => {
        Ok(Expr::Flt(val))
      }
      (_, Token::StrLit(val)) => {
        Ok(Expr::Str(val))
      }
      (_, Token::CStrLit(val)) => {
        Ok(Expr::CStr(val))
      }
      (location, token) => {
        Err(Error::UnexpectedToken(location, token))
      }
    }
  }

  fn parse_tuple_field_list(&mut self) -> Result<Vec<(RefStr, Expr)>, Error> {
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

  fn parse_array_element_list(&mut self) -> Result<Vec<Expr>, Error> {
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
