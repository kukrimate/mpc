/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use crate::*;
use crate::util::RefStr;
use crate::resolve::{ResolvedDef,resolve_defs};

use std::collections::HashMap;
use std::{fs, fmt};
use std::fmt::Formatter;
use std::hash::Hash;
use std::os::unix::fs::MetadataExt;
use std::path::PathBuf;

mod lexer;
mod parser;
mod tree;

pub use lexer::*;
pub use tree::*;

#[derive(Debug)]
pub struct Repository {
  def_cnt: usize,
  search_dirs: Vec<PathBuf>,
  current_scope: Vec<DefId>,
  ino_to_module: HashMap<u64, DefId>,
  parent_scope: HashMap<DefId, DefId>,
  pub parsed_defs: HashMap<DefId, Def>,
  pub resolved_defs: HashMap<DefId, ResolvedDef>,
  pub syms: HashMap<DefId, HashMap<RefStr, DefId>>
}

impl Repository {
  pub fn new() -> Repository {
    // Crate repository
    Repository {
      def_cnt: 0,
      search_dirs: vec![ PathBuf::from(env!("MPC_STD_DIR")) ],
      current_scope: Vec::new(),
      ino_to_module: HashMap::new(),
      parent_scope: HashMap::new(),
      parsed_defs: HashMap::new(),
      resolved_defs: HashMap::new(),
      syms: HashMap::new()
    }
  }

  pub fn locate(&self, scope_id: DefId, path: &Path) -> Option<DefId> {
    let mut cur_id = scope_id;
    for crumb in path.crumbs().iter() {
      let symtab = self.syms.get(&cur_id).unwrap();
      if let Some(def_id) = symtab.get(crumb) {
        cur_id = *def_id;
      } else {
        return None
      }
    }
    Some(cur_id)
  }

  pub fn parent(&self, def_id: DefId) -> DefId {
    *self.parent_scope.get(&def_id).unwrap()
  }

  pub fn parsed_by_id(&self, def_id: DefId) -> &Def {
    self.parsed_defs.get(&def_id).unwrap()
  }

  fn new_id(&mut self) -> DefId {
    let id = DefId(self.def_cnt);
    self.def_cnt += 1;
    id
  }

  fn def(&mut self, def: Def) -> DefId {
    let id = self.new_id();
    let parent = *self.current_scope.last().unwrap();
    self.parsed_defs.insert(id, def);
    self.parent_scope.insert(id, parent);
    id
  }

  fn sym(&mut self, location: Location, name: RefStr, def: DefId) -> Result<(), CompileError> {
    let scope = self.syms
      .entry(*self.current_scope.last().unwrap())
      .or_insert_with(|| HashMap::new());

    match scope.insert(name, def) {
      None => Ok(()),         // No redefinition
      Some(..) => {           // Redefinition errors
        Err(CompileError::Redefinition(location, name))
      }
    }
  }

  fn find_module(&mut self, location: Location, name: RefStr) -> Result<PathBuf, CompileError> {
    for dir in self.search_dirs.iter().rev() {
      let path = dir
        .join(std::path::Path::new(name.borrow_rs()))
        .with_extension("m");
      if path.is_file() { return Ok(path) }
    }
    Err(CompileError::UnknownModule(location, name))
  }

  fn parse_module(&mut self, path: &std::path::Path) -> Result<DefId, CompileError> {
    // Return previous copy if we've parsed a module with the same inode number
    // Otherwise we can go ahead and parse it

    let ino = fs::metadata(path)
      .map_err(|error| CompileError::IoError(path.to_path_buf(), error))?
      .ino();
    if let Some(def_id) = self.ino_to_module.get(&ino) {
      return Ok(*def_id)
    }

    // Create module context
    let module_id = self.new_id();
    self.ino_to_module.insert(ino, module_id);
    self.search_dirs.push(path.parent().unwrap().to_path_buf());
    self.current_scope.push(module_id);

    let input = fs::read_to_string(path).map_err(|error| CompileError::IoError(path.to_path_buf(), error))?;

    let lexer = lexer::Lexer::new(&input);
    let result = match parser::Parser::new(self, lexer).parse() {
      Ok(()) => Ok(module_id),
      Err(err) => Err(err)
    };

    // Exit module context
    self.current_scope.pop();
    self.search_dirs.pop();

    result
  }
}

pub fn parse_bundle(path: &std::path::Path) -> Result<Repository, CompileError> {
  let mut repo = Repository::new();
  repo.parse_module(path)?;
  resolve_defs(&mut repo)?;
  Ok(repo)
}
