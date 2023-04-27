/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use crate::*;
use crate::util::RefStr;

use std::collections::HashMap;
use std::os::unix::fs::MetadataExt;
use std::path::PathBuf;

mod lexer;
mod parser;
mod tree;

pub use lexer::*;
pub use tree::*;

pub struct Repository {
  def_cnt: usize,
  ino_to_module: HashMap<u64, DefId>,
  parsed_defs: HashMap<DefId, Def>,
  syms: HashMap<DefId, HashMap<RefStr, DefId>>,
  queue: Vec<ImportTodo>
}

struct ImportTodo {
  /// Import source location
  loc: SourceLocation,
  /// Parent module ID
  parent_id: DefId,
  /// Parent module path on disk
  parent_path: PathBuf,
  /// Imported module
  module: RefStr,
  /// Imported path
  path: Path
}

impl Repository {
  pub fn new() -> Repository {
    // Crate repository
    Repository {
      def_cnt: 0,
      ino_to_module: HashMap::new(),
      parsed_defs: HashMap::new(),
      syms: HashMap::new(),
      queue: Vec::new()
    }
  }

  pub fn locate_path(&self, scope_id: DefId, path: &Path) -> Option<DefId> {
    let mut cur_id = scope_id;
    for crumb in path.crumbs().iter() {
      cur_id = self.locate_name(cur_id, *crumb)?;
    }
    Some(cur_id)
  }

  pub fn locate_name(&self, scope_id: DefId, name: RefStr) -> Option<DefId> {
    let scope = self.syms.get(&scope_id)?;
    scope.get(&name).cloned()
  }

  pub fn parsed_def(&self, def_id: DefId) -> &Def {
    self.parsed_defs.get(&def_id).unwrap()
  }

  pub fn parsed_defs(&self) -> impl Iterator<Item=(&DefId, &Def)> {
    self.parsed_defs.iter()
  }

  fn new_id(&mut self) -> DefId {
    let id = DefId(self.def_cnt);
    self.def_cnt += 1;
    id
  }

  fn def(&mut self, def: Def) -> DefId {
    let id = self.new_id();
    self.parsed_defs.insert(id, def);
    id
  }

  fn sym(&mut self, location: SourceLocation, scope_id: DefId, name: RefStr, def_id: DefId) -> Result<(), CompileError> {
    // Find parent scope's symbol table
    let parent_scope = self.syms
      .entry(scope_id)
      .or_insert_with(|| HashMap::new());

    match parent_scope.insert(name, def_id) {
      None => Ok(()),         // No redefinition
      Some(..) => {           // Redefinition errors
        Err(CompileError::Redefinition(location, name))
      }
    }
  }

  fn parse_module(&mut self, path: &std::path::Path) -> Result<DefId, CompileError> {
    // Find inode
    let ino = std::fs::metadata(path)
      .map_err(|error| CompileError::IoError(path.to_path_buf(), error))?
      .ino();

    // Return previous copy if we've already parsed it
    if let Some(def_id) = self.ino_to_module.get(&ino) {
      return Ok(*def_id)
    }

    // Otherwise parse the module now
    let module_id = self.new_id();
    self.ino_to_module.insert(ino, module_id);

    let file = std::sync::Arc::new(SourceFile {
      path: path.to_owned(),
      data: std::fs::read_to_string(path).map_err(|error| CompileError::IoError(path.to_path_buf(), error))?
    });

    match parser::Parser::new(self, module_id, path, Lexer::new(file)).parse() {
      Ok(()) => Ok(module_id),
      Err(err) => Err(err)
    }
  }

  fn parse_modules(&mut self, root_path: &std::path::Path) -> Result<(), CompileError> {
    // Parse root module
    self.parse_module(root_path)?;

    // Symbols to be added after all modules were imported
    // (This is done is a separate paths, as imports cannot refer to other imports transitively)
    let mut q = Vec::new();

    // Parse queued dependencies
    while let Some(todo) = self.queue.pop() {
      // Search directories for this dependency
      let search_dirs = [
        todo.parent_path.parent().unwrap(),
        std::path::Path::new(env!("MPC_STD_DIR"))
      ];

      let mut found = false;

      for dir in search_dirs {
        let path = dir
          .join(todo.module.borrow_rs())
          .with_extension("m");

        if path.is_file() {
          // Parse dependency if found
          let module_id = self.parse_module(&path)?;
          // Find imported item
          let def_id = self.locate_path(module_id, &todo.path)
            .ok_or_else(|| CompileError::UnresolvedPath(todo.loc.clone(),
                                                        todo.path.clone()))?;
          // Add to queue
          if todo.path.crumbs().len() > 0 { q.push((todo.loc.clone(), todo.parent_id, *todo.path.crumbs().last().unwrap(), def_id)) }
          else { q.push((todo.loc.clone(), todo.parent_id, todo.module, def_id)) }
          // Set marker then exit
          found = true;
          break
        }
      }

      if !found {
        return Err(CompileError::UnknownModule(todo.loc, todo.module))
      }
    }

    for (loc , parent_id, name, def_id) in q.into_iter() {
      self.sym(loc, parent_id, name, def_id)?;
    }

    Ok(())
  }

  fn resolve_methods(&mut self) -> Result<(), CompileError> {
    let mut q = Vec::new();

    for (def_id, def) in self.parsed_defs.iter() {
      match def {
        Def::Func(def) => {
          if let Some((_, ty)) = &def.receiver {
            let receiver_id = self.find_receiver_id(def.parent_id, ty)?;
            q.push((def.loc.clone(), receiver_id, def.name, *def_id));
          }
        }
        _ => ()
      }
    }

    for (loc, receiver_id, name, method_id) in q.into_iter() {
      self.sym(loc, receiver_id, name, method_id)?;
    }

    Ok(())
  }

  fn find_receiver_id(&self, scope_id: DefId, ty: &Ty) -> Result<DefId, CompileError> {
    match ty {
      Ty::Inst(_ , path, _) => self.validate_receiver(ty.loc(), scope_id, path),
      Ty::Ptr(_, _, base) => match &**base {
        Ty::Inst(_, path, _) => self.validate_receiver(ty.loc(), scope_id, path),
        _ => Err(CompileError::InvalidMethodReceiver(ty.loc().clone()))
      }
      _ => Err(CompileError::InvalidMethodReceiver(ty.loc().clone()))
    }
  }

  fn validate_receiver(&self, loc: &SourceLocation, scope_id: DefId, path: &Path) -> Result<DefId, CompileError> {
    let receiver_id = self.locate_path(scope_id, path)
      .ok_or_else(|| CompileError::InvalidMethodReceiver(loc.clone()))?;
    match self.parsed_defs.get(&receiver_id).unwrap() {
      Def::Struct(..) | Def::Union(..) | Def::Enum(..) => Ok(receiver_id),
      _ => Err(CompileError::InvalidMethodReceiver(loc.clone()))?
    }
  }
}

pub fn parse_bundle(path: &std::path::Path) -> Result<Repository, CompileError> {
  let mut repo = Repository::new();
  repo.parse_modules(path)?;
  repo.resolve_methods()?;
  Ok(repo)
}
