/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use std::env;
use std::path;

fn main() {
  // Define MPC_STD_DIR if wasn't previously defined
  if let Err(..) = env::var("MPC_STD_DIR") {
    let manifest_dir =
      env::var("CARGO_MANIFEST_DIR").unwrap();
    let std_path =
      path::PathBuf::from(manifest_dir)
      .parent().unwrap()
      .join("mpc_std");
    println!("cargo:rustc-env=MPC_STD_DIR={}", std_path.to_str().unwrap());
  }
}
