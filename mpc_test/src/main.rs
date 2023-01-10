use mpc;
use std::ffi::OsStr;
use std::fs;
use std::path::Path;
use std::process::Command;

/// Directory of test programs
const PROG_DIR: &str = "mpc_test/prog";

/// Output directory
const OUTPUT_DIR: &str = "mpc_test/output";

/// Link an object file into an executable
fn link(obj_path: &Path, bin_path: &Path) {
  let status = Command::new("cc")
    .args([OsStr::new("-o"), bin_path.as_os_str(), obj_path.as_os_str()])
    .status()
    .expect("failed to run cc");

  if !status.success() {
    panic!("linking failed");
  }
}

fn main() {
  for cur in fs::read_dir(PROG_DIR).unwrap() {
    let src_path = cur.unwrap().path();
    let file_name = src_path.file_name().unwrap();
    let obj_path = Path::new(OUTPUT_DIR)
                    .join(&file_name)
                    .with_extension("o");
    let bin_path = Path::new(OUTPUT_DIR)
                      .join(&file_name)
                      .with_extension("");

    match mpc::compile(&src_path, &obj_path, mpc::CompileTo::Object)
            .and_then(|_| Ok(link(&obj_path, &bin_path))) {
      Ok(()) => println!("[OK] {}", file_name.to_str().unwrap()),
      Err(err) => println!("[ERR] {} {}", file_name.to_str().unwrap(), err),
    }
  }
}
