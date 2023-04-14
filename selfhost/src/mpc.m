import libc
import slice
import result
import mem
import lexer
import parser

// Compilation error
enum CompileError (
  UnexpectedEndOfFile,
  UnrecognizedCharacter(ch: Uint8),
  UnrecognizedEscapeSequence(ch: Uint8),
  UnexptedToken(tk: lexer::Tk)
)

// Print a compilation error
function (e: *CompileError) fmt(f: *mut libc::FILE) {
  match *e {
    UnexpectedEndOfFile => {
      libc::fprintf(f, c"Unexpected end of file");
    },
    UnrecognizedCharacter(ch) => {
      libc::fprintf(f, c"Unrecognized character %c", ch);
    },
    UnrecognizedEscapeSequence(ch) => {
      libc::fprintf(f, c"Unrecognized escape sequence %c", ch);
    },
    UnexptedToken(tk) => {
      libc::fprintf(f, c"Unrecognized token ");
      (&tk).fmt(f);
    }
  }
}

// Read a file
function read_file(path: *libc::Char) -> result::Result<slice::Slice<Uint8>, ()> {
  let infile = libc::fopen(path, c"r");
  if infile == nil { return result::err(()) }

  libc::fseek(infile, 0, libc::SEEK_END);
  let size = libc::ftell(infile) as <Uintn>;
  libc::rewind(infile);

  let input: *Uint8 = mem::allocate_contiguous(size);
  libc::fread(input as <*mut libc::Void>, 1, size, infile);

  libc::fclose(infile);

  result::ok(slice::from_ptr(input as <*Uint8>, size))
}

// Compiler entry point
function mpc_main(args: slice::Slice<*libc::Char>) -> libc::Int {
  // Parse arguments
  if args.length < 2 {
    libc::fprintf(libc::stderr, c"Usage: mpc INPUT\n");
    return 1
  }

  // Read input file
  let input = read_file(*args.at(1)).unwrap_ok();
  // Create parser
  let mut parser = parser::new(input);
  // Parse file
  (&parser).parse().unwrap_ok();

  0
}

// C entry point
function main(argc: libc::Int, argv: **libc::Char) -> libc::Int {
  mpc_main(slice::from_ptr(argv, argc as <Uintn>))
}
