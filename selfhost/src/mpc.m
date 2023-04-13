import libc
import slice
import result
import mem
import lexer

// Compilation error
enum CompileError (
  UnexpectedEndOfFile,
  UnrecognizedCharacter(ch: Uint8),
  UnrecognizedEscapeSequence(ch: Uint8)
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

  result::ok(slice::from_ptr(input, size))
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

  // Create lexer
  let lexer = lexer::new(input);

  loop {
    let r = lexer::next(&lexer);

    if (&r).is_err() {
      let err = r.unwrap_err();
      (&err).fmt(libc::stderr);
      libc::fputc('\n', libc::stderr);
      return 1
    }

    match r.unwrap_ok() {
      EndOfFile => break,
      Ident(v) => libc::printf(c"Ident\n"),
      IntLit(v) => libc::printf(c"IntLit\n"),
      FltLit(v) => libc::printf(c"FltLit\n"),
      StrLit(v) => libc::printf(c"StrLit\n"),
      CStrLit(v) => libc::printf(c"CStrLit\n"),
      TyBool => libc::printf(c"TyBool\n"),
      TyUint8 => libc::printf(c"TyUint8\n"),
      TyInt8 => libc::printf(c"TyInt8\n"),
      TyUint16 => libc::printf(c"TyUint16\n"),
      TyInt16 => libc::printf(c"TyInt16\n"),
      TyUint32 => libc::printf(c"TyUint32\n"),
      TyInt32 => libc::printf(c"TyInt32\n"),
      TyUint64 => libc::printf(c"TyUint64\n"),
      TyInt64 => libc::printf(c"TyInt64\n"),
      TyUintn => libc::printf(c"TyUintn\n"),
      TyIntn => libc::printf(c"TyIntn\n"),
      TyFloat => libc::printf(c"TyFloat\n"),
      TyDouble => libc::printf(c"TyDouble\n"),
      TyFunction => libc::printf(c"TyFunction\n"),
      KwAs => libc::printf(c"KwAs\n"),
      KwLet => libc::printf(c"KwLet\n"),
      KwMut => libc::printf(c"KwMut\n"),
      KwContinue => libc::printf(c"KwContinue\n"),
      KwBreak => libc::printf(c"KwBreak\n"),
      KwReturn => libc::printf(c"KwReturn\n"),
      KwIf => libc::printf(c"KwIf\n"),
      KwElse => libc::printf(c"KwElse\n"),
      KwWhile => libc::printf(c"KwWhile\n"),
      KwLoop => libc::printf(c"KwLoop\n"),
      KwMatch => libc::printf(c"KwMatch\n"),
      KwNil => libc::printf(c"KwNil\n"),
      KwTrue => libc::printf(c"KwTrue\n"),
      KwFalse => libc::printf(c"KwFalse\n"),
      KwStruct => libc::printf(c"KwStruct\n"),
      KwUnion => libc::printf(c"KwUnion\n"),
      KwEnum => libc::printf(c"KwEnum\n"),
      KwType => libc::printf(c"KwType\n"),
      KwFunction => libc::printf(c"KwFunction\n"),
      KwConst => libc::printf(c"KwConst\n"),
      KwData => libc::printf(c"KwData\n"),
      KwImport => libc::printf(c"KwImport\n"),
      KwExtern => libc::printf(c"KwExtern\n"),
      LParen => libc::printf(c"LParen\n"),
      RParen => libc::printf(c"RParen\n"),
      LSquare => libc::printf(c"LSquare\n"),
      RSquare => libc::printf(c"RSquare\n"),
      LCurly => libc::printf(c"LCurly\n"),
      RCurly => libc::printf(c"RCurly\n"),
      LAngle => libc::printf(c"LAngle\n"),
      RAngle => libc::printf(c"RAngle\n"),
      Amp => libc::printf(c"Amp\n"),
      Star => libc::printf(c"Star\n"),
      Plus => libc::printf(c"Plus\n"),
      Minus => libc::printf(c"Minus\n"),
      Tilde => libc::printf(c"Tilde\n"),
      Excl => libc::printf(c"Excl\n"),
      Slash => libc::printf(c"Slash\n"),
      Percent => libc::printf(c"Percent\n"),
      Pipe => libc::printf(c"Pipe\n"),
      Caret => libc::printf(c"Caret\n"),
      Eq => libc::printf(c"Eq\n"),
      Dot => libc::printf(c"Dot\n"),
      Comma => libc::printf(c"Comma\n"),
      Semi => libc::printf(c"Semi\n"),
      Colon => libc::printf(c"Colon\n"),
      LShift => libc::printf(c"LShift\n"),
      RShift => libc::printf(c"RShift\n"),
      DColon => libc::printf(c"DColon\n"),
      Arrow => libc::printf(c"Arrow\n"),
      FatArrow => libc::printf(c"FatArrow\n"),
      EqEq => libc::printf(c"EqEq\n"),
      ExclEq => libc::printf(c"ExclEq\n"),
      LessEq => libc::printf(c"LessEq\n"),
      GreaterEq => libc::printf(c"GreaterEq\n"),
      LogicAnd => libc::printf(c"LogicAnd\n"),
      LogicOr => libc::printf(c"LogicOr\n"),
      RmwAdd => libc::printf(c"RmwAdd\n"),
      RmwSub => libc::printf(c"RmwSub\n"),
      RmwMul => libc::printf(c"RmwMul\n"),
      RmwDiv => libc::printf(c"RmwDiv\n"),
      RmwMod => libc::printf(c"RmwMod\n"),
      RmwLShift => libc::printf(c"RmwLShift\n"),
      RmwRShift => libc::printf(c"RmwRShift\n"),
      RmwBitAnd => libc::printf(c"RmwBitAnd\n"),
      RmwBitOr => libc::printf(c"RmwBitOr\n"),
      RmwBitXor => libc::printf(c"RmwBitXor\n"),
      Varargs => libc::printf(c"Varargs\n")
    }
  }

  0
}

// C entry point
function main(argc: libc::Int, argv: **libc::Char) -> libc::Int {
  mpc_main(slice::from_ptr(argv, argc as <Uintn>))
}
