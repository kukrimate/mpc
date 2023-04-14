import libc
import mpc
import opt
import prog
import result
import slice
import str
import vec

enum Tk (
  EndOfFile,
  IntLit(v: Uintn),     // [0-9]+
                        // 0[xX][a-fA-f0-9]+
                        // 0[oO][0-7]+
                        // 0[bB][0-1]+
  FltLit(v: Double),    // [0-9]*[.][0-9]+([eE][+-]?[0-9]+)?
  StrLit(v: str::Str),  // "([^"]|\")*"
  CStrLit(v: str::Str), // c"([^"]|\")*"
  Ident(v: str::Str),   // [_a-zA-Z][_a-zA-Z0-9]*
  TyBool,               // Bool
  TyUint8,              // Uint8
  TyInt8,               // Int8
  TyUint16,             // Uint16
  TyInt16,              // Int16
  TyUint32,             // Uint32
  TyInt32,              // Int32
  TyUint64,             // Uint64
  TyInt64,              // Int64
  TyUintn,              // Uintn
  TyIntn,               // Intn
  TyFloat,              // Float
  TyDouble,             // Double
  TyFunction,           // Function
  KwAs,                 // as
  KwLet,                // let
  KwMut,                // mut
  KwContinue,           // continue
  KwBreak,              // break
  KwReturn,             // return
  KwIf,                 // if
  KwElse,               // else
  KwWhile,              // while
  KwLoop,               // loop
  KwMatch,              // match
  KwNil,                // nil
  KwTrue,               // true
  KwFalse,              // false
  KwStruct,             // struct
  KwUnion,              // union
  KwEnum,               // enum
  KwType,               // type
  KwFunction,           // function
  KwConst,              // const
  KwData,               // data
  KwImport,             // import
  KwExtern,             // extern
  LParen,               // (
  RParen,               // )
  LSquare,              // [
  RSquare,              // ]
  LCurly,               // {
  RCurly,               // }
  LAngle,               // <
  RAngle,               // >
  Amp,                  // &
  Star,                 // *
  Plus,                 // +
  Minus,                // -
  Tilde,                // ~
  Excl,                 // !
  Slash,                // /
  Percent,              // %
  Pipe,                 // |
  Caret,                // ^
  Eq,                   // =
  Dot,                  // .
  Comma,                // ,
  Semi,                 // ;
  Colon,                // :
  LShift,               // <<
  RShift,               // >>
  DColon,               // ::
  Arrow,                // ->
  FatArrow,             // =>
  EqEq,                 // ==
  ExclEq,               // !=
  LessEq,               // <=
  GreaterEq,            // >=
  LogicAnd,             // &&
  LogicOr,              // ||
  RmwAdd,               // +=
  RmwSub,               // -=
  RmwMul,               // *=
  RmwDiv,               // /=
  RmwMod,               // %=
  RmwLShift,            // <<=
  RmwRShift,            // >>=
  RmwBitAnd,            // &=
  RmwBitOr,             // |=
  RmwBitXor,            // ^=
  Varargs               // ...
)

function (tk: *Tk) fmt(f: *mut libc::FILE) {
  match *tk {
    EndOfFile => libc::fprintf(f, c"EndOfFile"),
    Ident(v) => libc::fprintf(f, c"Ident"),
    IntLit(v) => libc::fprintf(f, c"IntLit"),
    FltLit(v) => libc::fprintf(f, c"FltLit"),
    StrLit(v) => libc::fprintf(f, c"StrLit"),
    CStrLit(v) => libc::fprintf(f, c"CStrLit"),
    TyBool => libc::fprintf(f, c"TyBool"),
    TyUint8 => libc::fprintf(f, c"TyUint8"),
    TyInt8 => libc::fprintf(f, c"TyInt8"),
    TyUint16 => libc::fprintf(f, c"TyUint16"),
    TyInt16 => libc::fprintf(f, c"TyInt16"),
    TyUint32 => libc::fprintf(f, c"TyUint32"),
    TyInt32 => libc::fprintf(f, c"TyInt32"),
    TyUint64 => libc::fprintf(f, c"TyUint64"),
    TyInt64 => libc::fprintf(f, c"TyInt64"),
    TyUintn => libc::fprintf(f, c"TyUintn"),
    TyIntn => libc::fprintf(f, c"TyIntn"),
    TyFloat => libc::fprintf(f, c"TyFloat"),
    TyDouble => libc::fprintf(f, c"TyDouble"),
    TyFunction => libc::fprintf(f, c"TyFunction"),
    KwAs => libc::fprintf(f, c"KwAs"),
    KwLet => libc::fprintf(f, c"KwLet"),
    KwMut => libc::fprintf(f, c"KwMut"),
    KwContinue => libc::fprintf(f, c"KwContinue"),
    KwBreak => libc::fprintf(f, c"KwBreak"),
    KwReturn => libc::fprintf(f, c"KwReturn"),
    KwIf => libc::fprintf(f, c"KwIf"),
    KwElse => libc::fprintf(f, c"KwElse"),
    KwWhile => libc::fprintf(f, c"KwWhile"),
    KwLoop => libc::fprintf(f, c"KwLoop"),
    KwMatch => libc::fprintf(f, c"KwMatch"),
    KwNil => libc::fprintf(f, c"KwNil"),
    KwTrue => libc::fprintf(f, c"KwTrue"),
    KwFalse => libc::fprintf(f, c"KwFalse"),
    KwStruct => libc::fprintf(f, c"KwStruct"),
    KwUnion => libc::fprintf(f, c"KwUnion"),
    KwEnum => libc::fprintf(f, c"KwEnum"),
    KwType => libc::fprintf(f, c"KwType"),
    KwFunction => libc::fprintf(f, c"KwFunction"),
    KwConst => libc::fprintf(f, c"KwConst"),
    KwData => libc::fprintf(f, c"KwData"),
    KwImport => libc::fprintf(f, c"KwImport"),
    KwExtern => libc::fprintf(f, c"KwExtern"),
    LParen => libc::fprintf(f, c"LParen"),
    RParen => libc::fprintf(f, c"RParen"),
    LSquare => libc::fprintf(f, c"LSquare"),
    RSquare => libc::fprintf(f, c"RSquare"),
    LCurly => libc::fprintf(f, c"LCurly"),
    RCurly => libc::fprintf(f, c"RCurly"),
    LAngle => libc::fprintf(f, c"LAngle"),
    RAngle => libc::fprintf(f, c"RAngle"),
    Amp => libc::fprintf(f, c"Amp"),
    Star => libc::fprintf(f, c"Star"),
    Plus => libc::fprintf(f, c"Plus"),
    Minus => libc::fprintf(f, c"Minus"),
    Tilde => libc::fprintf(f, c"Tilde"),
    Excl => libc::fprintf(f, c"Excl"),
    Slash => libc::fprintf(f, c"Slash"),
    Percent => libc::fprintf(f, c"Percent"),
    Pipe => libc::fprintf(f, c"Pipe"),
    Caret => libc::fprintf(f, c"Caret"),
    Eq => libc::fprintf(f, c"Eq"),
    Dot => libc::fprintf(f, c"Dot"),
    Comma => libc::fprintf(f, c"Comma"),
    Semi => libc::fprintf(f, c"Semi"),
    Colon => libc::fprintf(f, c"Colon"),
    LShift => libc::fprintf(f, c"LShift"),
    RShift => libc::fprintf(f, c"RShift"),
    DColon => libc::fprintf(f, c"DColon"),
    Arrow => libc::fprintf(f, c"Arrow"),
    FatArrow => libc::fprintf(f, c"FatArrow"),
    EqEq => libc::fprintf(f, c"EqEq"),
    ExclEq => libc::fprintf(f, c"ExclEq"),
    LessEq => libc::fprintf(f, c"LessEq"),
    GreaterEq => libc::fprintf(f, c"GreaterEq"),
    LogicAnd => libc::fprintf(f, c"LogicAnd"),
    LogicOr => libc::fprintf(f, c"LogicOr"),
    RmwAdd => libc::fprintf(f, c"RmwAdd"),
    RmwSub => libc::fprintf(f, c"RmwSub"),
    RmwMul => libc::fprintf(f, c"RmwMul"),
    RmwDiv => libc::fprintf(f, c"RmwDiv"),
    RmwMod => libc::fprintf(f, c"RmwMod"),
    RmwLShift => libc::fprintf(f, c"RmwLShift"),
    RmwRShift => libc::fprintf(f, c"RmwRShift"),
    RmwBitAnd => libc::fprintf(f, c"RmwBitAnd"),
    RmwBitOr => libc::fprintf(f, c"RmwBitOr"),
    RmwBitXor => libc::fprintf(f, c"RmwBitXor"),
    Varargs => libc::fprintf(f, c"Varargn")
  };
}

struct Lexer (input: slice::Slice<Uint8>, cur: Uintn)

// Create a new lexer instance for a file
function new(input: slice::Slice<Uint8>) -> Lexer {
  Lexer(input, 0)
}


// Read the next input character
function (lexer: *mut Lexer) get() -> opt::Option<Uint8> {
  match (*lexer).input.at_or_none((*lexer).cur) {
    Some(val) => {
      (*lexer).cur += 1;
      opt::some(*val)
    },
    None => opt::none()
  }
}


// Peek at the next input character
function (lexer: *mut Lexer) peek() -> opt::Option<Uint8> {
  match (*lexer).input.at_or_none((*lexer).cur) {
    Some(val) => opt::some(*val),
    None => opt::none()
  }
}

// Consume the next input character if equal
function (lexer: *mut Lexer) consume_eq(want: Uint8) -> Bool {
  match (*lexer).input.at_or_none((*lexer).cur) {
    Some(val) => {
      if *val == want {
        (*lexer).cur += 1;
        true
      } else {
        false
      }
    },
    None => false
  }
}


// Read a token from the lexer
function (lexer: *mut Lexer) next() -> result::Result<Tk, mpc::CompileError> {
  loop {
    let ch = lexer.get();

    // End of file
    if (&ch).is_none() { return result::ok(Tk::EndOfFile) }

    // Now we know we can unwrap
    let ch = ch.unwrap();

    // Whitespace
    if ch == '\n' || ch == '\r' || ch == '\t' || ch == ' ' { continue }

    // Comments
    if ch == '/' {
      if lexer.consume_eq('/') {
        while {
          let ch = lexer.get();
          if (&ch).is_none() { return result::err(mpc::CompileError::UnexpectedEndOfFile) }
          opt::unwrap(ch) != '\n'
        } {}
        continue
      }
      if lexer.consume_eq('*') {
        while {
          // Read until *
          while {
            let ch = lexer.get();
            if (&ch).is_none() { return result::err(mpc::CompileError::UnexpectedEndOfFile) }
            opt::unwrap(ch) != '*'
          } {}
          // Exit if reached a  /
          !lexer.consume_eq('/')
        } {}
      }
    }

    // Numeric literals
    if ch == '0' {
      if lexer.consume_eq('x') || lexer.consume_eq('X') {
        return match read_hex(lexer) {
          Ok(v) => result::ok(Tk::IntLit(v)),
          Err(v) => result::err(v)
        }
      }
      if lexer.consume_eq('o') || lexer.consume_eq('O') {
        return match read_oct(lexer) {
          Ok(v) => result::ok(Tk::IntLit(v)),
          Err(v) => result::err(v)
        }
      }
      if lexer.consume_eq('b') || lexer.consume_eq('B') {
        return match read_bin(lexer) {
          Ok(v) => result::ok(Tk::IntLit(v)),
          Err(v) => result::err(v)
        }
      }
    }

    if ch >= '0' && ch <= '9' {
      return match read_dec(lexer, ch as <Uintn>) {
        Ok(v) => result::ok(Tk::IntLit(v)),
        Err(v) => result::err(v)
      }
    }

    // Character literal
    if ch == '\'' { return read_chr(lexer) }

    // String literals
    if ch == '"' { return read_str(lexer, false) }
    if ch == 'c' && lexer.consume_eq('"') { return read_str(lexer, true) }

    // Identifier
    if ch == '_' ||
       ch >= 'a' && ch <= 'z' ||
       ch >= 'A' && ch <= 'Z' {

      let mut s = vec::new();
      (&s).push(ch);

      loop {
        let ch = lexer.peek();

        if (&ch).is_none() { break }
        let ch = ch.unwrap();

        if ch == '_' ||
           ch >= 'a' && ch <= 'z' ||
           ch >= 'A' && ch <= 'Z' ||
           ch >= '0' && ch <= '9' {
          (&s).push(ch);
          lexer.get();
        } else {
          return result::ok(check_kw(s))
        }
      }
    }

    // Symbols
    if ch == '(' { return result::ok(Tk::LParen) }
    if ch == ')' { return result::ok(Tk::RParen) }
    if ch == '[' { return result::ok(Tk::LSquare) }
    if ch == ']' { return result::ok(Tk::RSquare) }
    if ch == '{' { return result::ok(Tk::LCurly) }
    if ch == '}' { return result::ok(Tk::RCurly) }
    if ch == '<' {
      if lexer.consume_eq('<') {
        if lexer.consume_eq('=') { return result::ok(Tk::RmwLShift) }
        return result::ok(Tk::LShift)
      }
      if lexer.consume_eq('=') { return result::ok(Tk::LessEq) }
      return result::ok(Tk::LAngle)
    }
    if ch == '>' {
      if lexer.consume_eq('>') {
        if lexer.consume_eq('=') { return result::ok(Tk::RmwRShift) }
        return result::ok(Tk::RShift)
      }
      if lexer.consume_eq('=') { return result::ok(Tk::GreaterEq) }
      return result::ok(Tk::RAngle)
    }
    if ch == '&' {
      if lexer.consume_eq('&') { return result::ok(Tk::LogicAnd) }
      if lexer.consume_eq('=') { return result::ok(Tk::RmwBitAnd) }
      return result::ok(Tk::Amp)
    }
    if ch == '*' {
      if lexer.consume_eq('=') { return result::ok(Tk::RmwMul) }
      return result::ok(Tk::Star)
    }
    if ch == '+' {
      if lexer.consume_eq('=') { return result::ok(Tk::RmwAdd) }
      return result::ok(Tk::Plus)
    }
    if ch == '-' {
      if lexer.consume_eq('>') { return result::ok(Tk::Arrow) }
      if lexer.consume_eq('=') { return result::ok(Tk::RmwSub) }
      return result::ok(Tk::Minus)
    }
    if ch == '~' { return result::ok(Tk::Tilde) }
    if ch == '!' {
      if lexer.consume_eq('=') { return result::ok(Tk::ExclEq) }
      return result::ok(Tk::Excl)
    }
    if ch == '/' {
      if lexer.consume_eq('=') { return result::ok(Tk::RmwDiv) }
      return result::ok(Tk::Slash)
    }
    if ch == '%' {
      if lexer.consume_eq('=') { return result::ok(Tk::RmwMod) }
      return result::ok(Tk::Percent)
    }
    if ch == '|' {
      if lexer.consume_eq('|') { return result::ok(Tk::LogicOr) }
      if lexer.consume_eq('=') { return result::ok(Tk::RmwBitOr) }
      return result::ok(Tk::Pipe)
    }
    if ch == '^' {
      if lexer.consume_eq('=') { return result::ok(Tk::RmwBitXor) }
      return result::ok(Tk::Caret)
    }
    if ch == '=' {
      if lexer.consume_eq('>') { return result::ok(Tk::FatArrow) }
      if lexer.consume_eq('=') { return result::ok(Tk::EqEq) }
      return result::ok(Tk::Eq)
    }
    if ch == '.' {
      // FIXME: handle case of ..
      if lexer.consume_eq('.') && lexer.consume_eq('.') {
        return result::ok(Tk::Varargs)
      }
      return result::ok(Tk::Dot)
    }
    if ch == ',' { return result::ok(Tk::Comma) }
    if ch == ';' { return result::ok(Tk::Semi) }
    if ch == ':' {
      if lexer.consume_eq(':') { return result::ok(Tk::DColon) }
      return result::ok(Tk::Colon)
    }

    // Unrecognized character
    return result::err(mpc::CompileError::UnrecognizedCharacter(ch))
  }
}

// Read a character literal
function (lexer: *mut Lexer) read_chr() -> result::Result<Tk, mpc::CompileError> {
  loop {
    let ch = lexer.get();

    // Char literal must not contain EOF
    if (&ch).is_none() { return result::err(mpc::CompileError::UnexpectedEndOfFile) }

    // Otherwise we can unwrap
    let ch = ch.unwrap();
    if ch == '\'' { break }
    if ch == '\\' { lexer.read_esc(); }
  }

  return result::ok(Tk::IntLit(0)) // FIXME: derive value
}

// Read a string literal
function (lexer: *mut Lexer) read_str(is_c: Bool) -> result::Result<Tk, mpc::CompileError> {
  let mut s = vec::new();

  loop {
    let ch = lexer.get();

    // Stirng literal must not contain EOF
    if (&ch).is_none() { return result::err(mpc::CompileError::UnexpectedEndOfFile) }

    // Otherwise we can unwrap
    let ch = ch.unwrap();
    if ch == '"' { break }
    if ch == '\\' {
      match lexer.read_esc() {
        Ok(v) => (&s).push(v as <Uint8>),
        Err(v) => return result::err(v)
      }
    } else {
      (&s).push(ch)
    }
  }

  if is_c { return result::ok(Tk::CStrLit(s)) }
  else    { return result::ok(Tk::StrLit(s)) }
}

// Read an escape sequence
function (lexer: *mut Lexer) read_esc() -> result::Result<Uintn, mpc::CompileError> {
  let ch = lexer.get();

  // EOF here is always unexpected
  if (&ch).is_none() { return result::err(mpc::CompileError::UnexpectedEndOfFile) }

  // Otherwise check the escape sequence
  let ch = ch.unwrap();
  if ch == '0'  { return result::ok(0) }
  if ch == 'n'  { return result::ok('\n') }
  if ch == 'r'  { return result::ok('\r') }
  if ch == 't'  { return result::ok('\t') }
  if ch == '\\' { return result::ok('\\') }
  if ch == '\'' { return result::ok('\'') }
  if ch == '"'  { return result::ok('"') }
  if ch == 'x'  { return read_hex(lexer) }

  // Which might very well be considered invalid
  return result::err(mpc::CompileError::UnrecognizedEscapeSequence(ch))
}

// Read a hexadecimal literal
function (lexer: *mut Lexer) read_hex() -> result::Result<Uintn, mpc::CompileError> {
  let mut val: Uintn = 0;
  loop {
    let ch = lexer.peek();

    if (&ch).is_none() { break }
    let ch = ch.unwrap();

    if ch >= '0' && ch <= '9' {
      val = val * 16 + (ch - '0') as <Uintn>;
      lexer.get();
    } else if ch >= 'a' && ch <= 'f' {
      val = val * 16 + (ch - 'a' + 0xa) as <Uintn>;
      lexer.get();
    } else if ch >= 'A' && ch <= 'F' {
      val = val * 16 + (ch - 'a' + 0xa) as <Uintn>;
      lexer.get();
    } else {
      break
    }
  }
  return result::ok(val)
}

// Read a octal literal
function (lexer: *mut Lexer) read_oct() -> result::Result<Uintn, mpc::CompileError> {
  let mut val: Uintn = 0;
  loop {
    let ch = lexer.peek();

    if (&ch).is_none() { break }
    let ch = ch.unwrap();

    if ch >= '0' && ch <= '7' {
      val = val * 8 + (ch - '0') as <Uintn>;
      lexer.get();
    } else {
      break
    }
  }
  return result::ok(val)
}

// Read a binary literal
function (lexer: *mut Lexer) read_bin() -> result::Result<Uintn, mpc::CompileError> {
  let mut val: Uintn = 0;
  loop {
    let ch = lexer.peek();

    if (&ch).is_none() { break }
    let ch = ch.unwrap();

    if ch >= '0' && ch <= '1' {
      val = val * 2 + (ch - '0') as <Uintn>;
      lexer.get();
    } else {
      break
    }
  }
  return result::ok(val)
}

// Read a decimal literal
function (lexer: *mut Lexer) read_dec(mut val: Uintn) -> result::Result<Uintn, mpc::CompileError> {
  loop {
    let ch = lexer.peek();

    if (&ch).is_none() { break }
    let ch = ch.unwrap();

    if ch >= '0' && ch <= '9' {
      val = val * 10 + (ch - '0') as <Uintn>;
      lexer.get();
    } else {
      break
    }
  }
  return result::ok(val)
}

// Check if an identifier is a keyword
function check_kw(s: str::Str) -> Tk {
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Bool"))      { return Tk::TyBool }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Uint8"))     { return Tk::TyUint8 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Int8"))      { return Tk::TyInt8 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Uint16"))    { return Tk::TyUint16 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Int16"))     { return Tk::TyInt16 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Uint32"))    { return Tk::TyUint32 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Int32"))     { return Tk::TyInt32 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Uint64"))    { return Tk::TyUint64 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Int64"))     { return Tk::TyInt64 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Uintn"))     { return Tk::TyUintn }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Intn"))      { return Tk::TyIntn }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Float"))     { return Tk::TyFloat }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Double"))    { return Tk::TyDouble }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Function"))  { return Tk::TyFunction }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"as"))        { return Tk::KwAs }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"let"))       { return Tk::KwLet }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"mut"))       { return Tk::KwMut }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"continue"))  { return Tk::KwContinue }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"break"))     { return Tk::KwBreak }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"return"))    { return Tk::KwReturn }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"if"))        { return Tk::KwIf }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"else"))      { return Tk::KwElse }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"while"))     { return Tk::KwWhile }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"loop"))      { return Tk::KwLoop }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"match"))     { return Tk::KwMatch }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"nil"))       { return Tk::KwNil }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"true"))      { return Tk::KwTrue }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"false"))     { return Tk::KwFalse }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"struct"))    { return Tk::KwStruct }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"union"))     { return Tk::KwUnion }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"enum"))      { return Tk::KwEnum }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"type"))      { return Tk::KwType }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"function"))  { return Tk::KwFunction }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"const"))     { return Tk::KwConst }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"data"))      { return Tk::KwData }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"import"))    { return Tk::KwImport }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"extern"))    { return Tk::KwExtern }
  return Tk::Ident(s)
}
