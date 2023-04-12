import mpc
import opt
import prog
import result
import slice
import str
import vec

enum Token (
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

struct Lexer (input: slice::Slice<Uint8>, cur: Uintn)

// Create a new lexer instance for a file
function new(input: slice::Slice<Uint8>) -> Lexer {
  Lexer(input, 0)
}

// Read a token from the lexer
function next(lexer: *mut Lexer) -> result::Result<Token, mpc::CompileError> {
  loop {
    let ch = get(lexer);

    // End of file
    if opt::is_none(&ch) { return result::ok(Token::EndOfFile) }

    // Now we know we can unwrap
    let ch = opt::unwrap(ch);

    // Whitespace
    if ch == '\n' || ch == '\r' || ch == '\t' || ch == ' ' { continue }

    // Comments
    if ch == '/' {
      if consume_eq(lexer, '/') {
        while {
          let ch = get(lexer);
          if opt::is_none(&ch) { return result::err(mpc::CompileError::UnexpectedEndOfFile) }
          opt::unwrap(ch) != '\n'
        } {}
        continue
      }
      if consume_eq(lexer, '*') {
        while {
          // Read until *
          while {
            let ch = get(lexer);
            if opt::is_none(&ch) { return result::err(mpc::CompileError::UnexpectedEndOfFile) }
            opt::unwrap(ch) != '*'
          } {}
          // Exit if reached a  /
          !consume_eq(lexer, '/')
        } {}
      }
    }

    // Numeric literals
    if ch == '0' {
      if consume_eq(lexer, 'x') || consume_eq(lexer, 'X') {
        return match read_hex(lexer) {
          o: Ok => result::ok(Token::IntLit(o.v)),
          e: Err => result::err(e.v)
        }
      }
      if consume_eq(lexer, 'o') || consume_eq(lexer, 'O') {
        return match read_oct(lexer) {
          o: Ok => result::ok(Token::IntLit(o.v)),
          e: Err => result::err(e.v)
        }
      }
      if consume_eq(lexer, 'b') || consume_eq(lexer, 'B') {
        return match read_bin(lexer) {
          o: Ok => result::ok(Token::IntLit(o.v)),
          e: Err => result::err(e.v)
        }
      }
    }

    if ch >= '0' && ch <= '9' {
      return match read_dec(lexer, ch as <Uintn>) {
        o: Ok => result::ok(Token::IntLit(o.v)),
        e: Err => result::err(e.v)
      }
    }

    // Character literal
    if ch == '\'' { return read_chr(lexer) }

    // String literals
    if ch == '"' { return read_str(lexer, false) }
    if ch == 'c' && consume_eq(lexer, '"') { return read_str(lexer, true) }

    // Identifier
    if ch == '_' ||
       ch >= 'a' && ch <= 'z' ||
       ch >= 'A' && ch <= 'Z' {

      let mut s = vec::new();

      loop {
        let ch = peek(lexer);

        if opt::is_none(&ch) { break }
        let ch = opt::unwrap(ch);

        if ch == '_' ||
           ch >= 'a' && ch <= 'z' ||
           ch >= 'A' && ch <= 'Z' ||
           ch >= '0' && ch <= '9' {
          vec::push(&s, ch);
          get(lexer);
        } else {
          return result::ok(check_kw(s))
        }
      }
    }

    // Symbols
    if ch == '(' { return result::ok(Token::LParen) }
    if ch == ')' { return result::ok(Token::RParen) }
    if ch == '[' { return result::ok(Token::LSquare) }
    if ch == ']' { return result::ok(Token::RSquare) }
    if ch == '{' { return result::ok(Token::LCurly) }
    if ch == '}' { return result::ok(Token::RCurly) }
    if ch == '<' {
      if consume_eq(lexer, '<') {
        if consume_eq(lexer, '=') { return result::ok(Token::RmwLShift) }
        return result::ok(Token::LShift)
      }
      if consume_eq(lexer, '=') { return result::ok(Token::LessEq) }
      return result::ok(Token::LAngle)
    }
    if ch == '>' {
      if consume_eq(lexer, '>') {
        if consume_eq(lexer, '=') { return result::ok(Token::RmwRShift) }
        return result::ok(Token::RShift)
      }
      if consume_eq(lexer, '=') { return result::ok(Token::GreaterEq) }
      return result::ok(Token::RAngle)
    }
    if ch == '&' {
      if consume_eq(lexer, '&') { return result::ok(Token::LogicAnd) }
      if consume_eq(lexer, '=') { return result::ok(Token::RmwBitAnd) }
      return result::ok(Token::Amp)
    }
    if ch == '*' {
      if consume_eq(lexer, '=') { return result::ok(Token::RmwMul) }
      return result::ok(Token::Star)
    }
    if ch == '+' {
      if consume_eq(lexer, '=') { return result::ok(Token::RmwAdd) }
      return result::ok(Token::Plus)
    }
    if ch == '-' {
      if consume_eq(lexer, '>') { return result::ok(Token::Arrow) }
      if consume_eq(lexer, '=') { return result::ok(Token::RmwSub) }
      return result::ok(Token::Minus)
    }
    if ch == '~' { return result::ok(Token::Tilde) }
    if ch == '!' {
      if consume_eq(lexer, '=') { return result::ok(Token::ExclEq) }
      return result::ok(Token::Excl)
    }
    if ch == '/' {
      if consume_eq(lexer, '=') { return result::ok(Token::RmwDiv) }
      return result::ok(Token::Slash)
    }
    if ch == '%' {
      if consume_eq(lexer, '=') { return result::ok(Token::RmwMod) }
      return result::ok(Token::Percent)
    }
    if ch == '|' {
      if consume_eq(lexer, '|') { return result::ok(Token::LogicOr) }
      if consume_eq(lexer, '=') { return result::ok(Token::RmwBitOr) }
      return result::ok(Token::Pipe)
    }
    if ch == '^' {
      if consume_eq(lexer, '=') { return result::ok(Token::RmwBitXor) }
      return result::ok(Token::Caret)
    }
    if ch == '=' {
      if consume_eq(lexer, '>') { return result::ok(Token::FatArrow) }
      if consume_eq(lexer, '=') { return result::ok(Token::EqEq) }
      return result::ok(Token::Eq)
    }
    if ch == '.' {
      // FIXME: handle case of ..
      if consume_eq(lexer, '.') && consume_eq(lexer, '.') {
        return result::ok(Token::Varargs)
      }
      return result::ok(Token::Dot)
    }
    if ch == ',' { return result::ok(Token::Comma) }
    if ch == ';' { return result::ok(Token::Semi) }
    if ch == ':' {
      if consume_eq(lexer, ':') { return result::ok(Token::DColon) }
      return result::ok(Token::Colon)
    }

    // Unrecognized character
    return result::err(mpc::CompileError::UnrecognizedCharacter(ch))
  }
}

// Read a character literal
function read_chr(lexer: *mut Lexer) -> result::Result<Token, mpc::CompileError> {
  loop {
    let ch = get(lexer);

    // Char literal must not contain EOF
    if opt::is_none(&ch) { return result::err(mpc::CompileError::UnexpectedEndOfFile) }

    // Otherwise we can unwrap
    let ch = opt::unwrap(ch);
    if ch == '\'' { break }
    if ch == '\\' { read_esc(lexer); }
  }

  return result::ok(Token::IntLit(0)) // FIXME: derive value
}

// Read a string literal
function read_str(lexer: *mut Lexer, is_c: Bool) -> result::Result<Token, mpc::CompileError> {
  let mut s = vec::new();

  loop {
    let ch = get(lexer);

    // Stirng literal must not contain EOF
    if opt::is_none(&ch) { return result::err(mpc::CompileError::UnexpectedEndOfFile) }

    // Otherwise we can unwrap
    let ch = opt::unwrap(ch);
    if ch == '"' { break }
    if ch == '\\' {
      match read_esc(lexer) {
        o: Ok => vec::push(&s, o.v as <Uint8>),
        e: Err => return result::err(e.v)
      }
    } else {
      vec::push(&s, ch)
    }
  }

  if is_c { return result::ok(Token::CStrLit(s)) }
  else    { return result::ok(Token::StrLit(s)) }
}

// Read an escape sequence
function read_esc(lexer: *mut Lexer) -> result::Result<Uintn, mpc::CompileError> {
  let ch = get(lexer);

  // EOF here is always unexpected
  if opt::is_none(&ch) { return result::err(mpc::CompileError::UnexpectedEndOfFile) }

  // Otherwise check the escape sequence
  let ch = opt::unwrap(ch);
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
function read_hex(lexer: *mut Lexer) -> result::Result<Uintn, mpc::CompileError> {
  let mut val: Uintn = 0;
  loop {
    let ch = peek(lexer);

    if opt::is_none(&ch) { break }
    let ch = opt::unwrap(ch);

    if ch >= '0' && ch <= '9' {
      val = val * 16 + (ch - '0') as <Uintn>;
      get(lexer);
    } else if ch >= 'a' && ch <= 'f' {
      val = val * 16 + (ch - 'a' + 0xa) as <Uintn>;
      get(lexer);
    } else if ch >= 'A' && ch <= 'F' {
      val = val * 16 + (ch - 'a' + 0xa) as <Uintn>;
      get(lexer);
    } else {
      break
    }
  }
  return result::ok(val)
}

// Read a octal literal
function read_oct(lexer: *mut Lexer) -> result::Result<Uintn, mpc::CompileError> {
  let mut val: Uintn = 0;
  loop {
    let ch = peek(lexer);

    if opt::is_none(&ch) { break }
    let ch = opt::unwrap(ch);

    if ch >= '0' && ch <= '7' {
      val = val * 8 + (ch - '0') as <Uintn>;
      get(lexer);
    } else {
      break
    }
  }
  return result::ok(val)
}

// Read a binary literal
function read_bin(lexer: *mut Lexer) -> result::Result<Uintn, mpc::CompileError> {
  let mut val: Uintn = 0;
  loop {
    let ch = peek(lexer);

    if opt::is_none(&ch) { break }
    let ch = opt::unwrap(ch);

    if ch >= '0' && ch <= '1' {
      val = val * 2 + (ch - '0') as <Uintn>;
      get(lexer);
    } else {
      break
    }
  }
  return result::ok(val)
}

// Read a decimal literal
function read_dec(lexer: *mut Lexer, mut val: Uintn) -> result::Result<Uintn, mpc::CompileError> {
  loop {
    let ch = peek(lexer);

    if opt::is_none(&ch) { break }
    let ch = opt::unwrap(ch);

    if ch >= '0' && ch <= '9' {
      val = val * 10 + (ch - '0') as <Uintn>;
      get(lexer);
    } else {
      break
    }
  }
  return result::ok(val)
}

// Check if an identifier is a keyword
function check_kw(s: str::Str) -> Token {
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Bool"))      { return Token::TyBool }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Uint8"))     { return Token::TyUint8 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Int8"))      { return Token::TyInt8 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Uint16"))    { return Token::TyUint16 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Int16"))     { return Token::TyInt16 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Uint32"))    { return Token::TyUint32 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Int32"))     { return Token::TyInt32 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Uint64"))    { return Token::TyUint64 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Int64"))     { return Token::TyInt64 }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Uintn"))     { return Token::TyUintn }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Intn"))      { return Token::TyIntn }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Float"))     { return Token::TyFloat }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Double"))    { return Token::TyDouble }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"Function"))  { return Token::TyFunction }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"as"))        { return Token::KwAs }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"let"))       { return Token::KwLet }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"mut"))       { return Token::KwMut }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"continue"))  { return Token::KwContinue }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"break"))     { return Token::KwBreak }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"return"))    { return Token::KwReturn }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"if"))        { return Token::KwIf }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"else"))      { return Token::KwElse }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"while"))     { return Token::KwWhile }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"loop"))      { return Token::KwLoop }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"match"))     { return Token::KwMatch }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"nil"))       { return Token::KwNil }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"true"))      { return Token::KwTrue }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"false"))     { return Token::KwFalse }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"struct"))    { return Token::KwStruct }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"union"))     { return Token::KwUnion }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"enum"))      { return Token::KwEnum }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"type"))      { return Token::KwType }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"function"))  { return Token::KwFunction }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"const"))     { return Token::KwConst }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"data"))      { return Token::KwData }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"import"))    { return Token::KwImport }
  if str::eq(str::view_from_str(&s), str::view_from_lit(&"extern"))    { return Token::KwExtern }
  return Token::Ident(s)
}

// Read the next input character
function get(lexer: *mut Lexer) -> opt::Option<Uint8> {
  match slice::at_or_none((*lexer).input, (*lexer).cur) {
    s: Some => {
      (*lexer).cur += 1;
      opt::some(*s.val)
    },
    None => opt::none()
  }
}


// Peek at the next input character
function peek(lexer: *mut Lexer) -> opt::Option<Uint8> {
  match slice::at_or_none((*lexer).input, (*lexer).cur) {
    s: Some => opt::some(*s.val),
    None => opt::none()
  }
}

// Consume the next input character if equal
function consume_eq(lexer: *mut Lexer, want: Uint8) -> Bool {
  match slice::at_or_none((*lexer).input, (*lexer).cur) {
    s: Some => {
      if *s.val == want {
        (*lexer).cur += 1;
        true
      } else {
        false
      }
    },
    None => false
  }
}
