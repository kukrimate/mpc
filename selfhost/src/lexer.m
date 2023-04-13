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
function (lexer: *mut Lexer) next() -> result::Result<Token, mpc::CompileError> {
  loop {
    let ch = lexer.get();

    // End of file
    if (&ch).is_none() { return result::ok(Token::EndOfFile) }

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
          Ok(v) => result::ok(Token::IntLit(v)),
          Err(v) => result::err(v)
        }
      }
      if lexer.consume_eq('o') || lexer.consume_eq('O') {
        return match read_oct(lexer) {
          Ok(v) => result::ok(Token::IntLit(v)),
          Err(v) => result::err(v)
        }
      }
      if lexer.consume_eq('b') || lexer.consume_eq('B') {
        return match read_bin(lexer) {
          Ok(v) => result::ok(Token::IntLit(v)),
          Err(v) => result::err(v)
        }
      }
    }

    if ch >= '0' && ch <= '9' {
      return match read_dec(lexer, ch as <Uintn>) {
        Ok(v) => result::ok(Token::IntLit(v)),
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
    if ch == '(' { return result::ok(Token::LParen) }
    if ch == ')' { return result::ok(Token::RParen) }
    if ch == '[' { return result::ok(Token::LSquare) }
    if ch == ']' { return result::ok(Token::RSquare) }
    if ch == '{' { return result::ok(Token::LCurly) }
    if ch == '}' { return result::ok(Token::RCurly) }
    if ch == '<' {
      if lexer.consume_eq('<') {
        if lexer.consume_eq('=') { return result::ok(Token::RmwLShift) }
        return result::ok(Token::LShift)
      }
      if lexer.consume_eq('=') { return result::ok(Token::LessEq) }
      return result::ok(Token::LAngle)
    }
    if ch == '>' {
      if lexer.consume_eq('>') {
        if lexer.consume_eq('=') { return result::ok(Token::RmwRShift) }
        return result::ok(Token::RShift)
      }
      if lexer.consume_eq('=') { return result::ok(Token::GreaterEq) }
      return result::ok(Token::RAngle)
    }
    if ch == '&' {
      if lexer.consume_eq('&') { return result::ok(Token::LogicAnd) }
      if lexer.consume_eq('=') { return result::ok(Token::RmwBitAnd) }
      return result::ok(Token::Amp)
    }
    if ch == '*' {
      if lexer.consume_eq('=') { return result::ok(Token::RmwMul) }
      return result::ok(Token::Star)
    }
    if ch == '+' {
      if lexer.consume_eq('=') { return result::ok(Token::RmwAdd) }
      return result::ok(Token::Plus)
    }
    if ch == '-' {
      if lexer.consume_eq('>') { return result::ok(Token::Arrow) }
      if lexer.consume_eq('=') { return result::ok(Token::RmwSub) }
      return result::ok(Token::Minus)
    }
    if ch == '~' { return result::ok(Token::Tilde) }
    if ch == '!' {
      if lexer.consume_eq('=') { return result::ok(Token::ExclEq) }
      return result::ok(Token::Excl)
    }
    if ch == '/' {
      if lexer.consume_eq('=') { return result::ok(Token::RmwDiv) }
      return result::ok(Token::Slash)
    }
    if ch == '%' {
      if lexer.consume_eq('=') { return result::ok(Token::RmwMod) }
      return result::ok(Token::Percent)
    }
    if ch == '|' {
      if lexer.consume_eq('|') { return result::ok(Token::LogicOr) }
      if lexer.consume_eq('=') { return result::ok(Token::RmwBitOr) }
      return result::ok(Token::Pipe)
    }
    if ch == '^' {
      if lexer.consume_eq('=') { return result::ok(Token::RmwBitXor) }
      return result::ok(Token::Caret)
    }
    if ch == '=' {
      if lexer.consume_eq('>') { return result::ok(Token::FatArrow) }
      if lexer.consume_eq('=') { return result::ok(Token::EqEq) }
      return result::ok(Token::Eq)
    }
    if ch == '.' {
      // FIXME: handle case of ..
      if lexer.consume_eq('.') && lexer.consume_eq('.') {
        return result::ok(Token::Varargs)
      }
      return result::ok(Token::Dot)
    }
    if ch == ',' { return result::ok(Token::Comma) }
    if ch == ';' { return result::ok(Token::Semi) }
    if ch == ':' {
      if lexer.consume_eq(':') { return result::ok(Token::DColon) }
      return result::ok(Token::Colon)
    }

    // Unrecognized character
    return result::err(mpc::CompileError::UnrecognizedCharacter(ch))
  }
}

// Read a character literal
function (lexer: *mut Lexer) read_chr() -> result::Result<Token, mpc::CompileError> {
  loop {
    let ch = lexer.get();

    // Char literal must not contain EOF
    if (&ch).is_none() { return result::err(mpc::CompileError::UnexpectedEndOfFile) }

    // Otherwise we can unwrap
    let ch = ch.unwrap();
    if ch == '\'' { break }
    if ch == '\\' { lexer.read_esc(); }
  }

  return result::ok(Token::IntLit(0)) // FIXME: derive value
}

// Read a string literal
function (lexer: *mut Lexer) read_str(is_c: Bool) -> result::Result<Token, mpc::CompileError> {
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

  if is_c { return result::ok(Token::CStrLit(s)) }
  else    { return result::ok(Token::StrLit(s)) }
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

import libc

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
