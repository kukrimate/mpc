/*
 * Copyright (c) 2022-2023, Mate Kukri
 * SPDX-License-Identifier: GPL-2.0-only
 */

use super::*;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::str::FromStr;

pub struct Lexer {
  keywords: HashMap<&'static str, Token>,
  file: std::sync::Arc<SourceFile>,
  begin: usize,
  end: usize,
  line: usize,
  column: usize
}

#[derive(Clone, Debug)]
pub enum Token {
  EndOfFile,
  Ident(RefStr),    // [_a-zA-Z][_a-zA-Z0-9]*
  IntLit(usize),    // [0-9]+
                    // 0[xX][a-fA-f0-9]+
                    // 0[oO][0-7]+
                    // 0[bB][0-1]+
  FltLit(f64),      // [0-9]*[.][0-9]+([eE][+-]?[0-9]+)?
  StrLit(Vec<u8>),  // "([^"]|\")*"
  CStrLit(Vec<u8>), // c"([^"]|\")*"
  TyBool,           // Bool
  TyUint8,          // Uint8
  TyInt8,           // Int8
  TyUint16,         // Uint16
  TyInt16,          // Int16
  TyUint32,         // Uint32
  TyInt32,          // Int32
  TyUint64,         // Uint64
  TyInt64,          // Int64
  TyUintn,          // Uintn
  TyIntn,           // Intn
  TyFloat,          // Float
  TyDouble,         // Double
  TyFunction,       // Function
  KwAs,             // as
  KwLet,            // let
  KwMut,            // mut
  KwContinue,       // continue
  KwBreak,          // break
  KwReturn,         // return
  KwIf,             // if
  KwElse,           // else
  KwWhile,          // while
  KwLoop,           // loop
  KwMatch,          // match
  KwNil,            // nil
  KwTrue,           // true
  KwFalse,          // false
  KwStruct,         // struct
  KwUnion,          // union
  KwEnum,           // enum
  KwType,           // type
  KwFunction,       // function
  KwConst,          // const
  KwData,           // data
  KwImport,         // import
  KwExtern,         // extern
  LParen,           // (
  RParen,           // )
  LSquare,          // [
  RSquare,          // ]
  LCurly,           // {
  RCurly,           // }
  LAngle,           // <
  RAngle,           // >
  Amp,              // &
  Star,             // *
  Plus,             // +
  Minus,            // -
  Tilde,            // ~
  Excl,             // !
  Slash,            // /
  Percent,          // %
  Pipe,             // |
  Caret,            // ^
  Eq,               // =
  Dot,              // .
  Comma,            // ,
  Semi,             // ;
  Colon,            // :
  LShift,           // <<
  RShift,           // >>
  DColon,           // ::
  Arrow,            // ->
  FatArrow,         // =>
  EqEq,             // ==
  ExclEq,           // !=
  LessEq,           // <=
  GreaterEq,        // >=
  LogicAnd,         // &&
  LogicOr,          // ||
  RmwAdd,           // +=
  RmwSub,           // -=
  RmwMul,           // *=
  RmwDiv,           // /=
  RmwMod,           // %=
  RmwLShift,        // <<=
  RmwRShift,        // >>=
  RmwBitAnd,        // &=
  RmwBitOr,         // |=
  RmwBitXor,        // ^=
  Varargs           // ...
}

impl Lexer {
  pub fn new(file: std::sync::Arc<SourceFile>) -> Self {
    let keywords = HashMap::from([
      ("Bool", Token::TyBool),
      ("Uint8", Token::TyUint8),
      ("Int8", Token::TyInt8),
      ("Uint16", Token::TyUint16),
      ("Int16", Token::TyInt16),
      ("Uint32", Token::TyUint32),
      ("Int32", Token::TyInt32),
      ("Uint64", Token::TyUint64),
      ("Int64", Token::TyInt64),
      ("Uintn", Token::TyUintn),
      ("Intn", Token::TyIntn),
      ("Float", Token::TyFloat),
      ("Double", Token::TyDouble),
      ("Function", Token::TyFunction),
      ("as", Token::KwAs),
      ("let", Token::KwLet),
      ("mut", Token::KwMut),
      ("continue", Token::KwContinue),
      ("break", Token::KwBreak),
      ("return", Token::KwReturn),
      ("if", Token::KwIf),
      ("else", Token::KwElse),
      ("while", Token::KwWhile),
      ("loop", Token::KwLoop),
      ("match", Token::KwMatch),
      ("nil", Token::KwNil),
      ("true", Token::KwTrue),
      ("false", Token::KwFalse),
      ("struct", Token::KwStruct),
      ("type", Token::KwType),
      ("union", Token::KwUnion),
      ("enum", Token::KwEnum),
      ("function", Token::KwFunction),
      ("const", Token::KwConst),
      ("data", Token::KwData),
      ("import", Token::KwImport),
      ("extern", Token::KwExtern),
    ]);

    Lexer {
      keywords,
      file,
      begin: 0,
      end: 0,
      line: 1,
      column: 1
    }
  }

  pub fn next(&mut self) -> Result<(SourceLocation, Token), CompileError> {
    loop {
      // Save beginning of token
      self.begin = self.end;
      // Save starting location
      let loc = SourceLocation { file: self.file.clone(), line: self.line, column: self.column };

      // Read character or bail on EOF
      let byte = if let Some(byte) = self.consume_byte() {
        byte
      } else {
        return Ok((loc, Token::EndOfFile))
      };

      // Decide next state after seeing initial char
      let token = match byte {
        // Whitespaces
        b'\n' => {
          self.handle_newline();
          continue
        }
        b'\r' | b'\t' | b' ' => continue,
        // C string literals
        b'c' if self.consume(b'"') => loop {
          match self.consume_byte() {
            Some(b'\n') | None => {
              return Err(CompileError::UnterminatedStr(loc))
            }
            Some(b'"') => {
              let s = self.slice();
              match unescape(loc.clone(), &s[2..s.len() - 1]) {
                Ok(v) => break Token::CStrLit(v),
                Err(err) => return Err(err),
              }
            },
            Some(_) => (),
          }
        }
        // Identifiers
        b'_' | b'a'..=b'z' | b'A'..=b'Z' => self.read_ident(),
        // Numeric literals
        b'0' => match self.peek_byte() {
          Some(b'b' | b'B') => { // Binary
            self.consume_byte();
            self.read_binary()
          }
          Some(b'o' | b'O') => { // Octal
            self.consume_byte();
            self.read_octal()
          }
          Some(b'x' | b'X') => { // Hexadecimal
            self.consume_byte();
            self.read_hex()
          }
          _ => self.read_decimal()
        }
        b'1'..=b'9' => self.read_decimal(),
        // String literals
        b'"' => loop {
          match self.consume_byte() {
            Some(b'\n') | None => {
              return Err(CompileError::UnterminatedStr(loc))
            }
            Some(b'\\') => {
              self.consume_byte();
            }
            Some(b'"') => {
              let s = self.slice();
              match unescape(loc.clone(), &s[1..s.len() - 1]) {
                Ok(v) => break Token::StrLit(v),
                Err(err) => return Err(err),
              }
            },
            Some(_) => (),
          }
        }
        // Character literals
        b'\'' => loop {
          match self.consume_byte() {
            Some(b'\n') | None => {
              return Err(CompileError::UnterminatedChar(loc))
            }
            Some(b'\\') => {
              self.consume_byte();
            }
            Some(b'\'') => {
              let s = self.slice();
              match unescape(loc.clone(), &s[1..s.len() - 1]) {
                Ok(v) if v.len() == 1 => {
                  break Token::IntLit(v[0] as usize)
                }
                Ok(_) => {
                  return Err(CompileError::InvalidChar(loc))
                }
                Err(err) => {
                  return Err(err)
                }
              }
            },
            Some(_) => (),
          }
        }
        b'(' => Token::LParen,
        b')' => Token::RParen,
        b'[' => Token::LSquare,
        b']' => Token::RSquare,
        b'{' => Token::LCurly,
        b'}' => Token::RCurly,
        b'<' => match self.peek_byte() {
          Some(b'<') => {
            self.consume_byte();
            match self.peek_byte() {
              Some(b'=') => {
                self.consume_byte();
                Token::RmwLShift
              }
              _ => Token::LShift
            }
          }
          Some(b'=') => {
            self.consume_byte();
            Token::LessEq
          }
          _ => Token::LAngle
        }
        b'>' => match self.peek_byte() {
          Some(b'>') => {
            self.consume_byte();
            match self.peek_byte() {
              Some(b'=') => {
                self.consume_byte();
                Token::RmwRShift
              }
              _ => Token::RShift
            }
          }
          Some(b'=') => {
            self.consume_byte();
            Token::GreaterEq
          }
          _ => Token::RAngle
        }
        b'&' => match self.peek_byte() {
          Some(b'=') => {
            self.consume_byte();
            Token::RmwBitAnd
          }
          Some(b'&') => {
            self.consume_byte();
            Token::LogicAnd
          }
          _ => Token::Amp
        }
        b'*' => match self.peek_byte() {
          Some(b'=') => {
            self.consume_byte();
            Token::RmwMul
          }
          _ => Token::Star
        }
        b'+' => match self.peek_byte() {
          Some(b'=') => {
            self.consume_byte();
            Token::RmwAdd
          }
          _ => Token::Plus
        }
        b'-' => match self.peek_byte() {
          Some(b'=') => {
            self.consume_byte();
            Token::RmwSub
          }
          Some(b'>') => {
            self.consume_byte();
            Token::Arrow
          }
          _ => Token::Minus
        }
        b'~' => Token::Tilde,
        b'!' => match self.peek_byte() {
          Some(b'=') => {
            self.consume_byte();
            Token::ExclEq
          }
          _ => Token::Excl
        }
        b'/' => match self.peek_byte() {
          Some(b'/') => {
            self.consume_byte();
            while match self.consume_byte() {
              Some(b'\n') => {
                self.handle_newline();
                false
              }
              None => false,
              Some(_) => true
            } {}
            continue
          }
          Some(b'*') => {
            self.consume_byte();
            while match self.consume_byte() {
              None => {
                return Err(CompileError::UnterminatedComment(loc))
              }
              Some(b'*') if matches!(self.peek_byte(), Some(b'/')) => {
                self.consume_byte();
                false
              }
              Some(b'\n') => {
                self.handle_newline();
                true
              }
              _ => true
            } {}
            continue
          }
          Some(b'=') => {
            self.consume_byte();
            Token::RmwDiv
          }
          _ => Token::Slash
        }
        b'%' => match self.peek_byte() {
          Some(b'=') => {
            self.consume_byte();
            Token::RmwMod
          }
          _ => Token::Percent
        }
        b'|' => match self.peek_byte() {
          Some(b'=') => {
            self.consume_byte();
            Token::RmwBitOr
          }
          Some(b'|') => {
            self.consume_byte();
            Token::LogicOr
          }
          _ => Token::Pipe
        }
        b'^' => match self.peek_byte() {
          Some(b'=') => {
            self.consume_byte();
            Token::RmwBitXor
          }
          _ => Token::Caret
        }
        b'=' => match self.peek_byte() {
          Some(b'=') => {
            self.consume_byte();
            Token::EqEq
          }
          Some(b'>') => {
            self.consume_byte();
            Token::FatArrow
          }
          _ => Token::Eq
        }
        b'.' => match self.peek_bytes() {
          Some(b"..") => {
            self.consume_byte();
            self.consume_byte();
            Token::Varargs
          }
          _ => Token::Dot
        }
        b',' => Token::Comma,
        b';' => Token::Semi,
        b':' => match self.peek_byte() {
          Some(b':') => {
            self.consume_byte();
            Token::DColon
          }
          _ => {
            Token::Colon
          }
        }
        _ => return Err(CompileError::UnknownToken(loc))
      };

      return Ok((loc, token))
    }
  }

  fn handle_newline(&mut self) {
    self.line += 1;
    self.column = 1;
  }

  fn read_ident(&mut self) -> Token {
    loop {
      match self.peek_byte() {
        Some(b'_' | b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9') => {
          self.consume_byte();
        }
        _ => break
      }
    }

    if let Some(kw) = self.keywords.get(self.slice()) {
      kw.clone()
    } else {
      Token::Ident(RefStr::new(self.slice()))
    }
  }

  fn read_binary(&mut self) -> Token {
    loop {
      match self.peek_byte() {
        Some(b'0'..=b'1') => {
          self.consume_byte();
        }
        _ => break
      }
    }
    Token::IntLit(usize::from_str_radix(&self.slice()[2..], 2).unwrap())
  }

  fn read_octal(&mut self) -> Token {
    loop {
      match self.peek_byte() {
        Some(b'0'..=b'7') => {
          self.consume_byte();
        }
        _ => break
      }
    }
    Token::IntLit(usize::from_str_radix(&self.slice()[2..], 8).unwrap())
  }

  fn read_hex(&mut self) -> Token {
    loop {
      match self.peek_byte() {
        Some(b'0'..=b'9') => {
          self.consume_byte();
        }
        Some(b'a'..=b'f') => {
          self.consume_byte();
        }
        Some(b'A'..=b'F') => {
          self.consume_byte();
        }
        _ => break
      }
    }
    Token::IntLit(usize::from_str_radix(&self.slice()[2..], 16).unwrap())
  }

  fn read_decimal(&mut self) -> Token {
    let mut is_flt = false;

    // Read whole part
    self.read_decimal_digits();

    // Read fractional part
    if self.consume(b'.') {
      is_flt = true;
      self.read_decimal_digits();
    }

    // Read exponent
    if self.consume(b'e') || self.consume(b'E') {
      is_flt = true;
      let _ = self.consume(b'+') || self.consume(b'-');
      self.read_decimal_digits();
    }

    if is_flt {
      Token::FltLit(f64::from_str(self.slice()).unwrap())
    } else {
      Token::IntLit(usize::from_str(self.slice()).unwrap())
    }
  }

  fn read_decimal_digits(&mut self) {
    loop {
      match self.peek_byte() {
        Some(b'0'..=b'9') => {
          self.consume_byte();
        }
        _ => break
      }
    }
  }

  #[inline(always)]
  fn peek_byte(&self) -> Option<u8> {
    self.file.data.as_bytes().get(self.end).cloned()
  }

  #[inline(always)]
  fn peek_bytes<const N: usize>(&self) -> Option<&[u8; N]> {
    self.file.data.as_bytes()
      .get(self.end..self.end+N)
      .map(|slice| <&[u8; N]>::try_from(slice).unwrap())
  }

  #[inline(always)]
  fn consume_byte(&mut self) -> Option<u8> {
    self.column += 1;
    let byte = self.peek_byte()?;
    self.end += 1;
    Some(byte)
  }

  #[inline(always)]
  fn consume(&mut self, desired: u8) -> bool {
    match self.peek_byte() {
      Some(byte) if byte == desired => {
        self.consume_byte();
        true
      }
      _ => false
    }
  }

  #[inline(always)]
  fn slice(&self) -> &str {
    &self.file.data[self.begin..self.end]
  }
}

fn unescape(loc: SourceLocation, s: &str) -> Result<Vec<u8>, CompileError> {
  let mut iterator = s.bytes().peekable();
  let mut buffer = Vec::new();

  loop {
    match iterator.next() {
      Some(b'\\') => {
        match iterator.next() {
          Some(b'0') => { buffer.push(b'\0'); }
          Some(b'n') => { buffer.push(b'\n'); }
          Some(b'r') => { buffer.push(b'\r'); }
          Some(b't') => { buffer.push(b'\t'); }
          Some(b'\\') => { buffer.push(b'\\'); }
          Some(b'\'') => { buffer.push(b'\''); }
          Some(b'"') => { buffer.push(b'"'); }
          Some(b'x') => {
            let mut byte = 0u8;
            loop {
              match iterator.peek() {
                Some(digit @ b'0'..=b'9') => {
                  byte = byte * 16 + digit - b'0';
                  iterator.next();
                }
                Some(digit @ b'a'..=b'f') => {
                  byte = byte * 16 + digit - b'a' + 0xa;
                  iterator.next();
                }
                Some(digit @ b'A'..=b'F') => {
                  byte = byte * 16 + digit - b'A' + 0xa;
                  iterator.next();
                }
                _ => break
              }
            }
            buffer.push(byte);
          }
          _ => { return Err(CompileError::UnknownEscape(loc)) }
        }
      }
      Some(byte) => {
        buffer.push(byte);
      }
      None => {
        return Ok(buffer)
      }
    }
  }
}
