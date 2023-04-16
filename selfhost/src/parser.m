import box
import lexer
import mpc
import opt
import result
import slice
import str
import vec

enum Ty (
  _Bool,
  _Uint8,
  _Int8,
  _Uint16,
  _Int16,
  _Uint32,
  _Int32,
  _Uint64,
  _Int64,
  _Uintn,
  _Intn,
  _Float,
  _Double,
  Inst(path: Path, ty_args: vec::Vec<Ty>),
  Ptr(is_mut: Bool, base_ty: box::Box<Ty>),
  Func(params: vec::Vec<Param>, ret_ty: box::Box<Ty>),
  Arr(elem_cnt: box::Box<Expr>, elem_ty: box::Box<Ty>),
  Unit,
  Tuple(params: vec::Vec<Param>)
)

type Path = vec::Vec<str::Str>

type Param = (name: str::Str, ty: Ty)

enum Expr (
  Inst(path: Path, ty_args: vec::Vec<Ty>),
  Nil,
  _Bool(val: Bool),
  Int(val: Uintn),
  Flt(val: Double),
  Str(val: str::Str),
  CStr(val: str::Str),
  Unit,
  Tuple(args: vec::Vec<Arg>),
  Arr(elements: vec::Vec<Expr>),
  Dot (
    base: box::Box<Expr>,
    field: str::Str
  ),
  Call (
    called: box::Box<Expr>,
    args: vec::Vec<Arg>
  ),
  Index (
    base: box::Box<Expr>,
    index: box::Box<Expr>
  ),
  Adr(base: box::Box<Expr>),
  Ind (
    base: box::Box<Expr>
  ),
  Un (
    op: UnOp,
    base: box::Box<Expr>
  ),
  LNot (
    base: box::Box<Expr>
  ),
  Cast (
    base: box::Box<Expr>,
    dest_ty: Ty
  ),
  Bin (
    op: BinOp,
    lhs: box::Box<Expr>,
    rhs: box::Box<Expr>
  ),
  LAnd (
    lhs: box::Box<Expr>,
    rhs: box::Box<Expr>
  ),
  LOr (
    lhs: box::Box<Expr>,
    rhs: box::Box<Expr>
  ),
  Block(body: vec::Vec<Expr>),
  As (
    dst: box::Box<Expr>,
    src: box::Box<Expr>
  ),
  Rmw (
    op: BinOp,
    lhs: box::Box<Expr>,
    rhs: box::Box<Expr>
  ),
  Continue,
  Break(base: box::Box<Expr>),
  Return(base: box::Box<Expr>),
  Let (
    name: str::Str,
    is_mut: Bool,
    ty: opt::Option<Ty>,
    init: opt::Option<box::Box<Expr> >
  ),
  If (
    cond: box::Box<Expr>,
    tbody: box::Box<Expr>,
    ebody: box::Box<Expr>
  ),
  While (
    cond: box::Box<Expr>,
    body: box::Box<Expr>
  ),
  Loop(body: box::Box<Expr>),
  Match (
    cond: box::Box<Expr>,
    patterns: vec::Vec<(pat: Pattern, val: Expr)>
  )
)

type Arg = (
  name: opt::Option<str::Str>,
  val: box::Box<Expr>
)

enum UnOp (
  Plus, Minus, Not
)

enum BinOp (
  Mul, Div, Mod, Add, Sub, Lsh, Rsh, And, Xor, Or, Eq, Ne, Lt, Gt, Le, Ge
)

enum Pattern (
  Any,
  Unit(name: str::Str),
  Struct (
    name: str::Str,
    fields: vec::Vec<str::Str>
  )
)

struct Parser (lexer: lexer::Lexer)

function new(input: slice::Slice<Uint8>) -> Parser {
  Parser(lexer::new(input))
}

function (p: *mut Parser) parse_ty() -> result::Result<Ty, mpc::CompileError> {
  let tk = match p.lexer.next() {
    Ok(tk) => tk,
    Err(err) => return result::err(err)
  };

  match tk {
    TyBool => result::ok(Ty::_Bool),
    TyUint8 => result::ok(Ty::_Uint8),
    TyInt8 => result::ok(Ty::_Int8),
    TyUint16 => result::ok(Ty::_Uint16),
    TyInt16 => result::ok(Ty::_Int16),
    TyUint32 => result::ok(Ty::_Uint32),
    TyInt32 => result::ok(Ty::_Int32),
    TyUint64 => result::ok(Ty::_Uint64),
    TyInt64 => result::ok(Ty::_Int64),
    TyUintn => result::ok(Ty::_Uintn),
    TyIntn => result::ok(Ty::_Intn),
    TyFloat => result::ok(Ty::_Float),
    TyDouble => result::ok(Ty::_Double),
    * => result::err(mpc::CompileError::UnexptedToken(tk))
  }
}

function (p: *mut Parser) parse() -> result::Result<(), mpc::CompileError> {
  match p.parse_ty() {
    Ok(ty) => result::ok(()),
    Err(err) => result::err(err)
  }
}
