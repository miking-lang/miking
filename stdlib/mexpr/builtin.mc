
include "ast.mc"

let builtin = use MExprAst in [
  -- Integers
  ("addi", CAddi ()),
  ("subi", CSubi ()),
  ("muli", CMuli ()),
  ("divi", CDivi ()),
  ("modi", CModi ()),
  ("negi", CNegi ()),
  ("negi", CNegi ()),
  ("lti", CLti ()),
  ("leqi", CEqi ()),
  ("gti", CGti ()),
  ("geqi", CGeqi ()),
  ("eqi", CEqi ()),
  ("neqi", CNeqi ()),
  ("slli", CSlli ()),
  ("srli", CSrli ()),
  ("srai", CSrai ()),
  -- ("arity", CArity ()),   -- Arity is not yet implemented
  ("print", CPrint ())
]




