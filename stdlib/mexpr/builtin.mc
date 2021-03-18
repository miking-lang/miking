
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
  -- Characters
  ("int2char", CInt2Char ()),
  ("char2int", CChar2Int ()),
  ("eqc", CEqc ()),
  -- Sequences
  ("length", CLength ()),
  ("get", CGet ()),
  ("concat", CConcat ()),
  ("create", CCreate ()),
  ("set", CSet ()),
  ("cons", CCons ()),
  ("snoc", CSnoc ()),
  ("splitAt", CSplitAt ()),
  ("reverse", CReverse ()),
  ("subsequence", CSubsequence ()),
  -- References
  ("ref", CRef ()),
  ("deref", CDeRef ()),
  ("modref", CModRef ()),
  -- IO operations
  ("print", CPrint ())
]
