include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "ocaml/ast.mc"
include "ocaml/pprint.mc"
include "mexpr/parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/eval.mc"
include "mexpr/eq.mc"
include "ocaml/compile.mc"
include "hashmap.mc"

let _opHashMap = lam prefix. lam ops.
let mkOp = lam op.
nameSym (join [prefix, op])
in
foldl (lam a. lam op. hashmapInsert hashmapStrTraits op (mkOp op) a)
hashmapEmpty ops

let _op = lam opHashMap. lam op.
nvar_
(hashmapLookupOrElse hashmapStrTraits
  (lam _.
    error (strJoin " " ["Operation", op, "not found"]))
    op
    opHashMap)

let _seqOps = [
  "make",
  "empty",
  "length",
  "concat",
  "get",
  "set",
  "cons",
  "snoc",
  "reverse",
  "split_at"
]

let _seqOp = _op (_opHashMap "Boot.Intrinsics.Mseq." _seqOps)

let _symbOps = [
  "gensym".
  "eqsym",
  "hash"
]

let _symbOp = _op (_opHashMap "Boot.Intrinsics.Symb." _symbOps)

lang OCamlGenerate = MExprAst + OCamlAst
  sem generateConst =
  -- Sequence intrinsics
  | CMakeSeq {} -> _seqOp "make"
  | CLength {} -> _seqOp "length"
  | CCons {} -> _seqOp "cons"
  | CSnoc {} -> _seqOp "snoc"
  | CGet {} -> _seqOp "get"
  | CSet {} -> _seqOp "set"
  | CSplitAt {} -> _seqOp "split_at"
  | CReverse {} -> _seqOp "reverse"
  -- Symbol intrinsics
  | CGensym {} -> _symbOp "gensym"
  | CEqsym {} -> _symbOp "eqsym"
  | CSym2hash {} -> _symbOp "hash"
  | v -> TmConst { val = v }

  sem generate =
  | TmSeq {tms = tms} ->
    let tms = map generate tms in
    foldr (lam tm. lam a. appSeq_ (_seqOp "cons") [tm, a])
          (_seqOp "empty")
          tms
  | TmConst {val = val} -> generateConst val
  | t -> smap_Expr_Expr generate t
end

lang OCamlTest = OCamlGenerate + OCamlPrettyPrint + MExprSym + ConstEq
                 + IntEq + BoolEq + CharEq

mexpr

use OCamlTest in

-- Test semantics

-- Parse helper
let parseAsMExpr = lam s.
  use MExprParser in parseExpr (initPos "") s
in

-- Evaluates OCaml expressions [strConvert] given as string, applied
-- to [p], and parses it as a mexpr expression.
let ocamlEval = lam p. lam strConvert.
  let subprocess = pyimport "subprocess" in
  let blt = pyimport "builtins" in
    let res = ocamlCompile (join ["print_string (", strConvert, "(", p, "))"]) in
    let out = (res.run "" []).stdout in
    let _ = res.cleanup () in
    parseAsMExpr out
in

-- Compares evaluation of [mexprAst] as a mexpr and evaluation of
-- [ocamlAst] as a OCaml expression.
let sameSemantics = lam mexprAst. lam ocamlAst.
  let mexprVal =
    use MExprEval in
    eval {env = []} mexprAst
  in
  match mexprVal with TmConst t then
    match t.val with CInt _ then
      let ocamlVal = ocamlEval (expr2str ocamlAst) "string_of_int" in
      match ocamlVal with TmConst {val = CInt _} then
        eqExpr mexprVal ocamlVal
      else error "Values mismatch"
    else match t.val with CBool _ then
      let ocamlVal = ocamlEval (expr2str ocamlAst) "string_of_bool" in
      match ocamlVal with TmConst {val = CBool _} then
        eqExpr mexprVal ocamlVal
      else error "Values mismatch"
    else match t.val with CChar _ then
      let ocamlVal =
        ocamlEval (expr2str ocamlAst) "Printf.sprintf \"'%c'\""
      in
      match ocamlVal with TmConst {val = CChar _} then
        eqExpr mexprVal ocamlVal
      else error "Values mismatch"
    else error "Unsupported constant"
  else error "Unsupported value"
in

-- Ints
let addInt1 = addi_ (int_ 1) (int_ 2) in
utest addInt1 with generate (symbolize addInt1) using sameSemantics in

let addInt2 = addi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest addInt2 with generate (symbolize addInt2) using sameSemantics in

let compareInt1 = eqi_ (int_ 1) (int_ 2) in
utest compareInt1 with generate (symbolize compareInt1)
using sameSemantics in

let compareInt2 = lti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt2 with generate (symbolize compareInt2)
using sameSemantics in

-- Booleans
let boolNot = not_ (not_ true_) in
utest boolNot with generate (symbolize boolNot) using sameSemantics in

-- Chars
let charLiteral = char_ 'c' in
utest charLiteral with generate (symbolize charLiteral)
using sameSemantics in

-- Abstractions
let fun =
  symbolize
  (appSeq_
    (ulam_ "@" (ulam_ "%" (addi_ (var_ "@") (var_ "%"))))
    [int_ 1, int_ 2])
in
utest fun with generate fun using sameSemantics in

let funShadowed =
  symbolize
  (appSeq_
    (ulam_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))))
    [ulam_ "@" (var_ "@"), int_ 2])
in
utest funShadowed with generate funShadowed using sameSemantics in

-- Lets
let testLet =
  symbolize
  (bindall_ [ulet_ "^" (int_ 1), addi_ (var_ "^") (int_ 2)])
in
utest testLet with generate testLet using sameSemantics in

let testLetShadowed =
  symbolize
  (bindall_ [ulet_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))),
             app_ (var_ "@") (int_ 1)])
in
utest testLetShadowed with generate testLetShadowed
using sameSemantics in

let testLetRec =
  symbolize
  (bind_
     (ureclets_add "$" (ulam_ "%" (app_ (var_ "@") (int_ 1)))
     (ureclets_add "@" (ulam_ "" (var_ ""))
     reclets_empty))
   (app_ (var_ "$") (var_ "@")))
in
utest testLetRec with generate testLetRec using sameSemantics in

-- Sequences
let testEmpty = symbolize (length_ (seq_ [])) in
utest testEmpty with generate testEmpty using sameSemantics in

let nonEmpty = seq_ [int_ 1, int_ 2, int_ 3] in
let len = length_ nonEmpty in
let fst = get_ nonEmpty (int_ 0) in
let snd = get_ nonEmpty (int_ 1) in
let thrd = get_ nonEmpty (int_ 2) in
utest int_ 3 with generate len using sameSemantics in
utest int_ 1 with generate fst using sameSemantics in
utest int_ 2 with generate snd using sameSemantics in
utest int_ 3 with generate thrd using sameSemantics in

let testMake = makeseq_ (int_ 2) (int_ 0) in
let len = length_ testMake in
let fst = get_ testMake (int_ 0) in
let lst = get_ testMake (int_ 1) in
utest int_ 2 with generate len using sameSemantics in
utest int_ 0 with generate fst using sameSemantics in
utest int_ 0 with generate lst using sameSemantics in

let testSet = set_ (seq_ [int_ 1, int_ 2]) (int_ 0) (int_ 3) in
let len = length_ testSet in
let fst = get_ testSet (int_ 0) in
let snd = get_ testSet (int_ 1) in
utest int_ 2 with generate len using sameSemantics in
utest int_ 3 with generate fst using sameSemantics in
utest int_ 2 with generate snd using sameSemantics in

let testCons = cons_  (int_ 1) (seq_ [int_ 2, int_ 3]) in
let len = length_ testCons in
let fst = get_ testCons (int_ 0) in
let snd = get_ testCons (int_ 1) in
let thrd = get_ testCons (int_ 2) in
utest int_ 3 with generate len using sameSemantics in
utest int_ 1 with generate fst using sameSemantics in
utest int_ 2 with generate snd using sameSemantics in
utest int_ 3 with generate thrd using sameSemantics in

let testSnoc = snoc_ (seq_ [int_ 1, int_ 2]) (int_ 3) in
let len = length_ testSnoc in
let fst = get_ testSnoc (int_ 0) in
let snd = get_ testSnoc (int_ 1) in
let thrd = get_ testSnoc (int_ 2) in
utest int_ 3 with generate len using sameSemantics in
utest int_ 1 with generate fst using sameSemantics in
utest int_ 2 with generate snd using sameSemantics in
utest int_ 3 with generate thrd using sameSemantics in

let testReverse = reverse_ (seq_ [int_ 1, int_ 2, int_ 3]) in
let len = length_ testReverse in
let fst = get_ testReverse (int_ 0) in
let snd = get_ testReverse (int_ 1) in
let thrd = get_ testReverse (int_ 2) in
utest int_ 3 with generate len using sameSemantics in
utest int_ 3 with generate fst using sameSemantics in
utest int_ 2 with generate snd using sameSemantics in
utest int_ 1 with generate thrd using sameSemantics in

-- TODO(Oscar Eriksson, 2020-11-16) Test splitAt when we have implemented tuple
-- projection.

-- TODO(Oscar Eriksson, 2020-12-30) Test symbol operations when we have
-- implemented tuples/records.

()
