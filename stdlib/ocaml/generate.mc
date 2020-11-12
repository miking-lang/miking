include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "ocaml/ast.mc"
include "ocaml/pprint.mc"
include "mexpr/parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/eval.mc"
include "mexpr/eq.mc"
include "ocaml/compile.mc"

let defaultIdentName = "_var"

let escapeFirstChar = lam c.
  if isLowerAlphaOrUnderscore c then c
  else '_'

utest map escapeFirstChar "abcABC/:@_'" with "abc________"

let escapeChar = lam c.
  if or (isAlphanum c) (or (eqChar c '_') (eqChar c '\'')) then c
  else '_'

utest map escapeChar "abcABC/:@_'" with "abcABC____'"

let escapeString = lam s.
  let n = length s in
  if gti n 0 then
    let hd = head s in
    let tl = tail s in
    if or (neqi n 1) (isLowerAlpha hd) then
      cons (escapeFirstChar hd) (map escapeChar tl)
    else
      defaultIdentName
  else
    defaultIdentName

utest escapeString "abcABC/:@_'" with "abcABC____'"
utest escapeString "" with defaultIdentName
utest escapeString "@" with defaultIdentName
utest escapeString "ABC123" with "_BC123"
utest escapeString "'a/b/c" with "_a_b_c"
utest escapeString "123" with "_23"

let escapeName = lam n.
  match n with (str,symb) then (escapeString str, symb)
  else never

utest (escapeName ("abcABC/:@_'", gensym ())).0
with ("abcABC____'", gensym ()).0

utest (escapeName ("ABC123", gensym ())).0
with ("_BC123", gensym ()).0

lang OCamlGenerate = MExprAst + OCamlAst
  sem generate =
  | TmVar t -> TmVar {t with ident = escapeName t.ident}
  | TmLam t ->
      TmLam {ident = escapeName t.ident,
             tpe = t.tpe,
             body = generate t.body}
  | TmLet t ->
      TmLet {ident = escapeName t.ident,
             body = generate t.body,
             inexpr = generate t.inexpr}
  | TmRecLets t ->
      let bs = map (lam b. {ident = escapeName b.ident,
                            body = generate b.body})
                   t.bindings
      in
      TmRecLets {bindings = bs, inexpr = generate t.inexpr}
  | t -> smap_Expr_Expr generate t
end

lang OCamlTest = OCamlGenerate + OCamlPrettyPrint + MExprSym + ConstEq
                 + IntEq + BoolEq + CharEq

mexpr

use OCamlTest in

-- Test identifier escaping

-- Vars
utest generate (var_ "abcABC/:@_'") with var_ "abcABC____'" in

-- Abstractions
utest generate (ulam_ "ABC123" (ulam_ "'a/b/c" (app_ (var_ "ABC123")
                                               (var_ "'a/b/c"))))
with ulam_ "_BC123" (ulam_ "_a_b_c" (app_ (var_ "_BC123")
                                          (var_ "_a_b_c")))
in

-- Lets
utest generate (let_ "abcABC/:@_'" (var_ "abcABC/:@_'"))
with (let_ "abcABC____'" (var_ "abcABC____'")) in

let testRec =
  bind_
    (reclets_add "abcABC/:@_'" (ulam_ "ABC123"
                               (app_ (var_ "abcABC/:@_'")
                                     (var_ "ABC123")))
      reclets_empty)
    (app_ (var_ "abcABC/:@_'") (int_ 1))
in

let testRecExpected =
  bind_
    (reclets_add "abcABC____'" (ulam_ "_BC123"
                               (app_ (var_ "abcABC____'")
                               (var_ "_BC123")))
      reclets_empty)
    (app_ (var_ "abcABC____'") (int_ 1))
in

utest generate testRec with testRecExpected in

let mutRec =
  bind_
    (reclets_add "'a/b/c" (ulam_ "" (app_ (var_ "123") (var_ "")))
      (reclets_add "123" (ulam_ "" (app_ (var_ "'a/b/c") (var_ "")))
         reclets_empty))
    (app_ (var_ "'a/b/c") (int_ 1))
in
let mutRecExpected =
  bind_
    (reclets_add "_a_b_c" (ulam_ defaultIdentName (app_ (var_ "_23")
                                             (var_ defaultIdentName)))
      (reclets_add "_23" (ulam_ defaultIdentName (app_ (var_ "_a_b_c")
                                            (var_ defaultIdentName)))
        reclets_empty))
    (app_ (var_ "_a_b_c") (int_ 1))
in

utest generate mutRec with mutRecExpected in

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
    let res = compile (join ["print_string (", strConvert, "(", p, "))"]) in
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
  (bindall_ [let_ "^" (int_ 1), addi_ (var_ "^") (int_ 2)])
in
utest testLet with generate testLet using sameSemantics in

let testLetShadowed =
  symbolize
  (bindall_ [let_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))),
             app_ (var_ "@") (int_ 1)])
in
utest testLetShadowed with generate testLetShadowed
using sameSemantics in

let testLetRec =
  symbolize
  (bind_
     (reclets_add "$" (ulam_ "%" (app_ (var_ "@") (int_ 1)))
     (reclets_add "@" (ulam_ "" (var_ ""))
     reclets_empty))
   (app_ (var_ "$") (var_ "@")))
in
utest testLetRec with generate testLetRec using sameSemantics in

()
