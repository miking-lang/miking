include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "ocaml/ast.mc"
include "ocaml/pprint.mc"

let escapeFirstChar = lam c.
  if or (isLowerAlpha c) (eqChar c '_') then c
  else '_'

utest map escapeFirstChar "abcABC/:@_'" with "abc________"

let escapeChar = lam c.
  if or (isAlphanum c) (or (eqChar c '_') (eqChar c '\'')) then c
  else '_'

utest map escapeChar "abcABC/:@_'" with "abcABC____'"

let escapeString = lam s.
  if gti (length s) 0 then
    cons (escapeFirstChar (head s)) (map escapeChar (tail s))
  else
    "var"

utest escapeString "abcABC/:@_'" with "abcABC____'"
utest escapeString "" with "var"
utest escapeString "ABC123" with "_BC123"
utest escapeString "'a/b/c" with "_a_b_c"
utest escapeString "123" with "_23"

let escapeName = lam n.
  match n with (str,symb) then (escapeString str, symb)
  else never

utest (escapeName ("abcABC/:@_'", gensym ())).0
with ("abcABC____'", gensym ()).0

utest (escapeName ("ABC123", gensym ())).0 with ("_BC123", gensym ()).0

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
      let bs = map (lam b. {ident = escapeName b.ident, body = generate b.body})
                   t.bindings
      in
      TmRecLets {bindings = bs, inexpr = generate t.inexpr}
  | t -> smap_Expr_Expr generate t
end

lang OCamlTest = OCamlGenerate + OCamlPrettyPrint

mexpr

use OCamlTest in

utest generate (var_ "abcABC/:@_'") with var_ "abcABC____'" in
utest generate (ulam_ "ABC123" (ulam_ "'a/b/c" (app_ (var_ "ABC123")
                                               (var_ "'a/b/c"))))
with ulam_ "_BC123" (ulam_ "_a_b_c" (app_ (var_ "_BC123") (var_ "_a_b_c"))) in

utest generate (let_ "abcABC/:@_'" (var_ "abcABC/:@_'"))
with (let_ "abcABC____'" (var_ "abcABC____'")) in

let testRec =
  bind_
    (reclets_add "abcABC/:@_'" (ulam_ "ABC123" (app_ (var_ "abcABC/:@_'")
                                                     (var_ "ABC123")))
      reclets_empty)
    (app_ (var_ "abcABC/:@_'") (int_ 1))
in

let testRecExpected =
  bind_
    (reclets_add "abcABC____'" (ulam_ "_BC123" (app_ (var_ "abcABC____'")
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
    (reclets_add "_a_b_c" (ulam_ "var" (app_ (var_ "_23") (var_ "var")))
      (reclets_add "_23" (ulam_ "var" (app_ (var_ "_a_b_c") (var_ "var")))
        reclets_empty))
    (app_ (var_ "_a_b_c") (int_ 1))
in
utest generate mutRec with mutRecExpected in

()
