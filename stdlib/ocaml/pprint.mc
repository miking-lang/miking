include "ocaml/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/symbolize.mc"
include "char.mc"
include "name.mc"

let spacing = lam indent. makeSeq indent ' '
let incr = lam indent. addi indent 2
let newline = lam indent. concat "\n" (spacing indent)

lang OCamlPrettyPrint = OCamlAst
  sem _pprintBinding (indent : Int) =
  | {ident = id, body = b} ->
    join [nameGetStr id, " = ", pprint indent b, " in"]

  sem pprintConst =
  | CInt {val = i} -> int2string i
  | CAddi _ -> "+"
  | CSubi _ -> "-"
  | CMuli _ -> "*"
  | CFloat {val = f} -> float2string f
  | CAddf _ -> "+."
  | CSubf _ -> "-."
  | CMulf _ -> "*."
  | CDivf _ -> "/."
  | CNegf _ -> "Float.neg"
  | CBool {val = b} ->
      match b with true then
        "true"
      else
        match b with false then
          "false"
        else never
  | CNot _ -> "not"
  | CEqi _ -> "="
  | CLti _ -> "<"
  | CEqf _ -> "="
  | CLtf _ -> "<"
  | CChar {val = c} -> show_char c

  sem pprint (indent : Int) =
  | TmApp {lhs = l, rhs = r} ->
    join ["(", pprint indent l, ")", newline (incr indent),
          "(", pprint (incr indent) r, ")"]
  | TmConst {val = c} -> pprintConst c
  | TmLam {ident = id, body = b} ->
    join ["fun ", nameGetStr id, " ->", newline (incr indent),
          pprint (incr indent) b]
  | TmVar {ident = name} -> nameGetStr name
  | TmLet t ->
    join ["let ", _pprintBinding indent t, newline (incr indent),
          (pprint (incr indent) t.inexpr)]
  | TmRecLets {bindings = bindings, inexpr = inexpr} ->
    let binds = map (_pprintBinding indent) bindings in
    join ["let rec ", strJoin (join [newline indent, "and "]) binds]
end

lang TestLang = OCamlPrettyPrint + MExprSym

mexpr
use TestLang in

let pprintProg = lam p.
  let _ = print "\n\n" in
  print (pprint 0 (symbolize assocEmpty p))
in

let addInt1 = addi_ (int_ 1) (int_ 2) in

let addInt2 = addi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in

let addFloat1 = addf_ (float_ 1.) (float_ 2.) in

let addFloat2 = addf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in

let negFloat = negf_ (float_ 1.) in

let boolNot = not_ (not_ true_) in

let compareInt1 = eqi_ (int_ 1) (int_ 2) in

let compareInt2 = lti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in

let compareFloat1 = eqf_ (float_ 1.) (float_ 2.) in

let compareFloat2 = lti_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in

let charLiteral = char_ 'c' in

let fun = ulam_ "x" (ulam_ "y" (app_ (var_ "x") (var_ "y"))) in

let testLet = bindall_ [let_ "x" (int_ 1), addi_ (var_ "x") (int_ 2)] in

let testRec =
  reclet_ "foo" (ulam_ "x" (app_ (var_ "foo") (var_ "x")))
in

let mutRec =
  bind_
    (reclets_add "foo" (ulam_ "x" (app_ (var_ "bar") (var_ "x")))
      (reclets_add "bar" (ulam_ "x" (app_ (var_ "foo") (var_ "x")))
         reclets_empty))
    (app_ (var_ "foo") (int_ 1))
in

let asts = [
  addInt1,
  addInt2,
  addFloat1,
  addFloat2,
  negFloat,
  boolNot,
  compareInt1,
  compareInt2,
  compareFloat1,
  compareFloat2,
  charLiteral,
  fun,
  testLet,
  testRec,
  mutRec
] in

map pprintProg asts
