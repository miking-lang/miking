include "ocaml/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/symbolize.mc"
include "mexpr/pprint.mc"
include "char.mc"
include "name.mc"

lang OCamlPrettyPrint = VarPrettyPrint + AppPrettyPrint + LetPrettyPrint
                        + ConstPrettyPrint + OCamlAst

  sem _pprintBinding (indent : Int) (env: PPrintEnv) =
  | {ident = id, body = b} ->
    join [nameGetStr id, " = ", pprintCode indent b]

  sem getConstStringCode (indent : Int) =
  | CInt {val = i} -> int2string i
  | CAddi _ -> "(+)"
  | CSubi _ -> "(-)"
  | CMuli _ -> "( * )"
  | CFloat {val = f} -> float2string f
  | CAddf _ -> "(+.)"
  | CSubf _ -> "(-.)"
  | CMulf _ -> "( *. )"
  | CDivf _ -> "(/.)"
  | CNegf _ -> "Float.neg"
  | CBool {val = b} ->
      match b with true then
        "true"
      else
        match b with false then
          "false"
        else never
  | CNot _ -> "not"
  | CEqi _ -> "(=)"
  | CLti _ -> "(<)"
  | CEqf _ -> "(=)"
  | CLtf _ -> "(<)"
  | CChar {val = c} -> show_char c

  sem pprintCode (indent : Int) (env: PPrintEnv) =
  | TmLam {ident = id, body = b} ->
    match pprintEnvGetStr id env with (env,str) then
      let ident = pprintVarString str in
      match pprintCode (pprintIncr indent) env b with (env,body) then
        (env,join ["fun ", ident, " ->",
         pprintNewline (pprintIncr indent), body])
      else never
    else never
  | TmRecLets {bindings = bindings, inexpr = inexpr} ->
    let lname = lam env. lam bind.
      match pprintEnvGetStr bind.ident env with (env,str) then
        (env,pprintVarString str)
      else never in
    let lbody = lam env. lam bind.
      match pprintCode (pprintIncr (pprintIncr indent)) env bind.body
      with (env,str) then (env,pprintVarString str)
      else never in
    match mapAccumL lname env bindings with (env,idents) then
      match mapAccumL lbody env bindings with (env,bodies) then
        match pprintCode indent env inexpr with (env,inexpr) then
          let fzip = lam ident. lam body.
            join [ident, " =",
                  pprintNewline (pprintIncr (pprintIncr indent)),
                  body]
          in
          (env,join ["let rec ",
                     strJoin (join [pprintNewline indent, "and "])
                     (zipWith fzip idents bodies),
                     pprintNewline indent, "in ", inexpr])
        else never
      else never
    else never
end

lang TestLang = OCamlPrettyPrint + MExprSym

mexpr
use TestLang in

let pprintProg = lam mexprAst.
  let _ = print "\n\n" in
  print (expr2str (symbolize mexprAst))
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

let fun = ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))) in

let testLet = bindall_ [let_ "x" (int_ 1), addi_ (var_ "x") (int_ 2)] in

let testRec =
  bind_
    (reclets_add "foo" (ulam_ "x" (app_ (var_ "foo") (var_ "x")))
      reclets_empty)
    (app_ (var_ "foo") (int_ 1))
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

-- let _ = map pprintProg asts in

()
