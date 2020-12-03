include "ocaml/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/symbolize.mc"
include "mexpr/pprint.mc"
include "char.mc"
include "name.mc"

let defaultIdentName = "_var"

let escapeFirstChar = lam c.
  if isLowerAlphaOrUnderscore c then c
  else '_'

utest map escapeFirstChar "abcABC/:@_'" with "abc________"

let isValidChar = lam c.
  or (isAlphanum c) (or (eqChar c '_') (eqChar c '\''))

let escapeChar = lam c.
  if isValidChar c then c else '_'

utest map escapeChar "abcABC/:@_'" with "abcABC____'"

let isIdentifierString = lam s.
  let n = length s in
  if null s then false
  else if gti n 1 then
    let hd = head s in
    let tl = tail s in
    and (isLowerAlphaOrUnderscore hd) (all isValidChar tl)
  else
    all isLowerAlpha s

utest isIdentifierString "__" with true
utest isIdentifierString "_1" with true
utest isIdentifierString "_A" with true
utest isIdentifierString "a" with true
utest isIdentifierString "a123" with true
utest isIdentifierString "aA" with true
utest isIdentifierString "_" with false
utest isIdentifierString "A" with false
utest isIdentifierString "AA" with false
utest isIdentifierString "__*" with false
utest isIdentifierString "" with false

let isModuleString = lam s.
  if not (null s) then
    if isUpperAlpha (head s) then
      let s = cons (char2lower (head s)) (tail s) in
      isIdentifierString s
    else false
  else
    false

utest isModuleString "A" with true
utest isModuleString "ABCD" with true
utest isModuleString "AbCd" with true
utest isModuleString "Aa123" with true
utest isModuleString "A_" with true
utest isModuleString "__" with false
utest isModuleString "a" with false
utest isModuleString "_" with false
utest isModuleString "aa" with false
utest isModuleString "A*" with false
utest isModuleString "1a" with false
utest isModuleString "1" with false
utest isModuleString "aA" with false
utest isModuleString "" with false

let isModuleCallString = lam s.
  let parts = strSplit "." s in
  let modules = init parts in
  if null modules then false
  else
    and (all isModuleString modules) (isIdentifierString (last parts))

utest isModuleCallString "Foo.bar" with true
utest isModuleCallString "A.B.C.D.E.F.G.hello" with true
utest isModuleCallString "Foo.Bar.foo" with true
utest isModuleCallString "Foo.Bar.__" with true
utest isModuleCallString "Foo.Bar._a" with true
utest isModuleCallString "Foo.Bar._A" with true
utest isModuleCallString "Foo.Bar._" with false
utest isModuleCallString "Foo.Bar.A" with false
utest isModuleCallString "Foo.Bar.*" with false
utest isModuleCallString "a" with false
utest isModuleCallString "A" with false
utest isModuleCallString "_a" with false
utest isModuleCallString "Foo.@" with false
utest isModuleCallString "foo.bar" with false
utest isModuleCallString "Foo.bar.foo" with false
utest isModuleCallString "Foo.B@r.foo" with false
utest isModuleCallString "foo.Bar.foo" with false

let escapeString = lam s.
  let n = length s in
  if gti n 0 then
    if isModuleCallString s then
      s
    else
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

lang OCamlPrettyPrint = VarPrettyPrint + AppPrettyPrint
                        + LetPrettyPrint + ConstPrettyPrint + OCamlAst
                        + IdentifierPrettyPrint + UnknownTypePrettyPrint

  sem pprintVarName (env : PprintEnv) =
  | name -> pprintEnvGetStr env (escapeName name)
  sem pprintLabelString =
  | s -> s

  sem isAtomic =
  | TmLam _ -> false
  | TmRecLets _ -> false

  sem _pprintBinding (indent : Int) (env: PprintEnv) =
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

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmLam {ident = id, body = b} ->
    match pprintVarName env id with (env,str) then
      match pprintCode (pprintIncr indent) env b with (env,body) then
        (env,join ["fun ", str, " ->", pprintNewline (pprintIncr indent), body])
      else never
    else never
  | TmRecLets {bindings = bindings, inexpr = inexpr} ->
    let lname = lam env. lam bind.
      match pprintVarName env bind.ident with (env,str) then
        (env, str)
      else never in
    let lbody = lam env. lam bind.
      match pprintCode (pprintIncr (pprintIncr indent)) env bind.body
      with (env,str) then (env, str)
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

let pprintProg = lam ast.
  let _ = print "\n\n" in
  print (expr2str (symbolize ast))
in

let testAddInt1 = addi_ (int_ 1) (int_ 2) in

let testAddInt2 = addi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in

let testAddFloat1 = addf_ (float_ 1.) (float_ 2.) in

let testAddFloat2 = addf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in

let testNegFloat = negf_ (float_ 1.) in

let testBoolNot = not_ (not_ true_) in

let testCompareInt1 = eqi_ (int_ 1) (int_ 2) in

let testCompareInt2 = lti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in

let testCompareFloat1 = eqf_ (float_ 1.) (float_ 2.) in

let testCompareFloat2 =
  lti_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.)
in

let testCharLiteral = char_ 'c' in

let testFun = ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))) in

let testLet =
  bindall_ [ulet_ "x" (int_ 1), addi_ (var_ "x") (int_ 2)]
in

let testRec =
  bind_
    (ureclets_add "foo" (ulam_ "x" (app_ (var_ "foo") (var_ "x")))
      reclets_empty)
    (app_ (var_ "foo") (int_ 1))
in

let testMutRec =
  bind_
    (ureclets_add "foo" (ulam_ "x" (app_ (var_ "bar") (var_ "x")))
      (ureclets_add "bar" (ulam_ "x" (app_ (var_ "foo") (var_ "x")))
         reclets_empty))
    (app_ (var_ "foo") (int_ 1))
in

-- Test identifier escapingvar

-- Abstractions
let testLamEscape = (ulam_ "ABC123" (ulam_ "'a/b/c" (app_ (var_ "ABC123")
                                                          (var_ "'a/b/c"))))
in

-- Lets
let testLetEscape = bind_ (ulet_ "abcABC/:@_'" (int_ 1)) (var_ "abcABC/:@_'") in

let testRecEscape =
  bind_
    (ureclets_add "abcABC/:@_'" (ulam_ "ABC123"
                               (app_ (var_ "abcABC/:@_'")
                                     (var_ "ABC123")))
      reclets_empty)
    (app_ (var_ "abcABC/:@_'") (int_ 1))
in

let testMutRecEscape =
  bind_
    (ureclets_add "'a/b/c" (ulam_ "" (app_ (var_ "123") (var_ "")))
      (ureclets_add "123" (ulam_ "" (app_ (var_ "'a/b/c") (var_ "")))
         reclets_empty))
    (app_ (var_ "'a/b/c") (int_ 1))
in

let asts = [
  testAddInt1,
  testAddInt2,
  testAddFloat1,
  testAddFloat2,
  testNegFloat,
  testBoolNot,
  testCompareInt1,
  testCompareInt2,
  testCompareFloat1,
  testCompareFloat2,
  testCharLiteral,
  testFun,
  testLet,
  testRec,
  testMutRec,
  testLamEscape,
  testLetEscape,
  testRecEscape,
  testMutRecEscape
] in

-- let _ = map pprintProg asts in

()
