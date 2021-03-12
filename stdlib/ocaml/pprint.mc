include "ocaml/ast.mc"
include "mexpr/ast-builder.mc"
include "ocaml/symbolize.mc"
include "mexpr/pprint.mc"
include "char.mc"
include "name.mc"

let defaultIdentName = "_var"
let defaultConName = "Con"

let escapeFirstChar = lam c.
  if isLowerAlphaOrUnderscore c then c
  else '_'

let escapeFirstConChar = lam c.
  if isUpperAlpha c then c
  else 'C'

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

let isConString = lam s.
  if null s then false else
  and (isUpperAlpha (head s)) (all isValidChar (tail s))

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

let escapeVarString = lam s.
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

let escapeConString = lam s.
  let n = length s in
  if gti n 0 then
    let hd = head s in
    let tl = tail s in
    if or (neqi n 1) (isUpperAlpha hd) then
      cons (escapeFirstConChar hd) (map escapeChar tl)
    else
      defaultConName
  else
    defaultConName

let escapeLabelStr = lam s. cons '_' (map escapeChar s)

utest escapeVarString "abcABC/:@_'" with "abcABC____'"
utest escapeVarString "" with defaultIdentName
utest escapeVarString "@" with defaultIdentName
utest escapeVarString "ABC123" with "_BC123"
utest escapeVarString "'a/b/c" with "_a_b_c"
utest escapeVarString "123" with "_23"

utest escapeConString "abcABC/:@_'" with "CbcABC____'"
utest escapeConString "" with defaultConName
utest escapeConString "@" with defaultConName
utest escapeConString "ABC123" with "ABC123"
utest escapeConString "'a/b/c" with "Ca_b_c"
utest escapeConString "123" with "C23"

let escapeName = lam n.
  match n with (str,symb) then (escapeVarString str, symb)
  else never

let escapeConName = lam n.
  match n with (str,symb) then (escapeConString str, symb)
  else never

utest (escapeName ("abcABC/:@_'", gensym ())).0
with ("abcABC____'", gensym ()).0

utest (escapeName ("ABC123", gensym ())).0
with ("_BC123", gensym ()).0

-- Pretty-printing of MExpr types in OCaml. Due to the obj-wrapping, we do not
-- want to specify the type names in general. Record types are printed in a
-- different way because their types must be declared at the top of the program
-- in order to use them (e.g. for pattern matching). As type-lifting replaces
-- all nested record types with type variables, all fields of a record type
-- will be printed as Obj.t.
lang OCamlTypePrettyPrint =
  UnknownTypeAst + BoolTypeAst + IntTypeAst + FloatTypeAst + CharTypeAst +
  SeqTypeAst + RecordTypeAst + VariantTypeAst + VarTypeAst +
  FunTypePrettyPrint + AppTypePrettyPrint

  sem pprintLabelString =

  sem getTypeStringCode (indent : Int) (env : PprintEnv) =
  | TyRecord t ->
    if mapIsEmpty t.bindings then
      error "Unit record type not supported in OCaml"
    else
      let f = lam env. lam sid. lam ty.
        let str = sidToString sid in
        match getTypeStringCode indent env ty with (env,ty) then
          let str = pprintLabelString str in
          (env, join [str, ": ", ty])
        else never
      in
      match mapMapAccum f env t.fields with (env, fields) then
        let fieldStrs = mapValues fields in
        (env, join ["{", strJoin "; " fieldStrs, "}"])
      else never
  | _ -> (env, "Obj.t")
end

lang OCamlPrettyPrint =
  VarPrettyPrint + ConstPrettyPrint + OCamlAst +
  IdentifierPrettyPrint + NamedPatPrettyPrint + IntPatPrettyPrint +
  CharPatPrettyPrint + BoolPatPrettyPrint + OCamlTypePrettyPrint

  sem pprintConName (env : PprintEnv) =
  | name -> pprintEnvGetStr env (escapeConName name)
  sem pprintVarName (env : PprintEnv) =
  | name -> pprintEnvGetStr env (escapeName name)
  sem pprintLabelString =
  | s -> escapeLabelStr s

  sem isAtomic =
  | TmLam _ -> false
  | TmLet _ -> false
  | TmRecLets _ -> false
  | TmApp _ -> false
  | TmRecord _ -> true
  | OTmArray _ -> true
  | OTmMatch _ -> false
  | OTmTuple _ -> true
  | OTmConApp {args = []} -> true
  | OTmConApp _ -> false
  | OTmVariantTypeDecl _ -> false
  | OTmVarExt _ -> true
  | OTmConAppExt _ -> false
  | OTmString _ -> true

  sem patIsAtomic =
  | OPatRecord _ -> false
  | OPatTuple _ -> true
  | OPatCon {args = []} -> true
  | OPatCon _ -> false
  | OPatConExt _ -> false

  sem getConstStringCode (indent : Int) =
  | CInt {val = i} -> int2string i
  | CAddi _ -> "(+)"
  | CSubi _ -> "(-)"
  | CMuli _ -> "( * )"
  | CDivi _ -> "(/)"
  | CModi _ -> "(mod)"
  | CNegi _ -> "(~-)"
  | CFloat {val = f} -> float2string f
  | CAddf _ -> "(+.)"
  | CSubf _ -> "(-.)"
  | CMulf _ -> "( *. )"
  | CDivf _ -> "(/.)"
  | CNegf _ -> "(~-.)"
  | CBool {val = b} ->
      match b with true then
        "true"
      else
        match b with false then
          "false"
        else never
  | CEqi _ -> "(=)"
  | CLti _ -> "(<)"
  | CLeqi _ -> "(<=)"
  | CGti _ -> "(>)"
  | CGeqi _ -> "(>=)"
  | CNeqi _ -> "(!=)"
  | CSlli _ -> "Int.shift_left"
  | CSrli _ -> "Int.shift_right_logical"
  | CSrai _ -> "Int.shift_right"
  | CEqf _ -> "(=)"
  | CLtf _ -> "(<)"
  | CLeqf _ -> "(<=)"
  | CGtf _ -> "(>)"
  | CGeqf _ -> "(>=)"
  | CNeqf _ -> "(!=)"
  | CInt2float _ -> "float_of_int"
  | CChar {val = c} -> show_char c
  | CEqc _ -> "(=)"
  | CChar2Int _ -> "int_of_char"
  | CInt2Char _ -> "char_of_int"

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | OTmVariantTypeDecl t ->
    let f = lam env. lam ident. lam ty.
      match pprintConName env ident with (env, ident) then
        match getTypeStringCode indent env ty with (env, ty) then
          (env, join ["| ", ident, " of ", ty])
        else never
      else never
    in
    match pprintVarName env t.ident with (env, ident) then
      match mapMapAccum f env t.constrs with (env, constrs) then
        match pprintCode indent env t.inexpr with (env, inexpr) then
          let constrs = strJoin (pprintNewline (pprintIncr indent))
                                (mapValues constrs) in
          (env, join ["type ", ident, " =", pprintNewline (pprintIncr indent),
                      constrs, ";;", pprintNewline indent,
                      inexpr])
        else never
      else never
    else never
  | OTmVarExt {ident = ident} -> (env, ident)
  | OTmConApp {ident = ident, args = []} -> pprintConName env ident
  | OTmConApp {ident = ident, args = [arg]} ->
    match pprintConName env ident with (env, ident) then
      match printParen indent env arg with (env, arg) then
        (env, join [ident, " ", arg])
      else never
    else never
  | OTmConApp {ident = ident, args = args} ->
    match pprintConName env ident with (env, ident) then
      match mapAccumL (pprintCode indent) env args with (env, args) then
        (env, join [ident, " (", strJoin ", " args, ")"])
      else never
    else never
  | OTmConAppExt {ident = ident, args = []} -> (env, ident)
  | OTmConAppExt {ident = ident, args = [arg]} ->
    match printParen ident env arg with (env, arg) then
      (env, join [ident, " ", arg])
    else never
  | OTmConAppExt {ident = ident, args = args} ->
    match mapAccumL (pprintCode indent) env args with (env, args) then
      (env, join [ident, " (", strJoin ", " args, ")"])
    else never
  | TmLam {ident = id, body = b} ->
    match pprintVarName env id with (env,str) then
      match pprintCode (pprintIncr indent) env b with (env,body) then
        (env,join ["fun ", str, " ->", pprintNewline (pprintIncr indent), body])
      else never
    else never
  | TmLet t ->
    match pprintVarName env t.ident with (env,str) then
      match pprintCode (pprintIncr indent) env t.body with (env,body) then
        match pprintCode indent env t.inexpr with (env,inexpr) then
          (env,
           if eqString (nameGetStr t.ident) "" then
             join [body, pprintNewline indent, ";", inexpr]
           else
             join ["let ", str, " =", pprintNewline (pprintIncr indent),
                   body, pprintNewline indent,
                   "in", pprintNewline indent,
                   inexpr])
        else never
      else never
    else never
  | TmRecord t ->
    if mapIsEmpty t.bindings then (env, "()")
    else
      let innerIndent = pprintIncr (pprintIncr indent) in
      match
        mapMapAccum (lam env. lam k. lam v.
          let k = sidToString k in
          match pprintCode innerIndent env v with (env, str) then
            (env, join [pprintLabelString k, " =", pprintNewline innerIndent,
                        str])
          else never) env t.bindings
      with (env, binds) then
        let binds = mapValues binds in
        let merged =
          strJoin (concat ";" (pprintNewline (pprintIncr indent))) binds
        in
        (env, join ["{ ", merged, " }"])
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
  | TmApp t ->
    match pprintCode indent env t.lhs with (env,l) then
      match pprintCode indent env t.rhs with (env,r) then
        (env, join ["(", l, ") (", r, ")"])
      else never
    else never
  | OTmArray t ->
    match mapAccumL (lam env. lam tm. pprintCode (pprintIncr indent) env tm)
                    env t.tms
    with (env,tms) then
      let merged =
        strJoin (concat ";" (pprintNewline (pprintIncr indent))) tms
      in
      (env,join ["[| ", merged, " |]"])
    else never
  | OTmTuple {values = values} ->
    match mapAccumL (pprintCode indent) env values
    with (env, values) then
      (env, join ["(", strJoin ", " values, ")"])
    else never
  | OTmMatch {
    target = target,
    arms
      = [ (PatBool {val = true}, thn), (PatBool {val = false}, els) ]
      | [ (PatBool {val = false}, els), (PatBool {val = true}, thn) ]
    } ->
    let i = indent in
    let ii = pprintIncr i in
    match pprintCode ii env target with (env, target) then
      match pprintCode ii env thn with (env, thn) then
        match pprintCode ii env els with (env, els) then  -- NOTE(vipa, 2020-11-30): if we add sequential composition (`;`) this will be wrong, it should be `printParen` instead of `printCode`.
          (env, join ["if", pprintNewline ii,
                      target, pprintNewline i,
                      "then", pprintNewline ii,
                      thn, pprintNewline i,
                      "else", pprintNewline ii,
                      els])
        else never
      else never
    else never
  | OTmMatch { target = target, arms = [(pat, expr)] } ->
    let i = indent in
    let ii = pprintIncr i in
    match pprintCode ii env target with (env, target) then
      match getPatStringCode ii env pat with (env, pat) then
        match pprintCode i env expr with (env, expr) then  -- NOTE(vipa, 2020-11-30): the NOTE above with the same date does not apply here; `let` has lower precedence than `;`
          (env, join ["let", pprintNewline ii,
                      pat, pprintNewline i,
                      "=", pprintNewline ii,
                      target, pprintNewline i,
                      "in", pprintNewline i,
                      expr])
        else never
      else never
    else never
  | OTmMatch {target = target, arms = arms} ->
    let i = indent in
    let ii = pprintIncr i in
    let iii = pprintIncr ii in
    match pprintCode ii env target with (env, target) then
      let pprintArm = lam env. lam arm. match arm with (pat, expr) then
        match getPatStringCode ii env pat with (env, pat) then
          match printParen iii env expr with (env, expr) then
            (env, join [pprintNewline i, "| ", pat, " ->", pprintNewline iii, expr])
          else never
        else never
      else never in
      match mapAccumL pprintArm env arms with (env, arms) then
        (env, join ["match", pprintNewline ii, target, pprintNewline i,
                    "with", join arms])
      else never
    else never
  | OTmPreambleText t ->
    match pprintCode indent env t.inexpr with (env, inexpr) then
      (env, join [t.text, inexpr])
    else never
  | OTmString t -> (env, join ["\"", t.text, "\""])

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | OPatRecord {bindings = bindings} ->
    let bindingLabels = map sidToString (mapKeys bindings) in
    let labels = map pprintLabelString bindingLabels in
    let pats = mapValues bindings in
    match mapAccumL (getPatStringCode indent) env pats with (env, pats) then
      let strs = mapi (lam i. lam p. join [get labels i, " = ", p]) pats in
      (env, join ["{", strJoin ";" strs, "}"])
    else never
  | OPatTuple {pats = pats} ->
    match mapAccumL (getPatStringCode indent) env pats with (env, pats) then
      (env, join ["(", strJoin ", " pats, ")"])
    else never
  | OPatCon {ident = ident, args = []} -> pprintConName env ident
  | OPatCon {ident = ident, args = [arg]} ->
    match pprintConName env ident with (env, ident) then
      match printPatParen indent env arg with (env, arg) then
        (env, join [ident, " ", arg])
      else never
    else never
  | OPatCon {ident = ident, args = args} ->
    match pprintConName env ident with (env, ident) then
      match mapAccumL (getPatStringCode indent) env args with (env, args) then
        (env, join [ident, " (", strJoin ", " args, ")"])
      else never
    else never
  | OPatConExt {ident = ident, args = []} -> (env, ident)
  | OPatConExt {ident = ident, args = [arg]} ->
    match printPatParen indent env arg with (env, arg) then
      (env, join [ident, " ", arg])
    else never
  | OPatConExt {ident = ident, args = args} ->
    match mapAccumL (getPatStringCode indent) env args with (env, args) then
      (env, join [ident, " (", strJoin ", " args, ")"])
    else never
end

lang TestLang = OCamlPrettyPrint + OCamlSym

mexpr
use TestLang in

let debugPrint = false in

let pprintProg = lam ast.
  if debugPrint then
    print "\n\n";
    print (expr2str (symbolize ast))
  else ()
in

let testAddInt1 = addi_ (int_ 1) (int_ 2) in

let testAddInt2 = addi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in

let testMulInt = muli_ (int_ 2) (int_ 3) in

let testModInt = modi_ (int_ 2) (int_ 3) in

let testDivInt = divi_ (int_ 2) (int_ 3) in

let testNegInt = negi_ (int_ 2) in

let testAddFloat1 = addf_ (float_ 1.) (float_ 2.) in

let testAddFloat2 = addf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in

let testNegFloat = negf_ (float_ 1.) in

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

let testMatchSimple =
  let armA = (pvar_ "a", var_ "a") in
  let armB = (pvarw_, int_ 3) in
  OTmMatch {target = true_, arms = [armA, armB]}
in

let testMatchNested =
  let armA = (pvar_ "a", var_ "a") in
  let armB = (pvarw_, var_ "b") in
  let inner = OTmMatch {target = true_, arms = [armA]} in
  let armB = (pvar_ "b", inner) in
  let armC = (pvar_ "c", false_) in
  OTmMatch {target = true_, arms = [armB, armC]}
in

let testIf =
  OTmMatch {target = true_, arms = [(ptrue_, true_), (pfalse_, false_)]}
in

let testIfNested =
  let t = lam v. OTmMatch {target = true_, arms = [(ptrue_, v true_), (pfalse_, v false_)]} in
  OTmMatch {target = true_, arms = [(pfalse_, t (lam x. addi_ false_ x)), (ptrue_, t (lam x. addi_ true_ x))]}
in

let testPatLet =
  OTmMatch {target = true_, arms = [(pvar_ "a", var_ "a")]}
in

let testTuple =
  OTmMatch
  { target = OTmTuple {values = [true_, false_]}
  , arms = [(OPatTuple {pats = [pvar_ "a", pvar_ "b"]}, OTmTuple {values = [var_ "b", var_ "a"]})]}
in

let asts = [
  testAddInt1,
  testAddInt2,
  testMulInt,
  testModInt,
  testDivInt,
  testNegInt,
  testAddFloat1,
  testAddFloat2,
  testNegFloat,
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
  testMutRecEscape,
  testMatchSimple,
  testMatchNested,
  testIf,
  testIfNested,
  testPatLet,
  testTuple
] in

map pprintProg asts;

()
