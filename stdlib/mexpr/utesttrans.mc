include "bool.mc"
include "string.mc"
include "name.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/builtin.mc"
include "mexpr/eq.mc"
include "mexpr/eval.mc"
include "mexpr/type-annot.mc"

let _utestRunnerStr = "
let head = lam seq. get seq 0 in
let tail = lam seq. subsequence seq 1 (length seq) in
let null = lam seq. eqi (length seq) 0 in

recursive
  let foldl = lam f. lam acc. lam seq.
    if null seq then acc
    else foldl f (f acc (head seq)) (tail seq)
in
let join = lam seqs.
  foldl concat [] seqs
in

let printLn = lam s.
  print (concat s \"\\n\")
in

let int2string = lam n.
  recursive
  let int2string_rechelper = lam n.
    if lti n 10
    then [int2char (addi n (char2int '0'))]
    else
      let d = [int2char (addi (modi n 10) (char2int '0'))] in
      concat (int2string_rechelper (divi n 10)) d
  in
  if lti n 0
  then cons '-' (int2string_rechelper (negi n))
  else int2string_rechelper n
in

recursive
  let strJoin = lam delim. lam strs.
    if eqi (length strs) 0
    then \"\"
    else if eqi (length strs) 1
         then head strs
         else concat (concat (head strs) delim) (strJoin delim (tail strs))
in

let mapi = lam f. lam seq.
  recursive let work = lam i. lam f. lam seq.
      if null seq then []
      else cons (f i (head seq)) (work (addi i 1) f (tail seq))
  in
  work 0 f seq
in

let map = lam f. mapi (lam. lam x. f x) in

let eqSeq = lam eq : (Unknown -> Unknown -> Bool).
  recursive let work = lam as. lam bs.
    let pair = (as, bs) in
    match pair with ([], []) then true else
    match pair with ([a] ++ as, [b] ++ bs) then
      if eq a b then work as bs else false
    else false
  in work
in

let utestTestPassed = lam.
  print \".\"
in

let utestTestFailed =
  lam line   : String.
  lam lhsStr : String.
  lam rhsStr : String.
  printLn \"\";
  printLn (join [\" ** Unit test FAILED on line \", line, \" **\"]);
  printLn (join [\"    LHS: \", lhsStr]);
  printLn (join [\"    RHS: \", rhsStr])
in

let utestRunner =
  lam info   : {filename : String, row : String}.
  lam printf : Unknown -> String.
  lam eqfunc : Unknown -> Unknown -> Bool.
  lam lhs    : Unknown.
  lam rhs    : Unknown.
  -- Comparison
  if eqfunc lhs rhs then
    utestTestPassed ()
  else
    utestTestFailed info.row (printf lhs) (printf rhs)
in

()
"

let utestRunner =
  use BootParser in
  use MExprSym in
  parseMExprString _utestRunnerStr

-- Get the name of a string identifier in an expression
let findName : String -> Expr -> Option Name = use MExprAst in
  lam str. lam expr.
    recursive let findNameH = lam acc. lam expr.
      match acc with Some n then Some n
      else match expr with TmLet {ident = ident, body = body, inexpr = inexpr} then
        if eqString (nameGetStr ident) str then Some ident
        else match findNameH (None ()) body with Some n then Some n
        else match findNameH (None ()) inexpr with Some n then Some n
        else None ()
      else sfold_Expr_Expr findNameH (None ()) expr
    in
    findNameH (None ()) expr

let utestRunnerName = optionGetOrElse
  (lam. error "Expected utestRunner to be defined")
  (findName "utestRunner" utestRunner)

let int2stringName = optionGetOrElse
  (lam. error "Expected int2string to be defined")
  (findName "int2string" utestRunner)

let withUtestRunner = lam term.
  bind_ utestRunner term

recursive let _printFunc = use MExprAst in
  lam ty.
  match ty with TyInt {} then
    nvar_ int2stringName
  else match ty with TyBool {} then
    ulam_ "b" (if_ (var_ "b") (str_ "true") (str_ "false"))
  else match ty with TySeq {ty = elemTy} then
    ulam_ "seq" (app_ (var_ "join") (seq_ [
      str_ "[",
      appf2_ (var_ "strJoin")
               (str_ ",")
               (appf2_ (var_ "map") (_printFunc elemTy) (var_ "seq")),
      str_ "]"
    ]))
  else dprintLn ty; error "Unsupported type"
end

let _eqBool = ulam_ "a" (ulam_ "b"
  (or_ (and_ (var_ "a") (var_ "b"))
       (and_ (not_ (var_ "a")) (not_ (var_ "b")))))

recursive let _eqFunc = use MExprAst in
  lam ty.
  match ty with TyInt {} then
    ulam_ "a" (ulam_ "b" (eqi_ (var_ "a") (var_ "b")))
  else match ty with TyBool {} then
    _eqBool
  else match ty with TySeq {ty = elemTy} then
    ulam_ "a" (ulam_ "b" (appf3_ (var_ "eqSeq")
                                 (_eqFunc elemTy) (var_ "a") (var_ "b")))
  else dprintLn ty; error "Unsupported type"
end

let utestAst = lam ty. lam info. lam l. lam r.
  appf5_
    (nvar_ utestRunnerName)
    (record_ [
      ("filename", str_ info.filename),
      ("row", str_ info.row)])
    (_printFunc ty)
    (_eqFunc ty)
    l
    r

let _generateUtest = lam t.
  use MExprAst in
  let utestInfo =
    match t.info with Info {filename = f, row1 = row} then
      {filename = f, row = int2string row}
    else match t.info with NoInfo () then
      {filename = "", row = "0"}
    else never
  in
  match compatibleType assocEmpty (ty t.test) (ty t.expected) with Some ty then
    utestAst ty utestInfo t.test t.expected
  else error "Type error"

-- NOTE(linnea, 2021-03-17): Assumes that typeAnnot has been called prior to the
-- transformation.
lang MExprUtestTrans = MExprAst
  sem utestStripH =
  | TmUtest t -> utestStripH t.next
  | t -> smap_Expr_Expr utestStripH t

  sem utestStrip =
  | t -> utestStripH t

  sem utestGenH =
  | TmUtest t ->
    bind_ (ulet_ "" (_generateUtest t)) (utestGenH t.next)
  | t -> smap_Expr_Expr utestGenH t

  sem utestGen =
  | t ->
    let t = utestGenH t in
    withUtestRunner t
end

lang TestLang = MExprUtestTrans + MExprEq + MExprTypeAnnot + MExprEval

mexpr

use TestLang in

let default_info =
  Info { filename = "utesttrans.mc"
       , row1 = 0, col1 = 0, row2 = 0, col1 = 0}
in

let utest_info_ =
  lam t. lam e. lam n.
  TmUtest { test = t
          , expected = e
          , next = n
          , tusing = None ()
          , ty = TyUnknown {}
          , info = default_info}
in

let utestu_info_ =
  lam t. lam e. lam n. lam u.
  TmUtest { test = t
          , expected = e
          , next = n
          , tusing = Some u
          , ty = TyUnknown {}
          , info = default_info}
in

let t = typeAnnot (utest_info_ (int_ 1) (int_ 0) unit_) in
eval {env = builtinEnv} (symbolize (utestGen t));
utest utestStrip t with unit_ using eqExpr in

let t1 = typeAnnot (utestu_info_ (int_ 1) (int_ 0) unit_ (const_ (CGeqi{}))) in
eval {env = builtinEnv} (symbolize (utestGen t1));
utest utestStrip t1 with unit_ using eqExpr in

let lhs = seq_ [seq_ [int_ 1, int_ 2], seq_ [int_ 3, int_ 4]] in
let rhs = reverse_ (seq_ [
  reverse_ (seq_ [int_ 4, int_ 3]),
  reverse_ (seq_ [int_ 2, int_ 1])]) in
let t2 = typeAnnot (utest_info_ lhs rhs unit_) in
eval {env = builtinEnv} (symbolize (utestGen t2));
utest utestStrip t2 with unit_ using eqExpr in

()
