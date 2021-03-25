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

let inf =
  divf 1.0 0.0
in

-- A naive float2string implementation that only formats in standard form
let float2string = lam arg.
  -- Quick fix to check for infinities
  if eqf arg inf then \"INFINITY\" else
  if eqf arg (negf inf) then \"-INFINITY\" else
  -- End of quick fix
  let precision = 7 in -- Precision in number of digits
  let prefixpair = if ltf arg 0.0 then (\"-\", negf arg) else (\"\", arg) in
  let prefix = prefixpair.0 in
  let val = prefixpair.1 in
  recursive
  let float2string_rechelper = lam prec. lam digits. lam v.
    -- Assume 0 <= v < 10
    if eqi prec digits then
      \"\"
    else if eqf v 0.0 then
      \"0\"
    else
      let fstdig = floorfi v in
      let remaining = mulf (subf v (int2float fstdig)) 10.0 in
      let c = int2char (addi fstdig (char2int '0')) in
      cons c (float2string_rechelper prec (addi digits 1) remaining)
  in
  recursive
  let positiveExponentPair = lam acc. lam v.
    if ltf v 10.0
    then (v, acc)
    else positiveExponentPair (addi acc 1) (divf v 10.0)
  in
  recursive
  let negativeExponentPair = lam acc. lam v.
    if geqf v 1.0
    then (v, acc)
    else negativeExponentPair (addi acc 1) (mulf v 10.0)
  in
  let res = if eqf val 0.0 then
              \"0.0\"
            else if gtf val 1.0 then
              let pospair = positiveExponentPair 0 val in
              let retstr = float2string_rechelper precision 0 (pospair.0) in
              let decimals = cons (head retstr) (cons '.' (tail retstr)) in
              concat decimals (concat \"e+\" (int2string pospair.1))
            else
              let pospair = negativeExponentPair 0 val in
              let retstr = float2string_rechelper precision 0 (pospair.0) in
              let decimals = cons (head retstr) (cons '.' (tail retstr)) in
              concat decimals (concat \"e-\" (int2string pospair.1))
  in
  concat prefix res
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

let float2stringName = optionGetOrElse
  (lam. error "Expected float2string to be defined")
  (findName "float2string" utestRunner)

let withUtestRunner = lam term.
  bind_ utestRunner term

recursive let _printFunc = use MExprAst in
  lam ty.
  match ty with TyInt _ then
    nvar_ int2stringName
  else match ty with TyFloat _ then
    nvar_ float2stringName
  else match ty with TyBool _ then
    ulam_ "b" (if_ (var_ "b") (str_ "true") (str_ "false"))
  else match ty with TyChar _ then
    ulam_ "c" (seq_ [char_ '\'', var_ "c", char_ '\''])
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
  match ty with TyInt _ then
    ulam_ "a" (ulam_ "b" (eqi_ (var_ "a") (var_ "b")))
  else match ty with TyBool _ then
    _eqBool
  else match ty with TyChar _ then
    ulam_ "a" (ulam_ "b" (eqc_ (var_ "a") (var_ "b")))
  else match ty with TySeq {ty = elemTy} then
    ulam_ "a" (ulam_ "b" (appf3_ (var_ "eqSeq")
                                 (_eqFunc elemTy) (var_ "a") (var_ "b")))
  else dprintLn ty; error "Unsupported type"
end

let utestRunnerCall = lam info. lam printFunc. lam eqFunc. lam l. lam r.
  appf5_
    (nvar_ utestRunnerName)
    (record_ [
      ("filename", str_ info.filename),
      ("row", str_ info.row)])
    printFunc
    eqFunc
    l
    r

let utestAst = lam ty. lam info. lam l. lam r.
  utestRunnerCall info (_printFunc ty) (_eqFunc ty) l r

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
    match t.tusing with Some eqFunc then
      let eqFunc =
        ulam_ "a"
          (ulam_ "b"
            (appf2_ eqFunc (var_ "a") (var_ "b"))) in
      utestRunnerCall utestInfo (_printFunc ty) eqFunc t.test t.expected
    else
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

let intNoUsing = typeAnnot (utest_info_ (int_ 1) (int_ 0) unit_) in
eval {env = builtinEnv} (symbolize (utestGen intNoUsing));
utest utestStrip intNoUsing with unit_ using eqExpr in

let intWithUsing = typeAnnot (
  utestu_info_ (int_ 1) (int_ 0) unit_ (const_ (CGeqi{}))) in
eval {env = builtinEnv} (symbolize (utestGen intWithUsing));
utest utestStrip intWithUsing with unit_ using eqExpr in

let lhs = seq_ [seq_ [int_ 1, int_ 2], seq_ [int_ 3, int_ 4]] in
let rhs = reverse_ (seq_ [
  reverse_ (seq_ [int_ 4, int_ 3]),
  reverse_ (seq_ [int_ 2, int_ 1])]) in
let nestedSeqInt = typeAnnot (utest_info_ lhs rhs unit_) in
eval {env = builtinEnv} (symbolize (utestGen nestedSeqInt));
utest utestStrip nestedSeqInt with unit_ using eqExpr in

let lhs = seq_ [
  float_ 6.5, float_ 1.0, float_ 0.0, float_ 3.14
] in
let rhs = reverse_ (seq_ [
  float_ 3.14, float_ 0.0, float_ 1.0, float_ 6.5
]) in
let elemEq = const_ (CEqf ()) in
let seqEq =
  ulam_ "a"
    (ulam_ "b" (appf3_ (var_ "eqSeq") elemEq (var_ "a") (var_ "b"))) in
let floatSeqWithUsing = typeAnnot (utestu_info_ lhs rhs unit_ seqEq) in
eval {env = builtinEnv} (symbolize (utestGen floatSeqWithUsing));
utest utestStrip floatSeqWithUsing with unit_ using eqExpr in

let charNoUsing = typeAnnot (utest_info_ (char_ 'a') (char_ 'A') unit_) in
eval {env = builtinEnv} (symbolize (utestGen charNoUsing));
utest utestStrip charNoUsing with unit_ using eqExpr in

let charWithUsing = typeAnnot (bindall_ [
  ulet_ "leqChar" (ulam_ "c1" (ulam_ "c2" (
    leqi_ (char2int_ (var_ "c1")) (char2int_ (var_ "c2"))
  ))),
  ulet_ "geqChar" (ulam_ "c1" (ulam_ "c2" (
    geqi_ (char2int_ (var_ "c1")) (char2int_ (var_ "c2"))
  ))),
  ulet_ "char2lower" (ulam_ "c" (
    if_
      (and_
        (appf2_ (var_ "geqChar") (var_ "c") (char_ 'A'))
        (appf2_ (var_ "leqChar") (var_ "c") (char_ 'Z')))
      (int2char_ (addi_ (char2int_ (var_ "c")) (int_ 32)))
      (var_ "c")
  )),
  ulet_ "charEqIgnoreCase"
    (ulam_ "a"
      (ulam_ "b"
        (eqc_
          (app_ (var_ "char2lower") (var_ "a"))
          (app_ (var_ "char2lower") (var_ "b"))))),
  utestu_info_ (char_ 'a') (char_ 'A') unit_ (var_ "charEqIgnoreCase")
]) in
eval {env = builtinEnv} (symbolize (utestGen charWithUsing));

()
