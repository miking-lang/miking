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
  "gensym",
  "eqsym",
  "hash"
]

let _symbOp = _op (_opHashMap "Boot.Intrinsics.Symb." _symbOps)

let _floatOps = [
  "floorfi",
  "ceilfi",
  "roundfi"
]

let _floatOp = _op (_opHashMap "Boot.Intrinsics.FloatConversion." _floatOps)

-- Input is a map from name to be introduced to name containing the value to be bound to that location
-- Output is essentially `M.toList input & unzip & \(pats, exprs) -> (OPTuple pats, TmTuple exprs)`
-- alternatively output is made such that if (_mkFinalPatExpr ... = (pat, expr)) then let 'pat = 'expr
-- (where ' splices things into expressions) binds the appropriate names to the appropriate values
-- INVARIANT: two semantically equal maps produce the same output, i.e., we preserve an equality that is stronger than structural
let _mkFinalPatExpr : Map Name Name -> (Pat, Expr) = use OCamlAst in lam nameMap.
  let cmp = lam n1. lam n2. subi (sym2hash (optionGetOr (negi 1) (nameGetSym n1.0))) (sym2hash (optionGetOr (negi 1) (nameGetSym n2.0))) in
  match unzip (sort cmp (assoc2seq {eq=nameEqSym} nameMap)) with (patNames, exprNames) then
    (OPTuple {pats = map npvar_ patNames}, OTmTuple {values = map nvar_ exprNames})
  else never

-- Construct a match expression that matches against an option
let _someName = nameSym "Option.Some"
let _noneName = nameSym "Option.None"
let _optMatch = use OCamlAst in lam target. lam somePat. lam someExpr. lam noneExpr.
  OTmMatch
  { target = target
  , arms =
    [ (OPCon {ident = _someName, args = [somePat]}, someExpr)
    , (OPCon {ident = _noneName, args = []}, noneExpr)]}
let _some = use OCamlAst in lam val. OTmConApp {ident = _someName, args = [val]}
let _none = use OCamlAst in OTmConApp {ident = _noneName, args = []}
let _if = use OCamlAst in lam cond. lam thn. lam els. OTmMatch {target = cond, arms = [(ptrue_, thn), (pfalse_, els)]}
let _tuplet = use OCamlAst in lam pats. lam val. lam body. OTmMatch {target = val, arms = [(OPTuple {pats = pats}, body)]}

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
  -- Float intrinsics
  | CFloorfi {} -> _floatOp "floorfi"
  | CCeilfi {} -> _floatOp "ceilfi"
  | CRoundfi {} -> _floatOp "roundfi"
  | v -> TmConst { val = v }

  sem generate =
  | TmSeq {tms = tms} ->
    let tms = map generate tms in
    foldr (lam tm. lam a. appSeq_ (_seqOp "cons") [tm, a])
          (_seqOp "empty")
          tms
  | TmConst {val = val} -> generateConst val
  | TmMatch {target = target, pat = pat, thn = thn, els = els} ->
    let tname = nameSym "_target" in
    match generatePat tname pat with (nameMap, wrap) then
      match _mkFinalPatExpr nameMap with (pat, expr) then
        _optMatch
          (bind_ (nulet_ tname (generate target)) (wrap (_some expr)))
          pat
          (generate thn)
          (generate els)
      else never
    else never
  | t -> smap_Expr_Expr generate t

  sem generatePat (targetName : Name) /- : Pat -> (AssocMap Name Name, Expr -> Expr) -/ =
  | PNamed {ident = PWildcard _} -> (assocEmpty, identity)
  | PNamed {ident = PName n} -> (assocInsert {eq=nameEqSym} n targetName assocEmpty, identity)
  | PBool {val = val} ->
    let wrap = lam cont.
      if_ (nvar_ targetName)
        (if val then cont else _none)
        (if val then _none else cont)
    in (assocEmpty, wrap)
  | PInt {val = val} ->
    (assocEmpty, lam cont. _if (eqi_ (nvar_ targetName) (int_ val)) cont _none)
  | PChar {val = val} ->
    (assocEmpty, lam cont. _if (eqi_ (nvar_ targetName) (char_ val)) cont _none)
  | PSeqTot {pats = pats} ->
    let genOne = lam i. lam pat.
      let n = nameSym "_seqElem" in
      match generatePat n pat with (names, innerWrap) then
        let wrap = lam cont.
          bind_
            (nlet_ n tyunknown_ (appf2_ (_seqOp "get") (nvar_ targetName) (int_ i)))
            (innerWrap cont)
        in (names, wrap)
      else never in
    match unzip (mapi genOne pats) with (allNames, allWraps) then
      let wrap = lam cont.
        _if (eqi_ (app_ (_seqOp "length") (nvar_ targetName)) (int_ (length pats)))
          (foldr (lam f. lam v. f v) cont allWraps)
          _none in
      ( foldl (assocMergePreferRight {eq=nameEqSym}) assocEmpty allNames
      , wrap
      )
    else never
  | PSeqEdge {prefix = prefix, middle = middle, postfix = postfix} ->
    let apply = lam f. lam x. f x in
    let mergeNames = assocMergePreferRight {eq=nameEqSym} in
    let minLen = addi (length prefix) (length postfix) in
    let preName = nameSym "_prefix" in
    let tempName = nameSym "_splitTemp" in
    let midName = nameSym "_middle" in
    let postName = nameSym "_postfix" in
    let genOne = lam targetName. lam i. lam pat.
      let n = nameSym "_seqElem" in
      match generatePat n pat with (names, innerWrap) then
        let wrap = lam cont.
          bind_
            (nlet_ n tyunknown_ (appf2_ (_seqOp "get") (nvar_ targetName) (int_ i)))
            (innerWrap cont)
        in (names, wrap)
      else never in
    match unzip (mapi (genOne preName) prefix) with (preNames, preWraps) then
      match unzip (mapi (genOne postName) postfix) with (postNames, postWraps) then
        let names = foldl mergeNames assocEmpty (concat preNames postNames) in
        let names = match middle with PName n then assocInsert {eq=nameEqSym} n midName names else names in
        let wrap = lam cont.
          _if (lti_ (appf1_ (_seqOp "length") (nvar_ targetName)) (int_ minLen))
            _none
            (_tuplet [npvar_ preName, npvar_ tempName]
              (appf2_ (_seqOp "split_at") (nvar_ targetName) (int_ (length prefix)))
              (_tuplet [npvar_ midName, npvar_ postName]
                (appf2_ (_seqOp "split_at") (nvar_ tempName) (subi_ (appf1_ (_seqOp "length") (nvar_ tempName)) (int_ (length postfix))))
                (foldr apply (foldr apply cont postWraps) preWraps))) in
        (names, wrap)
      else never
    else never
  | POr {lpat = lpat, rpat = rpat} ->
    match generatePat targetName lpat with (lnames, lwrap) then
      match generatePat targetName rpat with (rnames, rwrap) then
        match _mkFinalPatExpr lnames with (lpat, lexpr) then
          match _mkFinalPatExpr rnames with (_, rexpr) then  -- NOTE(vipa, 2020-12-03): the pattern is identical between the two, assuming the two branches bind exactly the same names, which they should
            let names = assocMapWithKey {eq=nameEqSym} (lam k. lam _. k) lnames in
            let xname = nameSym "_x" in
            let wrap = lam cont.
              _optMatch
                (_optMatch
                   (lwrap (_some lexpr))
                   (npvar_ xname)
                   (_some (nvar_ xname))
                   (rwrap (_some rexpr)))
                lpat
                cont
                _none
            in (names, wrap)
          else never
        else never
      else never
    else never
  | PAnd {lpat = lpat, rpat = rpat} ->
    match generatePat targetName lpat with (lnames, lwrap) then
      match generatePat targetName rpat with (rnames, rwrap) then
        let names = assocMergePreferRight {eq=nameEqSym} lnames rnames in
        let wrap = lam cont. lwrap (rwrap cont) in
        (names, wrap)
      else never
    else never
  | PNot {subpat = pat} ->
    match generatePat targetName pat with (_, innerWrap) then
      let wrap = lam cont.
        _optMatch (innerWrap (_some (OTmTuple {values = []})))
          pvarw_
          _none
          cont in
      (assocEmpty, wrap)
    else never
end

lang OCamlTest = OCamlGenerate + OCamlPrettyPrint + MExprSym + ConstEq
                 + IntEq + BoolEq + CharEq + FloatEq

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
    let res = ocamlCompileWithConfig {warnings=false} (join ["print_string (", strConvert, "(", p, "))"]) in
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
    else match t.val with CFloat _ then
      let ocamlVal = ocamlEval (expr2str ocamlAst) "string_of_float" in
      match ocamlVal with TmConst {val = CFloat _} then
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

-- Match
let matchChar1 = symbolize
  (match_ (char_ 'a')
    (pchar_ 'a')
    true_
    false_) in
utest matchChar1 with generate matchChar1 using sameSemantics in

let matchChar2 = symbolize
  (match_ (char_ 'a')
    (pchar_ 'b')
    true_
    false_) in
utest matchChar2 with generate matchChar2 using sameSemantics in

let matchSeq = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3])
    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
    (addi_ (var_ "a") (var_ "b"))
    (int_ 42)) in
utest matchSeq with generate matchSeq using sameSemantics in

let noMatchSeq1 = symbolize
  (match_ (seq_ [int_ 2, int_ 2, int_ 3])
    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
    (addi_ (var_ "a") (var_ "b"))
    (int_ 42)) in
utest noMatchSeq1 with generate noMatchSeq1 using sameSemantics in

let noMatchSeqLen = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
    (addi_ (var_ "a") (var_ "b"))
    (int_ 42)) in
utest noMatchSeqLen with generate noMatchSeqLen using sameSemantics in

let noMatchSeqLen2 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
    (addi_ (var_ "a") (var_ "b"))
    (int_ 42)) in
utest noMatchSeqLen2 with generate noMatchSeqLen2 using sameSemantics in

let matchOr1 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchOr1 with generate matchOr1 using sameSemantics in

let matchOr2 = symbolize
  (match_ (seq_ [int_ 2, int_ 1])
    (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchOr2 with generate matchOr2 using sameSemantics in

let matchOr3 = symbolize
  (match_ (seq_ [int_ 3, int_ 1])
    (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchOr3 with generate matchOr3 using sameSemantics in

let matchNestedOr1 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"])) (pseqtot_ [pint_ 3, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchNestedOr1 with generate matchNestedOr1 using sameSemantics in

let matchNestedOr2 = symbolize
  (match_ (seq_ [int_ 2, int_ 1])
    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"])) (pseqtot_ [pint_ 3, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchNestedOr2 with generate matchNestedOr2 using sameSemantics in

let matchNestedOr3 = symbolize
  (match_ (seq_ [int_ 3, int_ 7])
    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"])) (pseqtot_ [pint_ 3, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchNestedOr3 with generate matchNestedOr3 using sameSemantics in

let matchNestedOr4 = symbolize
  (match_ (seq_ [int_ 4, int_ 7])
    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"])) (pseqtot_ [pint_ 3, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchNestedOr4 with generate matchNestedOr4 using sameSemantics in

let matchNot1 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pnot_ (pseqtot_ [pint_ 1, pvar_ "a"]))
    true_
    false_) in
utest matchNot1 with generate matchNot1 using sameSemantics in

let matchNot2 = symbolize
  (match_ (seq_ [int_ 2, int_ 2])
    (pnot_ (pseqtot_ [pint_ 1, pvar_ "a"]))
    true_
    false_) in
utest matchNot2 with generate matchNot2 using sameSemantics in

let matchAnd1 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pvar_ "b"))
    (addi_ (var_ "a") (get_ (var_ "b") (int_ 1)))
    (int_ 53)) in
utest matchAnd1 with generate matchAnd1 using sameSemantics in

let matchAnd2 = symbolize
  (match_ (seq_ [int_ 2, int_ 2])
    (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pvar_ "b"))
    (addi_ (var_ "a") (get_ (var_ "b") (int_ 1)))
    (int_ 53)) in
utest matchAnd2 with generate matchAnd2 using sameSemantics in

let matchAnd3 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ []))
    (var_ "a")
    (int_ 53)) in
utest matchAnd3 with generate matchAnd3 using sameSemantics in

let matchAnd4 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pand_ (pseqtot_ []) (pseqtot_ [pint_ 1, pvar_ "a"]))
    (var_ "a")
    (int_ 53)) in
utest matchAnd4 with generate matchAnd4 using sameSemantics in

let matchSeqEdge1 = symbolize
  (match_ (seq_ [int_ 1])
    (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
    (addi_ (var_ "a") (var_ "c"))
    (int_ 75)) in
utest matchSeqEdge1 with generate matchSeqEdge1 using sameSemantics in

let matchSeqEdge2 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
    (addi_ (var_ "a") (var_ "c"))
    (int_ 75)) in
utest matchSeqEdge2 with generate matchSeqEdge2 using sameSemantics in

let matchSeqEdge3 = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3])
    (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
    (addi_ (var_ "a") (var_ "c"))
    (int_ 75)) in
utest matchSeqEdge3 with generate matchSeqEdge3 using sameSemantics in

let matchSeqEdge4 = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
    (pseqedge_ [pvar_ "a", pvar_ "d"] "b" [pvar_ "c"])
    (addi_ (addi_ (var_ "d") (var_ "a")) (var_ "c"))
    (int_ 75)) in
utest matchSeqEdge4 with generate matchSeqEdge4 using sameSemantics in

let matchSeqEdge5 = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
    (por_ (pseqedge_ [pint_ 2] "b" []) (pseqedge_ [pint_ 1] "b" []))
    (match_ (var_ "b")
      (pseqedgew_ [pvar_ "a"] [pvar_ "c"])
      (addi_ (var_ "a") (var_ "c"))
      (int_ 84))
    (int_ 75)) in
utest matchSeqEdge5 with generate matchSeqEdge5 using sameSemantics in

let matchSeqEdge6 = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
    (por_ (pseqedge_ [pint_ 2] "b" []) (pseqedge_ [] "b" [pint_ 4]))
    (match_ (var_ "b")
      (pseqedgew_ [pvar_ "a"] [pvar_ "c"])
      (addi_ (var_ "a") (var_ "c"))
      (int_ 84))
    (int_ 75)) in
utest matchSeqEdge6 with generate matchSeqEdge6 using sameSemantics in

let matchSeqEdge7 = symbolize
  (match_ (seq_ [int_ 1])
    (pseqedgew_ [pvar_ "a"] [])
    (var_ "a")
    (int_ 75)) in
utest matchSeqEdge7 with generate matchSeqEdge7 using sameSemantics in
let symbAndGen = lam e. generate (symbolize e) in

-- Ints
let addInt1 = addi_ (int_ 1) (int_ 2) in
utest addInt1 with symbAndGen addInt1 using sameSemantics in

let addInt2 = addi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest addInt2 with symbAndGen addInt2 using sameSemantics in

let testMulInt = muli_ (int_ 2) (int_ 3) in
utest testMulInt with symbAndGen testMulInt using sameSemantics in

let testModInt = modi_ (int_ 2) (int_ 3) in
utest testModInt with symbAndGen testModInt using sameSemantics in

let testDivInt = divi_ (int_ 2) (int_ 3) in
utest testDivInt with symbAndGen testDivInt using sameSemantics in

let testNegInt = addi_ (int_ 2) (negi_ (int_ 2)) in
utest testNegInt with symbAndGen testNegInt using sameSemantics in

let compareInt1 = eqi_ (int_ 1) (int_ 2) in
utest compareInt1 with symbAndGen compareInt1
using sameSemantics in

let compareInt2 = lti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt2 with symbAndGen compareInt2
using sameSemantics in

-- Chars
let charLiteral = char_ 'c' in
utest charLiteral with symbAndGen charLiteral
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

-- TODO(Oscar Eriksson, 2020-11-30) Test symbol operations when we have
-- implemented tuples/records.

-- Float-Integer conversions
let testFloorfi = floorfi_ (float_ 1.5) in
utest testFloorfi with generate testFloorfi using sameSemantics in

let testCeilfi = ceilfi_ (float_ 1.5) in
utest testCeilfi with generate testCeilfi using sameSemantics in

let testRoundfi = roundfi_ (float_ 1.5) in
utest testRoundfi with generate testRoundfi using sameSemantics in

let testInt2float = int2float_ (int_ 1) in
utest testInt2float with generate testInt2float using sameSemantics in

()
