include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eq.mc"
include "mexpr/eval.mc"
include "mexpr/parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/type-lift.mc"
include "ocaml/ast.mc"
include "ocaml/pprint.mc"
include "ocaml/compile.mc"
include "hashmap.mc"

let _opHashMap = lam prefix. lam ops.
  let mkOp = lam op. nameSym (join [prefix, op]) in
  foldl (lam a. lam op. hashmapInsert hashmapStrTraits op (mkOp op) a)
        hashmapEmpty
        ops

let _op = lam opHashMap. lam op.
  nvar_
  (hashmapLookupOrElse hashmapStrTraits
    (lam.
      error (strJoin " " ["Operation", op, "not found"]))
      op
      opHashMap)

let _seqOps = [
  "create",
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
  "roundfi",
  "string2float"
]

let _floatOp = _op (_opHashMap "Boot.Intrinsics.FloatConversion." _floatOps)

-- Input is a map from name to be introduced to name containing the value to be bound to that location
-- Output is essentially `M.toList input & unzip & \(pats, exprs) -> (OPatTuple pats, TmTuple exprs)`
-- alternatively output is made such that if (_mkFinalPatExpr ... = (pat, expr)) then let 'pat = 'expr
-- (where ' splices things into expressions) binds the appropriate names to the appropriate values
-- INVARIANT: two semantically equal maps produce the same output, i.e., we preserve an equality that is stronger than structural
let _mkFinalPatExpr : Map Name Name -> (Pat, Expr) = use OCamlAst in lam nameMap.
  let cmp = lam n1. lam n2. subi (sym2hash (optionGetOr (negi 1) (nameGetSym n1.0))) (sym2hash (optionGetOr (negi 1) (nameGetSym n2.0))) in
  match unzip (sort cmp (assoc2seq {eq=nameEqSym} nameMap)) with (patNames, exprNames) then
    (OPatTuple {pats = map npvar_ patNames}, OTmTuple {values = map nvar_ exprNames})
  else never

-- Construct a match expression that matches against an option
let _someName = nameSym "Option.Some"
let _noneName = nameSym "Option.None"
let _optMatch = use OCamlAst in lam target. lam somePat. lam someExpr. lam noneExpr.
  OTmMatch
  { target = target
  , arms =
    [ (OPatCon {ident = _someName, args = [somePat]}, someExpr)
    , (OPatCon {ident = _noneName, args = []}, noneExpr)]}
let _some = use OCamlAst in lam val. OTmConApp {ident = _someName, args = [val]}
let _none = use OCamlAst in OTmConApp {ident = _noneName, args = []}
let _if = use OCamlAst in lam cond. lam thn. lam els. OTmMatch {target = cond, arms = [(ptrue_, thn), (pfalse_, els)]}
let _tuplet = use OCamlAst in lam pats. lam val. lam body. OTmMatch {target = val, arms = [(OPatTuple {pats = pats}, body)]}

lang OCamlGenerate = MExprAst + OCamlAst
  sem generateConst =
  -- Sequence intrinsics
  | CCreate {} -> _seqOp "create"
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
  -- Int-Float Conversion intrinsics
  | CFloorfi {} -> _floatOp "floorfi"
  | CCeilfi {} -> _floatOp "ceilfi"
  | CRoundfi {} -> _floatOp "roundfi"
  | CString2float {} -> _floatOp "string2float"
  | v -> TmConst { val = v }

  sem generate (variants : Map Name Type) =
  | TmSeq {tms = tms} ->
    let tms = map (generate variants) tms in
    foldr (lam tm. lam a. appSeq_ (_seqOp "cons") [tm, a])
          (_seqOp "empty")
          tms
  | TmConst {val = val} -> generateConst val
  | TmMatch {target = target, pat = pat, thn = thn, els = els} ->
    let tname = nameSym "_target" in
    match generatePat variants tname pat with (nameMap, wrap) then
      match _mkFinalPatExpr nameMap with (pat, expr) then
        _optMatch
          (bind_ (nulet_ tname (generate variants target)) (wrap (_some expr)))
          pat
          (generate variants thn)
          (generate variants els)
      else never
    else never
  | TmType t -> generate variants t.inexpr
  | TmConDef t -> generate variants t.inexpr
  | TmConApp t -> OTmConApp {ident = t.ident, args = [generate variants t.body]}
  | t -> smap_Expr_Expr (generate variants) t

  /- : Pat -> (AssocMap Name Name, Expr -> Expr) -/
  sem generatePat (variants : Map Name Type) (targetName : Name) =
  | PatNamed {ident = PWildcard _} -> (assocEmpty, identity)
  | PatNamed {ident = PName n} -> (assocInsert {eq=nameEqSym} n targetName assocEmpty, identity)
  | PatBool {val = val} ->
    let wrap = lam cont.
      if_ (nvar_ targetName)
        (if val then cont else _none)
        (if val then _none else cont)
    in (assocEmpty, wrap)
  | PatInt {val = val} ->
    (assocEmpty, lam cont. _if (eqi_ (nvar_ targetName) (int_ val)) cont _none)
  | PatChar {val = val} ->
    (assocEmpty, lam cont. _if (eqc_ (nvar_ targetName) (char_ val)) cont _none)
  | PatSeqTot {pats = pats} ->
    let genOne = lam i. lam pat.
      let n = nameSym "_seqElem" in
      match generatePat variants n pat with (names, innerWrap) then
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
  | PatSeqEdge {prefix = prefix, middle = middle, postfix = postfix} ->
    let apply = lam f. lam x. f x in
    let mergeNames = assocMergePreferRight {eq=nameEqSym} in
    let minLen = addi (length prefix) (length postfix) in
    let preName = nameSym "_prefix" in
    let tempName = nameSym "_splitTemp" in
    let midName = nameSym "_middle" in
    let postName = nameSym "_postfix" in
    let genOne = lam targetName. lam i. lam pat.
      let n = nameSym "_seqElem" in
      match generatePat variants n pat with (names, innerWrap) then
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
  | PatOr {lpat = lpat, rpat = rpat} ->
    match generatePat variants targetName lpat with (lnames, lwrap) then
      match generatePat variants targetName rpat with (rnames, rwrap) then
        match _mkFinalPatExpr lnames with (lpat, lexpr) then
          match _mkFinalPatExpr rnames with (_, rexpr) then  -- NOTE(vipa, 2020-12-03): the pattern is identical between the two, assuming the two branches bind exactly the same names, which they should
            let names = assocMapWithKey {eq=nameEqSym} (lam k. lam. k) lnames in
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
  | PatAnd {lpat = lpat, rpat = rpat} ->
    match generatePat variants targetName lpat with (lnames, lwrap) then
      match generatePat variants targetName rpat with (rnames, rwrap) then
        let names = assocMergePreferRight {eq=nameEqSym} lnames rnames in
        let wrap = lam cont. lwrap (rwrap cont) in
        (names, wrap)
      else never
    else never
  | PatNot {subpat = pat} ->
    match generatePat variants targetName pat with (_, innerWrap) then
      let wrap = lam cont.
        _optMatch (innerWrap (_some (OTmTuple {values = []})))
          pvarw_
          _none
          cont in
      (assocEmpty, wrap)
    else never
  | PatRecord {bindings = bindings} ->
    let genBindingPat = lam id. lam pat.
      let n = nameSym "_recordElem" in
      match generatePat variants n pat with (names,innerWrap) then
        let wrap = lam cont.
          bind_ (nulet_ n (nvar_ (nameNoSym id))) (innerWrap cont)
        in
        (names, wrap)
      else never
    in
    let genPats = map (lam p. genBindingPat p.0 p.1) (assoc2seq {eq=eqString} bindings) in
    -- TODO(larshum, 20210226): This name should be chosen based on the type of
    -- the matched record.
    let n = nameSym "Rec" in
    match unzip genPats with (allNames, allWraps) then
      let f = lam id. lam. pvar_ id in
      let precord = OPatRecord {bindings = assocMapWithKey {eq=eqString} f bindings} in
      let wrap = lam cont.
        OTmMatch {
          target = nvar_ targetName,
          arms = [
            (OPatCon {ident = n, args = [precord]}, foldr (lam f. lam v. f v) cont allWraps)
          ]
        }
      in
      ( foldl (assocMergePreferRight {eq=nameEqSym}) assocEmpty allNames
      , wrap
      )
    else never
  | PatCon {ident = id, subpat = subpat} ->
    let conVarName = nameSym "_n" in
    match generatePat variants conVarName subpat with (names, subwrap) then
      let wrap = lam cont.
        OTmMatch {
          target = subwrap (nvar_ targetName),
          arms = [
            (OPatCon {ident = id, args = [npvar_ conVarName]}, cont),
            (pvarw_, _none)
          ]
        } in
      (names, wrap)
    else never
end

let _objTypeName = nameSym "Obj.t"
let _objType = ntyvar_ _objTypeName

let _unnestRecordTypes = lam recordTypes.
  use MExprAst in
  recursive let unnestRecordType = lam acc. lam ty.
    match ty with TyRecord t then
      let fields = assoc2seq {eq=eqString} t.fields in
      if null fields then acc
      else
        let acc = snoc acc ty in
        let fieldTypes = map (lam f. f.1) fields in
        foldl unnestRecordType acc fieldTypes
    else match ty with TyUnknown {} then
      error "Cannot generate type declaration from untyped record"
    else acc
  in
  foldl unnestRecordType [] recordTypes

let _objTyped = lam ty.
  use RecordTypeAst in
  match ty with TyRecord t then
    if eqi (assocLength t.fields) 0 then _objType
    else
      let fields = assocMap {eq=eqString} (lam. _objType) t.fields in
      TyRecord {t with fields = fields}
  else _objType

let _objTypedRecordFields = lam recordTypes.
  map _objTyped recordTypes

let _objTypedConstructors = lam constructors.
  use RecordTypeAst in
  map (lam p. (p.0, _objTyped p.1)) constructors

lang OCamlRecordDeclGenerate = OCamlAst + MExprEq + RecordAst
  sem generateOCamlRecords (namedRecords : [(Name, Type)]) =
  | TmRecord t ->
    if null t.bindings then OTmRecord {bindings = []}
    else
      let ty = get (_objTypedRecordFields [t.ty]) 0 in
      match find (lam r. eqType assocEmpty ty r.1) namedRecords with Some r then
        let bindings = assocMap {eq=eqString} (generateOCamlRecords namedRecords) t.bindings in
        let bindings = assoc2seq {eq=eqString} bindings in
        OTmConApp {ident = r.0, args = [OTmRecord {bindings = bindings}]}
      else never
  | t -> smap_Expr_Expr (generateOCamlRecords namedRecords) t

  sem generateRecordDecl (recordTypes : [Type]) =
  | expr ->
    let nestedRecordTypes = _unnestRecordTypes recordTypes in
    let objRecords = distinct (eqType assocEmpty)
                              (_objTypedRecordFields nestedRecordTypes) in
    let namedObjRecords = map (lam r. (nameSym "Rec", r)) objRecords in
    let expr = generateOCamlRecords namedObjRecords expr in
    let f = lam acc. lam record.
      let recordVariantName = record.0 in
      (
        OTmVariantTypeDecl {
          ident = nameSym "record",
          constrs = [record],
          inexpr = acc
        },
        recordVariantName
      )
    in
    mapAccumL f expr namedObjRecords
end

lang OCamlVariantDeclGenerate = OCamlAst
  sem generateVariantDecl (variantTypes: Map Name [Map Name Type]) =
  | expr ->
    let variantTypesSeq = mapBindings variantTypes in
    let f = lam acc. lam variant.
      match variant with (variantName, constrMap) then
        let constructors = _objTypedConstructors (mapBindings constrMap) in
        OTmVariantTypeDecl {
          ident = variantName,
          constrs = constructors,
          inexpr = acc
        }
      else never
    in
    foldl f expr variantTypesSeq
end

lang OCamlDeclGenerate =
  MExprTypeLift + OCamlRecordDeclGenerate + OCamlVariantDeclGenerate
  sem generateDecl =
  | expr ->
    let recordTypes = liftRecords expr in
    let variantTypes = liftVariants expr in
    match generateRecordDecl recordTypes expr with (expr, recVariantTypes) then
      let expr = generateVariantDecl variantTypes expr in
      -- Convert Map Name (Map Name Type) -> Map Name Type because we don't
      -- need name of the variant type, only names of constructors. Names are
      -- unique so we know that the resulting map will not have colliding keys.
      let mexprVariantMap =
        mapFromList nameCmp (join (map (lam p. mapBindings p.1) (mapBindings variantTypes)))
      in
      let recordVariantMap = mapFromList nameCmp recVariantTypes in
      (expr, mapUnion mexprVariantMap recordVariantMap)
    else never
end

let _objReprName = nameSym "Obj.repr"
let _objTName = nameSym "Obj.t"
let _objObjName = nameSym "Obj.obj"

let _objRepr = lam t. app_ (nvar_ _objReprName) t
let _objObj = lam t. app_ (nvar_ _objObjName) t

lang OCamlObjWrap = MExprAst
  sem objWrapRec =
  | (TmConst {val = (CInt _) | (CFloat _) | (CChar _) | (CBool _)}) & t ->
    _objRepr t
  | TmConst {val = c} -> c
  | t -> smap_Expr_Expr objWrapRec t

  sem objWrap =
  | t ->
    _objObj (objWrapRec t)
end

lang OCamlTest = OCamlGenerate + OCamlDeclGenerate + OCamlPrettyPrint +
                 MExprSym + ConstEq + IntEq + BoolEq + CharEq + FloatEq +
                 MExprTypeAnnot + OCamlObjWrap

mexpr

use OCamlTest in

-- Test semantics

-- Parse helper
let parseAsMExpr = lam s.
  use MExprParser in parseExpr (initPos "") s
in

-- Evaluates OCaml expressions [strConvert] given as string, applied
-- to [p], and parses it as a mexpr expression.
let ocamlEval = lam p.
  let subprocess = pyimport "subprocess" in
  let blt = pyimport "builtins" in
  let res = ocamlCompileWithConfig {warnings=false} (expr2str p) in
  let out = (res.run "" []).stdout in
  res.cleanup ();
  printLn (expr2str p);
  parseAsMExpr out
in

-- Compares evaluation of [mexprAst] as a mexpr and evaluation of
-- [ocamlAst] as a OCaml expression.
let sameSemantics = lam mexprAst. lam ocamlAst.
  let mexprVal =
    use MExprEval in
    eval {env = []} mexprAst
  in
  recursive
  let ocamlAstWithPrinting = lam ast. lam printTerm.
    match ast with OTmVariantTypeDecl t then
      OTmVariantTypeDecl {t with inexpr = ocamlAstWithPrinting t.inexpr printTerm}
    else app_ printTerm ast
  in
  let printfVar = nvar_ (nameSym "Printf.printf") in
  let ocamlAst = ocamlAstWithPrinting ocamlAst in
  match mexprVal with TmConst t then
    match t.val with CInt _ then
      let ocamlVal = ocamlEval (ocamlAst (app_ printfVar (str_ "%d"))) in
      match ocamlVal with TmConst {val = CInt _} then
        eqExpr mexprVal ocamlVal
      else error "Values mismatch"
    else match t.val with CFloat _ then
      let ocamlVal = ocamlEval (ocamlAst (app_ printfVar (str_ "%f"))) in
      match ocamlVal with TmConst {val = CFloat _} then
        eqExpr mexprVal ocamlVal
      else error "Values mismatch"
    else match t.val with CBool _ then
      let ocamlVal = ocamlEval (ocamlAst (app_ printfVar (str_ "%b"))) in
      match ocamlVal with TmConst {val = CBool _} then
        eqExpr mexprVal ocamlVal
      else error "Values mismatch"
    else match t.val with CChar _ then
      let ocamlVal = ocamlEval (ocamlAst (app_ printfVar (str_ "'%c'"))) in
      match ocamlVal with TmConst {val = CChar _} then
        eqExpr mexprVal ocamlVal
      else error "Values mismatch"
    else error "Unsupported constant"
  else error "Unsupported value"
in

let generateEmptyVariants = lam t.
  objWrap (generate (mapEmpty nameCmp) t)
in

let generateTypeAnnotated = lam t.
  match generateDecl (typeAnnot t) with (t, variants) then
    generate variants t
  else never
in

let stripTypeDecls = lam t.
  recursive
  let stripDecls = lam t.
    match t with TmType {inexpr = inexpr} then stripDecls inexpr
    else match t with TmConDef {inexpr = inexpr} then stripDecls inexpr
    else smap_Expr_Expr stripDecls t
  in
  stripDecls t
in

-- Match
--let matchChar1 = symbolize
--  (match_ (char_ 'a')
--    (pchar_ 'a')
--    true_
--    false_) in
--utest matchChar1 with generateEmptyVariants matchChar1 using sameSemantics in
--
--let matchChar2 = symbolize
--  (match_ (char_ 'a')
--    (pchar_ 'b')
--    true_
--    false_) in
--utest matchChar2 with generateEmptyVariants matchChar2 using sameSemantics in
--
--let matchSeq = symbolize
--  (match_ (seq_ [int_ 1, int_ 2, int_ 3])
--    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
--    (addi_ (var_ "a") (var_ "b"))
--    (int_ 42)) in
--utest matchSeq with generateEmptyVariants matchSeq using sameSemantics in
--
--let noMatchSeq1 = symbolize
--  (match_ (seq_ [int_ 2, int_ 2, int_ 3])
--    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
--    (addi_ (var_ "a") (var_ "b"))
--    (int_ 42)) in
--utest noMatchSeq1 with generateEmptyVariants noMatchSeq1 using sameSemantics in
--
--let noMatchSeqLen = symbolize
--  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
--    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
--    (addi_ (var_ "a") (var_ "b"))
--    (int_ 42)) in
--utest noMatchSeqLen with generateEmptyVariants noMatchSeqLen using sameSemantics in
--
--let noMatchSeqLen2 = symbolize
--  (match_ (seq_ [int_ 1, int_ 2])
--    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
--    (addi_ (var_ "a") (var_ "b"))
--    (int_ 42)) in
--utest noMatchSeqLen2 with generateEmptyVariants noMatchSeqLen2 using sameSemantics in
--
--let matchOr1 = symbolize
--  (match_ (seq_ [int_ 1, int_ 2])
--    (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--    (var_ "a")
--    (int_ 42)) in
--utest matchOr1 with generateEmptyVariants matchOr1 using sameSemantics in
--
--let matchOr2 = symbolize
--  (match_ (seq_ [int_ 2, int_ 1])
--    (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--    (var_ "a")
--    (int_ 42)) in
--utest matchOr2 with generateEmptyVariants matchOr2 using sameSemantics in
--
--let matchOr3 = symbolize
--  (match_ (seq_ [int_ 3, int_ 1])
--    (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--    (var_ "a")
--    (int_ 42)) in
--utest matchOr3 with generateEmptyVariants matchOr3 using sameSemantics in
--
--let matchNestedOr1 = symbolize
--  (match_ (seq_ [int_ 1, int_ 2])
--    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--          (pseqtot_ [pint_ 3, pvar_ "a"]))
--    (var_ "a")
--    (int_ 42)) in
--utest matchNestedOr1 with generateEmptyVariants matchNestedOr1 using sameSemantics in
--
--let matchNestedOr2 = symbolize
--  (match_ (seq_ [int_ 2, int_ 1])
--    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--          (pseqtot_ [pint_ 3, pvar_ "a"]))
--    (var_ "a")
--    (int_ 42)) in
--utest matchNestedOr2 with generateEmptyVariants matchNestedOr2 using sameSemantics in
--
--let matchNestedOr3 = symbolize
--  (match_ (seq_ [int_ 3, int_ 7])
--    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--          (pseqtot_ [pint_ 3, pvar_ "a"]))
--    (var_ "a")
--    (int_ 42)) in
--utest matchNestedOr3 with generateEmptyVariants matchNestedOr3 using sameSemantics in
--
--let matchNestedOr4 = symbolize
--  (match_ (seq_ [int_ 4, int_ 7])
--    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--          (pseqtot_ [pint_ 3, pvar_ "a"]))
--    (var_ "a")
--    (int_ 42)) in
--utest matchNestedOr4 with generateEmptyVariants matchNestedOr4 using sameSemantics in
--
--let matchNot1 = symbolize
--  (match_ (seq_ [int_ 1, int_ 2])
--    (pnot_ (pseqtot_ [pint_ 1, pvar_ "a"]))
--    true_
--    false_) in
--utest matchNot1 with generateEmptyVariants matchNot1 using sameSemantics in
--
--let matchNot2 = symbolize
--  (match_ (seq_ [int_ 2, int_ 2])
--    (pnot_ (pseqtot_ [pint_ 1, pvar_ "a"]))
--    true_
--    false_) in
--utest matchNot2 with generateEmptyVariants matchNot2 using sameSemantics in
--
--let matchAnd1 = symbolize
--  (match_ (seq_ [int_ 1, int_ 2])
--    (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pvar_ "b"))
--    (addi_ (var_ "a") (get_ (var_ "b") (int_ 1)))
--    (int_ 53)) in
--utest matchAnd1 with generateEmptyVariants matchAnd1 using sameSemantics in
--
--let matchAnd2 = symbolize
--  (match_ (seq_ [int_ 2, int_ 2])
--    (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pvar_ "b"))
--    (addi_ (var_ "a") (get_ (var_ "b") (int_ 1)))
--    (int_ 53)) in
--utest matchAnd2 with generateEmptyVariants matchAnd2 using sameSemantics in
--
--let matchAnd3 = symbolize
--  (match_ (seq_ [int_ 1, int_ 2])
--    (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ []))
--    (var_ "a")
--    (int_ 53)) in
--utest matchAnd3 with generateEmptyVariants matchAnd3 using sameSemantics in
--
--let matchAnd4 = symbolize
--  (match_ (seq_ [int_ 1, int_ 2])
--    (pand_ (pseqtot_ []) (pseqtot_ [pint_ 1, pvar_ "a"]))
--    (var_ "a")
--    (int_ 53)) in
--utest matchAnd4 with generateEmptyVariants matchAnd4 using sameSemantics in
--
--let matchSeqEdge1 = symbolize
--  (match_ (seq_ [int_ 1])
--    (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
--    (addi_ (var_ "a") (var_ "c"))
--    (int_ 75)) in
--utest matchSeqEdge1 with generateEmptyVariants matchSeqEdge1 using sameSemantics in
--
--let matchSeqEdge2 = symbolize
--  (match_ (seq_ [int_ 1, int_ 2])
--    (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
--    (addi_ (var_ "a") (var_ "c"))
--    (int_ 75)) in
--utest matchSeqEdge2 with generateEmptyVariants matchSeqEdge2 using sameSemantics in
--
--let matchSeqEdge3 = symbolize
--  (match_ (seq_ [int_ 1, int_ 2, int_ 3])
--    (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
--    (addi_ (var_ "a") (var_ "c"))
--    (int_ 75)) in
--utest matchSeqEdge3 with generateEmptyVariants matchSeqEdge3 using sameSemantics in
--
--let matchSeqEdge4 = symbolize
--  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
--    (pseqedge_ [pvar_ "a", pvar_ "d"] "b" [pvar_ "c"])
--    (addi_ (addi_ (var_ "d") (var_ "a")) (var_ "c"))
--    (int_ 75)) in
--utest matchSeqEdge4 with generateEmptyVariants matchSeqEdge4 using sameSemantics in
--
--let matchSeqEdge5 = symbolize
--  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
--    (por_ (pseqedge_ [pint_ 2] "b" []) (pseqedge_ [pint_ 1] "b" []))
--    (match_ (var_ "b")
--      (pseqedgew_ [pvar_ "a"] [pvar_ "c"])
--      (addi_ (var_ "a") (var_ "c"))
--      (int_ 84))
--    (int_ 75)) in
--utest matchSeqEdge5 with generateEmptyVariants matchSeqEdge5 using sameSemantics in
--
--let matchSeqEdge6 = symbolize
--  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
--    (por_ (pseqedge_ [pint_ 2] "b" []) (pseqedge_ [] "b" [pint_ 4]))
--    (match_ (var_ "b")
--      (pseqedgew_ [pvar_ "a"] [pvar_ "c"])
--      (addi_ (var_ "a") (var_ "c"))
--      (int_ 84))
--    (int_ 75)) in
--utest matchSeqEdge6 with generateEmptyVariants matchSeqEdge6 using sameSemantics in
--
--let matchSeqEdge7 = symbolize
--  (match_ (seq_ [int_ 1])
--    (pseqedgew_ [pvar_ "a"] [])
--    (var_ "a")
--    (int_ 75)) in
--utest matchSeqEdge7 with generateEmptyVariants matchSeqEdge7 using sameSemantics in

let intEither = nameSym "IntEither" in
let intEitherTy = ntyvar_ intEither in
let left = nameSym "Left" in
let right = nameSym "Right" in
let nested = nameSym "Nested" in
let eitherMatch = lam matchTerm.
  bindall_ [
    ntype_ intEither tyunknown_,
    ncondef_ left (tyarrow_ tyint_ intEitherTy),
    ncondef_ right (tyarrow_ tyint_ intEitherTy),
    ncondef_ nested (tyarrow_ intEitherTy intEitherTy),
    matchTerm
  ] in

let matchCon1 = symbolize (
  eitherMatch
    (match_ (nconapp_ left (int_ 7))
      (npcon_ left (pvar_ "n"))
      (withType tyint_ (var_ "n"))
      (int_ 0))) in
utest stripTypeDecls matchCon1 with generateTypeAnnotated matchCon1 using sameSemantics in

let matchCon2 = symbolize (
  eitherMatch
    (match_ (nconapp_ left (int_ 7))
      (npcon_ right (pvar_ "n"))
      (withType tyint_ (var_ "n"))
      (int_ 0))) in
utest stripTypeDecls matchCon2 with generateTypeAnnotated matchCon2 using sameSemantics in

let matchCon3 = symbolize (
  eitherMatch
    (match_ (nconapp_ left (int_ 7))
      (npcon_ left (pint_ 7))
      (int_ 1)
      (int_ 0))) in
utest stripTypeDecls matchCon3 with generateTypeAnnotated matchCon3 using sameSemantics in

let matchCon4 = symbolize (
  eitherMatch
    (match_ (nconapp_ left (int_ 7))
      (npcon_ right (pint_ 7))
      (int_ 1)
      (int_ 0))) in
utest stripTypeDecls matchCon4 with generateTypeAnnotated matchCon4 using sameSemantics in

let matchNestedCon1 = symbolize (
  eitherMatch
    (match_ (nconapp_ nested (nconapp_ left (int_ 7)))
      (npcon_ nested (pvar_ "n"))
      (int_ 1)
      (int_ 0))) in
utest stripTypeDecls matchNestedCon1 with generateTypeAnnotated matchNestedCon1
using sameSemantics in

let matchNestedCon2 = symbolize (
  eitherMatch
    (match_ (nconapp_ nested (nconapp_ left (int_ 7)))
      (npcon_ nested (npcon_ left (pvar_ "n")))
      (withType tyint_ (var_ "n"))
      (int_ 0))) in
utest stripTypeDecls matchNestedCon2 with generateTypeAnnotated matchNestedCon2
using sameSemantics in

let matchNestedCon3 = symbolize (
  eitherMatch
    (match_ (nconapp_ nested (nconapp_ left (int_ 7)))
      (npcon_ nested (npcon_ left (pint_ 7)))
      (int_ 1)
      (int_ 0))) in
utest stripTypeDecls matchNestedCon3 with generateTypeAnnotated matchNestedCon3
using sameSemantics in

let matchNestedCon4 = symbolize (
  eitherMatch
    (match_ (nconapp_ nested (nconapp_ left (int_ 7)))
      (npcon_ nested (pvar_ "n1"))
      (match_ (var_ "n1")
        (npcon_ left (pvar_ "n2"))
        (var_ "n2")
        (int_ 1))
      (int_ 2))) in
utest stripTypeDecls matchNestedCon4 with generateTypeAnnotated matchNestedCon4
using sameSemantics in

let matchNestedCon5 = symbolize (
  eitherMatch
    (match_ (nconapp_ nested (nconapp_ left (int_ 7)))
      (npcon_ nested (pvar_ "n1"))
      (match_ (var_ "n1")
        (npcon_ right (pvar_ "n2"))
        (var_ "n2")
        (int_ 1))
      (int_ 2))) in
utest stripTypeDecls matchNestedCon5 with generateTypeAnnotated matchNestedCon5
using sameSemantics in

-- Ints
let addInt1 = addi_ (int_ 1) (int_ 2) in
utest addInt1 with generateEmptyVariants addInt1 using sameSemantics in

let addInt2 = addi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest addInt2 with generateEmptyVariants addInt2 using sameSemantics in

let testMulInt = muli_ (int_ 2) (int_ 3) in
utest testMulInt with generateEmptyVariants testMulInt using sameSemantics in

let testModInt = modi_ (int_ 2) (int_ 3) in
utest testModInt with generateEmptyVariants testModInt using sameSemantics in

let testDivInt = divi_ (int_ 2) (int_ 3) in
utest testDivInt with generateEmptyVariants testDivInt using sameSemantics in

let testNegInt = addi_ (int_ 2) (negi_ (int_ 2)) in
utest testNegInt with generateEmptyVariants testNegInt using sameSemantics in

let compareInt1 = eqi_ (int_ 1) (int_ 2) in
utest compareInt1 with generateEmptyVariants compareInt1 using sameSemantics in

let compareInt2 = lti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt2 with generateEmptyVariants compareInt2 using sameSemantics in

let compareInt3 = leqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt3 with generateEmptyVariants compareInt3 using sameSemantics in

let compareInt4 = gti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt4 with generateEmptyVariants compareInt4 using sameSemantics in

let compareInt5 = geqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt5 with generateEmptyVariants compareInt5 using sameSemantics in

let compareInt6 = neqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt6 with generateEmptyVariants compareInt6 using sameSemantics in

let shiftInt1 = slli_ (int_ 5) (int_ 2) in
utest shiftInt1 with generateEmptyVariants shiftInt1 using sameSemantics in

let shiftInt2 = srli_ (int_ 5) (int_ 2) in
utest shiftInt2 with generateEmptyVariants shiftInt2 using sameSemantics in

let shiftInt3 = srai_ (int_ 5) (int_ 2) in
utest shiftInt3 with generateEmptyVariants shiftInt3 using sameSemantics in

-- Floats
let addFloat1 = addf_ (float_ 1.) (float_ 2.) in
utest addFloat1 with generateEmptyVariants addFloat1 using sameSemantics in

let addFloat2 = addf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest addFloat2 with generateEmptyVariants addFloat2 using sameSemantics in

let testMulFloat = mulf_ (float_ 2.) (float_ 3.) in
utest testMulFloat with generateEmptyVariants testMulFloat using sameSemantics in

let testDivFloat = divf_ (float_ 6.) (float_ 3.) in
utest testDivFloat with generateEmptyVariants testDivFloat using sameSemantics in

let testNegFloat = addf_ (float_ 2.) (negf_ (float_ 2.)) in
utest testNegFloat with generateEmptyVariants testNegFloat using sameSemantics in

let compareFloat1 = eqf_ (float_ 1.) (float_ 2.) in
utest compareFloat1 with generateEmptyVariants compareFloat1 using sameSemantics in

let compareFloat2 = ltf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat2 with generateEmptyVariants compareFloat2 using sameSemantics in

let compareFloat3 = leqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat3 with generateEmptyVariants compareFloat3 using sameSemantics in

let compareFloat4 = gtf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat4 with generateEmptyVariants compareFloat4 using sameSemantics in

let compareFloat5 = geqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat5 with generateEmptyVariants compareFloat5 using sameSemantics in

let compareFloat6 = neqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat6 with generateEmptyVariants compareFloat6 using sameSemantics in

-- Chars
let charLiteral = char_ 'c' in
utest charLiteral with generateEmptyVariants charLiteral
using sameSemantics in

-- Abstractions
let fun =
  symbolize
  (appSeq_
    (ulam_ "@" (ulam_ "%" (addi_ (var_ "@") (var_ "%"))))
    [int_ 1, int_ 2])
in
utest fun with generateEmptyVariants fun using sameSemantics in

let funShadowed =
  symbolize
  (appSeq_
    (ulam_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))))
    [ulam_ "@" (var_ "@"), int_ 2])
in
utest funShadowed with generateEmptyVariants funShadowed using sameSemantics in

-- Lets
let testLet =
  symbolize
  (bindall_ [ulet_ "^" (int_ 1), addi_ (var_ "^") (int_ 2)])
in
utest testLet with generateEmptyVariants testLet using sameSemantics in

let testLetShadowed =
  symbolize
  (bindall_ [ulet_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))),
             app_ (var_ "@") (int_ 1)])
in
utest testLetShadowed with generateEmptyVariants testLetShadowed
using sameSemantics in

let testLetRec =
  symbolize
  (bind_
     (ureclets_add "$" (ulam_ "%" (app_ (var_ "@") (int_ 1)))
     (ureclets_add "@" (ulam_ "" (var_ ""))
     reclets_empty))
   (app_ (var_ "$") (var_ "@")))
in
utest testLetRec with generateEmptyVariants testLetRec using sameSemantics in

-- Sequences
let testEmpty = symbolize (length_ (seq_ [])) in
utest testEmpty with generateEmptyVariants testEmpty using sameSemantics in

let nonEmpty = seq_ [int_ 1, int_ 2, int_ 3] in
let len = length_ nonEmpty in
let fst = get_ nonEmpty (int_ 0) in
let snd = get_ nonEmpty (int_ 1) in
let thrd = get_ nonEmpty (int_ 2) in
utest int_ 3 with generateEmptyVariants len using sameSemantics in
utest int_ 1 with generateEmptyVariants fst using sameSemantics in
utest int_ 2 with generateEmptyVariants snd using sameSemantics in
utest int_ 3 with generateEmptyVariants thrd using sameSemantics in

let testMake = create_ (int_ 2) (ulam_ "_" (int_ 0)) in
let len = length_ testMake in
let fst = get_ testMake (int_ 0) in
let lst = get_ testMake (int_ 1) in
utest int_ 2 with generateEmptyVariants len using sameSemantics in
utest int_ 0 with generateEmptyVariants fst using sameSemantics in
utest int_ 0 with generateEmptyVariants lst using sameSemantics in

let testSet = set_ (seq_ [int_ 1, int_ 2]) (int_ 0) (int_ 3) in
let len = length_ testSet in
let fst = get_ testSet (int_ 0) in
let snd = get_ testSet (int_ 1) in
utest int_ 2 with generateEmptyVariants len using sameSemantics in
utest int_ 3 with generateEmptyVariants fst using sameSemantics in
utest int_ 2 with generateEmptyVariants snd using sameSemantics in

let testCons = cons_  (int_ 1) (seq_ [int_ 2, int_ 3]) in
let len = length_ testCons in
let fst = get_ testCons (int_ 0) in
let snd = get_ testCons (int_ 1) in
let thrd = get_ testCons (int_ 2) in
utest int_ 3 with generateEmptyVariants len using sameSemantics in
utest int_ 1 with generateEmptyVariants fst using sameSemantics in
utest int_ 2 with generateEmptyVariants snd using sameSemantics in
utest int_ 3 with generateEmptyVariants thrd using sameSemantics in

let testSnoc = snoc_ (seq_ [int_ 1, int_ 2]) (int_ 3) in
let len = length_ testSnoc in
let fst = get_ testSnoc (int_ 0) in
let snd = get_ testSnoc (int_ 1) in
let thrd = get_ testSnoc (int_ 2) in
utest int_ 3 with generateEmptyVariants len using sameSemantics in
utest int_ 1 with generateEmptyVariants fst using sameSemantics in
utest int_ 2 with generateEmptyVariants snd using sameSemantics in
utest int_ 3 with generateEmptyVariants thrd using sameSemantics in

let testReverse = reverse_ (seq_ [int_ 1, int_ 2, int_ 3]) in
let len = length_ testReverse in
let fst = get_ testReverse (int_ 0) in
let snd = get_ testReverse (int_ 1) in
let thrd = get_ testReverse (int_ 2) in
utest int_ 3 with generateEmptyVariants len using sameSemantics in
utest int_ 3 with generateEmptyVariants fst using sameSemantics in
utest int_ 2 with generateEmptyVariants snd using sameSemantics in
utest int_ 1 with generateEmptyVariants thrd using sameSemantics in

-- TODO(Oscar Eriksson, 2020-11-16) Test splitAt when we have implemented tuple
-- projection.

-- TODO(Oscar Eriksson, 2020-11-30) Test symbol operations when we have
-- implemented tuples/records.

-- Float-Integer conversions
let testFloorfi = floorfi_ (float_ 1.5) in
utest testFloorfi with generateEmptyVariants testFloorfi using sameSemantics in

let testCeilfi = ceilfi_ (float_ 1.5) in
utest testCeilfi with generateEmptyVariants testCeilfi using sameSemantics in

let testRoundfi = roundfi_ (float_ 1.5) in
utest testRoundfi with generateEmptyVariants testRoundfi using sameSemantics in

let testInt2float = int2float_ (int_ 1) in
utest testInt2float with generateEmptyVariants testInt2float using sameSemantics in

-- TODO(Oscar Eriksson, 2020-12-7) We need to think about how we should compile strings.
-- let testString2float = string2float_ (str_ "1.5") in
-- utest testString2float with generate testString2float using sameSemantics in
let x = nameSym "x" in
let y = nameSym "y" in
let z = nameSym "z" in
/-
let test1 = bindall_ [
  nulet_ x unit_,
  int_ 0
] in
utest test1 with generate (generateDecl (typeAnnot test1)) using sameSemantics in

let test2 = bindall_ [
  nulet_ x (record_ [("a", record_ []), ("b", tuple_ [int_ 1, int_ 2])]),
  --nulet_ y (nrecordproj_ (nameNoSym "a") "a" (nvar_ x)),
  --nulet_ z (tupleproj_ 0 (nvar_ y)),
  int_ 0
] in
let t = generate (generateDecl (typeAnnot test2)) in
let _ = printLn (expr2str t) in

let expr = nameSym "Expr" in
let exprty = ntyvar_ expr in
let cint = nameSym "CInt" in
let tmconst = nameSym "TmConst" in
let pair = nameSym "Pair" in

let pat = npcon_ pair (pvar_ "t") in
let test3 = bindall_ [
  ntype_ expr tyunknown_,
  ncondef_ cint (tyarrow_ tyint_ exprty),
  ncondef_ tmconst (tyarrow_ (tyrecord_ [("val", exprty)]) exprty),
  ncondef_ pair (tyarrow_ (tyrecord_ [("lhs", exprty), ("rhs", exprty)]) exprty),
  nulet_ y (nconapp_ pair (record_ [
    ("lhs", nconapp_ cint (int_ 4)),
    ("rhs", nconapp_ tmconst (record_ [
      ("val", nconapp_ cint (int_ 2))
    ]))
  ])),
  match_ (nvar_ y) pat (int_ 1) (int_ 0)
] in
let t = generate (generateDecl (typeAnnot (symbolize test3))) in
let _x = printLn (expr2str t) in
-/

let pat = prec_ [("a", pvar_ "a")] in
let t = bindall_ [
  nulet_ x (record_ [("a", int_ 1), ("b", float_ 0.0)]),
  match_ (nvar_ x) pat (withType tyint_ (var_ "a")) (int_ 0)
] in
/-
let intopt = nameSym "IntResult" in
let intoptty = ntyvar_ intopt in
let ok = nameSym "Ok" in
let err = nameSym "Err" in
let pat = npcon_ ok (pvar_ "n") in
let t = bindall_ [
  ntype_ intopt tyunknown_,
  ncondef_ ok (tyarrow_ tyint_ intoptty),
  ncondef_ err (tyarrow_ tyunit_ intoptty),
  nulet_ x (nconapp_ ok (int_ 2)),
  match_ (nvar_ x) pat (withType tyint_ (var_ "n")) (int_ 0)
] in
-/
let #var"" =
  use MExprPrettyPrint in
  printLn (expr2str t)
in
printLn "==========" ;
let t = symbolize t in
let t = typeAnnot t in
match generateDecl t with (t, variants) then
  let t = generate variants t in
  let t = expr2str t in
  printLn t
else never
