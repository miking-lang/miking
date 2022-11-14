include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/builtin.mc"
include "mexpr/eq.mc"
include "mexpr/info.mc"
include "mexpr/parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/remove-ascription.mc"
include "mexpr/type-lift.mc"
include "mexpr/cmp.mc"
include "mexpr/type.mc"
include "ocaml/ast.mc"
include "ocaml/pprint.mc"
include "ocaml/compile.mc"
include "ocaml/intrinsics-ops.mc"
include "ocaml/generate-env.mc"
include "ocaml/external.mc"
include "common.mc"

-- Input is a map from name to be introduced to name containing the value to be bound to that location
-- Output is essentially `M.toList input & unzip & \(pats, exprs) -> (OPatTuple pats, TmTuple exprs)`
-- alternatively output is made such that if (_mkFinalPatExpr ... = (pat, expr)) then let 'pat = 'expr
-- (where ' splices things into expressions) binds the appropriate names to the appropriate values
-- INVARIANT: two semantically equal maps produce the same output, i.e., we preserve an equality that is stronger than structural
let _mkFinalPatExpr : AssocMap Name Name -> (Pat, Expr) = use OCamlAst in lam nameMap.
  let cmp = lam n1 : (Name, Name). lam n2 : (Name, Name).
    subi (sym2hash (optionGetOr _noSymbol (nameGetSym n1.0))) (sym2hash (optionGetOr _noSymbol (nameGetSym n2.0))) in
  match unzip (sort cmp (assoc2seq {eq=nameEqSym} nameMap)) with (patNames, exprNames) then
    (OPatTuple {pats = map npvar_ patNames}, OTmTuple {values = map nvar_ exprNames})
  else never

let _omatch_ = lam target. lam arms.
  use OCamlAst in
  match arms with [h] ++ rest
  then OTmMatch { target = target, arms = cons h (map (lam x: (Unknown, Unknown). (x.0, objMagic x.1)) rest) }
  else OTmMatch { target = target, arms = arms }

-- Construct a match expression that matches against an option
let _someName = "Option.Some"
let _noneName = "Option.None"
let _optMatch = use OCamlAst in lam target. lam somePat. lam someExpr. lam noneExpr.
  _omatch_ target
    [ (OPatConExt {ident = _someName, args = [somePat]}, someExpr)
    , (OPatConExt {ident = _noneName, args = []}, noneExpr)]
let _some = use OCamlAst in lam val. OTmConAppExt {ident = _someName, args = [val]}
let _none = use OCamlAst in OTmConAppExt {ident = _noneName, args = []}
let _if = use OCamlAst in lam cond. lam thn. lam els. _omatch_ cond [(ptrue_, thn), (pfalse_, els)]
let _tuplet = use OCamlAst in lam pats. lam val. lam body. _omatch_ val [(OPatTuple {pats = pats}, body)]

let _isLengthAtLeastName = intrinsicOpSeq "is_length_at_least"
let _isLengthAtLeast = use OCamlAst in
  appf2_ (OTmVarExt {ident = _isLengthAtLeastName})

let _builtinNameMap : Map String Name =
  let builtinStrs =
    match unzip builtin with (strs, _) then
      strs
    else never
  in
  mapFromSeq cmpString
    (map (lam s. (s, nameSym s))
      (concat
        builtinStrs
        [
          "ofArray"
        ]))

let _builtinNamesSet : Set Name =
  setOfSeq nameCmp
           (map (lam x : (String, Name). x.1)
           (mapBindings _builtinNameMap))

let _intrinsicName : String -> Name = lam str.
  match mapLookup str _builtinNameMap with Some name then
    name
  else error (join ["Unsupported intrinsic: ", str])

let lookupRecordFields = use MExprAst in
  lam ty. lam constrs.
  match ty with TyRecord {fields = fields} then
    Some fields
  else match ty with TyCon {ident = ident} then
    match mapLookup ident constrs with Some (TyRecord {fields = fields}) then
      Some fields
    else None ()
  else None ()

type MatchRecord = {target : Expr, pat : Pat, thn : Expr,
                    els : Expr, ty : Type, info : Info}

lang OCamlTopGenerate = MExprAst + OCamlAst + OCamlGenerateExternalNaive
  sem generateTops (env : GenerateEnv) =
  | t ->
    match generateTopsAndExpr env t with (tops, expr) then
      snoc tops (OTopExpr { expr = expr })
    else never

  sem generateTopsAndExpr (env : GenerateEnv) =
  | TmLet t ->
    let here = OTopLet { ident = t.ident, tyBody = t.tyBody, body = generate env t.body } in
    let later: ([Top], Expr) = generateTopsAndExpr env t.inexpr in
    (cons here later.0, later.1)
  | TmRecLets t ->
    let f = lam binding : RecLetBinding.
      { ident = binding.ident
      , tyBody = binding.tyBody
      , body = generate env binding.body
      } in
    let here = OTopRecLets { bindings = map f t.bindings } in
    let later: ([Top], Expr) = generateTopsAndExpr env t.inexpr in
    (cons here later.0, later.1)
  | TmExt t ->
    match convertExternalBody env t.ident t.tyIdent t.info with body in
    let here = OTopLet { ident = t.ident, tyBody = t.tyIdent, body = body } in
    let later : ([Top], Expr) = generateTopsAndExpr env t.inexpr in
    (cons here later.0, later.1)
  | t ->
    ([], generate env t)

  sem convertExternalBody (env : GenerateEnv) (ident : Name) (tyIdent : Type) =
  | info ->
    match mapLookup ident env.exts with Some r then
      let r : ExternalImpl = head r in
      match convertData info env (OTmExprExt { expr = r.expr }) (r.ty, tyIdent)
      with (_, body) in
      body
    else
      errorSingle [info] (join ["No implementation for external ", nameGetStr ident])

  sem generate (env : GenerateEnv) =
  -- Intentionally left blank
end

lang OCamlMatchGenerate = MExprAst + OCamlAst
  sem generateDefaultMatchCase (env : GenerateEnv) =
  | t ->
    let t : MatchRecord = t in
    let tname = nameSym "_target" in
    match generatePat env tname t.pat with (nameMap, wrap) then
      match _mkFinalPatExpr nameMap with (pat, expr) then
        _optMatch
          (objMagic
            (bind_ (nulet_ tname (generate env t.target))
                   (generate env (wrap (_some expr)))))
          pat
          (generate env t.thn)
          (generate env t.els)
      else never
    else never

  sem collectNestedMatches
    : all acc. GenerateEnv
            -> (Pat -> Bool)
            -> acc
            -> (acc -> MatchRecord -> acc)
            -> MatchRecord
            -> (acc, Expr)
  sem collectNestedMatches env isNestedPat acc addMatchCase =
  | t ->
    let t : MatchRecord = t in
    -- We assume that the target is a variable because otherwise there is no
    -- easy way to determine that the expressions are the same, as we don't
    -- have access to the outer scope where variables have been defined.
    let eqTarget =
      match t.target with TmVar {ident = ident} then
        lam t.
          match t with TmVar {ident = id} then
            nameEq ident id
          else false
      else never
    in
    recursive let collectMatchTerms = lam acc. lam t : MatchRecord.
      if eqTarget t.target then
        if isNestedPat t.pat then
          let acc = addMatchCase acc t in
          match t.els with TmMatch tm then
            collectMatchTerms acc tm
          else (acc, t.els)
        else (acc, TmMatch t)
      else (acc, TmMatch t)
    in
    collectMatchTerms acc t

  sem collectNestedMatchesByConstructor (env : GenerateEnv) =
  | t ->
    collectNestedMatches env
      (lam pat. match pat with PatCon _ then true else false)
      (mapEmpty nameCmp)
      (lam acc. lam t : MatchRecord.
         match t.pat with PatCon pc then
           match mapLookup pc.ident acc with Some pats then
             let pats = cons (pc.subpat, t.thn) pats in
             mapInsert pc.ident pats acc
           else
             mapInsert pc.ident [(pc.subpat, t.thn)] acc
         else never) t

  sem generate (env : GenerateEnv) =
  | TmMatch ({pat = (PatBool {val = true})} & t) ->
    _if (objMagic (generate env t.target)) (generate env t.thn) (generate env t.els)
  | TmMatch ({pat = (PatBool {val = false})} & t) ->
    _if (objMagic (generate env t.target)) (generate env t.els) (generate env t.thn)
  | TmMatch ({pat = PatInt _, target = TmVar _} & t) ->
    match
      collectNestedMatches env
        (lam pat. match pat with PatInt _ then true else false) []
        (lam acc. lam t : MatchRecord. snoc acc (t.pat, generate env t.thn)) t
    with (arms, defaultCase) then
      _omatch_ (generate env t.target)
        (snoc arms (pvarw_, generate env defaultCase))
    else never
  | TmMatch ({pat = PatInt _} & t) ->
    _omatch_ (generate env t.target)
      [(t.pat, generate env t.thn), (pvarw_, generate env t.els)]
  | TmMatch ({pat = PatChar {val = c}, target = TmVar _} & t) ->
    match
      collectNestedMatches env
        (lam pat. match pat with PatChar _ then true else false) []
        (lam acc. lam t : MatchRecord.
          match t.pat with PatChar pc then
            let pat =
              PatInt {val = char2int pc.val, info = pc.info, ty = pc.ty}
            in snoc acc (pat, generate env t.thn)
          else never) t
    with (arms, defaultCase) then
      _omatch_ (generate env t.target)
        (snoc arms (pvarw_, generate env defaultCase))
    else never
  | TmMatch ({pat = PatChar pc} & t) ->
    let pat = PatInt {val = char2int pc.val, info = pc.info, ty = pc.ty} in
    _omatch_ (generate env t.target)
      [(pat, generate env t.thn), (pvarw_, generate env t.els)]
  | TmMatch ({pat = PatNamed {ident = PWildcard _, ty = tyunknown_}} & t) ->
    generate env t.thn
  | TmMatch ({pat = PatNamed {ident = PName n}} & t) ->
    generate env (bind_
      (nulet_ n t.target)
       t.thn)
  | TmMatch ({pat = PatSeqTot {pats = []}} & t) ->
    let cond = generate env (null_ t.target) in
    _if cond (generate env t.thn) (generate env t.els)
  | TmMatch ({info = info, pat = PatRecord pr, thn = TmVar thnv, els = TmNever _} & t) ->
    let binds : [(SID, Pat)] = mapBindings pr.bindings in
    match binds with [(fieldLabel, PatNamed ({ident = PName patName} & p))] then
      if nameEq patName thnv.ident then
        let targetTy = typeUnwrapAlias env.aliases pr.ty in
        match lookupRecordFields targetTy env.constrs with Some fields then
          let fieldTypes = ocamlTypedFields fields in
          match mapLookup fieldTypes env.records with Some name then
            let pat = PatNamed p in
            let precord = OPatRecord {bindings = mapFromSeq cmpSID [(fieldLabel, pat)]} in
            _omatch_ (objMagic (generate env t.target))
              [(OPatCon {ident = name, args = [precord]}, objMagic (nvar_ patName))]
          else error "Record type not handled by type-lifting"
        else errorSingle [info] "Unknown record type"
      else generateDefaultMatchCase env t
    else generateDefaultMatchCase env t
  | TmMatch ({target = TmVar _, pat = PatCon pc, els = TmMatch em} & t) ->
    match collectNestedMatchesByConstructor env t with (arms, defaultCase) then
      -- Assign the term of the final else-branch to a variable so that we
      -- don't introduce unnecessary code duplication (the default case could
      -- be large).
      let defaultCaseName = nameSym "defaultCase" in
      let defaultCaseVal = ulam_ "" (generate env defaultCase) in
      let defaultCaseLet = nulet_ defaultCaseName defaultCaseVal in

      let toNestedMatch = lam target : Expr. lam patExpr : [(Pat, Expr)].
        assocSeqFold
          (lam acc. lam pat. lam thn. match_ target pat thn acc)
          (app_ (nvar_ defaultCaseName) uunit_)
          patExpr
      in
      let f = lam arm : (Name, [(Pat, Expr)]).
        match mapLookup arm.0 env.constrs with Some argTy then
          let patVarName = nameSym "x" in
          let target =
            match argTy with TyRecord _ then t.target
            else nvar_ patVarName
          in
          let isUnit = match argTy with TyRecord {fields = fields} then
            mapIsEmpty fields else false in
          let pat = if isUnit
            then OPatCon {ident = arm.0, args = []}-- TODO(vipa, 2021-05-12): this will break if there actually is an inner pattern that wants to look at the unit
            else OPatCon {ident = arm.0, args = [npvar_ patVarName]} in
          let innerPatternTerm = toNestedMatch (withType argTy (objMagic target)) arm.1 in
          (pat, generate env innerPatternTerm)
        else
          let msg = join [
            "Unknown constructor referenced in nested match expression: ",
            nameGetStr arm.0
          ] in
          errorSingle [t.info] msg
      in
      let flattenedMatch =
        _omatch_ (objMagic (generate env t.target))
          (snoc
              (map f (mapBindings arms))
              (pvarw_, (app_ (nvar_ defaultCaseName) uunit_)))
      in bind_ defaultCaseLet flattenedMatch
    else never
  | TmMatch t -> generateDefaultMatchCase env t

  sem generatePat (env : GenerateEnv) (targetName : Name) =
end

lang OCamlGenerate = MExprAst + OCamlAst + OCamlTopGenerate + OCamlMatchGenerate
  sem generate (env : GenerateEnv) =
  | TmSeq {tms = tms} ->
    -- NOTE(vipa, 2021-05-14): Assume that explicit Consts have the same type, since the program wouldn't typecheck otherwise
    let innerGenerate = lam tm.
      let tm = generate env tm in
      match tm with TmConst _ then tm
      else objMagic tm in
    app_
      (objMagic (OTmVarExt {ident = (intrinsicOpSeq "Helpers.of_array")}))
      (OTmArray {tms = map innerGenerate tms})
  | TmRecord t ->
    if mapIsEmpty t.bindings then TmRecord t
    else
      let ty = typeUnwrapAlias env.aliases t.ty in
      match ty with TyCon {ident = ident} then
        match mapLookup ident env.constrs with Some (TyRecord {fields = fields} & ty) then
          let fieldTypes = ocamlTypedFields fields in
          match mapLookup fieldTypes env.records with Some id then
            let bindings = mapMap (lam e. objRepr (generate env e)) t.bindings in
            OTmConApp {
              ident = id,
              args = [TmRecord {t with bindings = bindings}]
            }
          else never
        else errorSingle [infoTy ty] "env.constrs lookup failed"
      else errorSingle [infoTy ty] "expected TyCon"
  | TmRecordUpdate t ->
    let ty = typeUnwrapAlias env.aliases t.ty in
    match ty with TyCon {ident = ident} then
      match mapLookup ident env.constrs with Some (TyRecord {fields = fields}) then
        let fieldTypes = ocamlTypedFields fields in
        match mapLookup fieldTypes env.records with Some id then
          let rec = objMagic (generate env t.rec) in
          let key = sidToString t.key in
          let value = objRepr (generate env t.value) in
          let inlineRecordName = nameSym "rec" in
          _omatch_ rec
            [ ( OPatCon {ident = id, args = [npvar_ inlineRecordName]}
              , OTmConApp {ident = id, args =
                [ recordupdate_ (nvar_ inlineRecordName) key value ]
                }
              )
            ]
        else
          let msg = join ["No record type could be found in the environment. ",
                          "This was caused by an error in the type-lifting."] in
          errorSingle [t.info] msg
      else
        let msg = join ["Record update was annotated with an invalid type."] in
        errorSingle [t.info] msg
    else
      let msg = join ["Expected type to be a TyCon. ",
                      "This was caused by an error in the type-lifting."] in
      errorSingle [t.info] msg
  | TmConApp t ->
    -- TODO(vipa, 2021-05-11): can env.constrs contain a non-resolved alias? If so this breaks.
    match mapLookup t.ident env.constrs with Some (TyRecord {fields = fields}) then
      -- NOTE(vipa, 2021-05-11): Constructor that takes explicit record, it should be inlined
      if mapIsEmpty fields then
        -- NOTE(vipa, 2021-05-12): Unit record, the OCaml constructor takes 0 arguments
        let value = OTmConApp { ident = t.ident, args = [] } in
        match t.body with TmRecord _ then
          value
        else
          semi_ (generate env t.body) value
      else
        -- NOTE(vipa, 2021-05-12): Non-unit record, the OCaml constructor takes a record with 1 or more fields
        match t.body with TmRecord r then
          -- NOTE(vipa, 2021-05-11): We have an explicit record, use it directly
          OTmConApp {
            ident = t.ident,
            args = [TmRecord {r with bindings = mapMap (lam e. objRepr (generate env e)) r.bindings}]
          }
        else
          -- NOTE(vipa, 2021-05-11): Not an explicit record, pattern match and reconstruct it
          let fieldTypes = ocamlTypedFields fields in
          match mapLookup fieldTypes env.records with Some id then
            let inlineRecordName = nameSym "rec" in
            let fieldNames =
              mapMapWithKey (lam sid. lam. nameSym (sidToString sid)) fields
            in
            let fieldPatterns = mapMap (lam n. npvar_ n) fieldNames in
            let pat = OPatRecord {bindings = fieldPatterns} in
            let reconstructedRecord = TmRecord {
              bindings = mapMap (lam n. nvar_ n) fieldNames,
              ty = tyTm t.body,
              info = infoTm t.body
            } in
            _omatch_ (objMagic (generate env t.body))
              [ ( OPatCon {ident = id, args = [pat]}
                , OTmConApp {ident = t.ident, args = [reconstructedRecord]}
                )
              ]
        else
          let msg = join ["No record type could be found in the environment. ",
                          "This was caused by an error in the type-lifting."] in
          errorSingle [t.info] msg
    else
      -- NOTE(vipa, 2021-05-11): Argument is not an explicit record, it should be `repr`ed
      OTmConApp {
        ident = t.ident,
        args = [objRepr (generate env t.body)]
      }
  | TmApp (t & {lhs = lhs & !(TmApp _), rhs = rhs}) ->
  -- NOTE(vipa, 2021-05-17): Putting `magic` around the function in a
  -- function chain makes all the other types flexible, the arguments
  -- can be any type, and the result type can be any type, it's thus
  -- very economical
    TmApp {{t with lhs = objMagic (generate env lhs)}
              with rhs = generate env rhs}
  | TmNever t ->
    let msg = "Reached a never term, which should be impossible in a well-typed program." in
    TmApp {
      lhs = OTmVarExt {ident = "failwith"},
      rhs = OTmString {text = escapeString (infoErrorString t.info msg)},
      ty = t.ty,
      info = NoInfo ()
    }
  -- TmExt Generation
  | TmExt {ident = ident, tyIdent = tyIdent, inexpr = inexpr, info = info} ->
    match convertExternalBody env ident tyIdent info with body in
    let inexpr = generate env inexpr in
    TmLet {
      ident = ident,
      tyAnnot = tyIdent,
      tyBody = tyIdent,
      body = body,
      inexpr = inexpr,
      ty = TyUnknown {info = info},
      info = info
    }
  | t -> smap_Expr_Expr (generate env) t

  /- : Pat -> (AssocMap Name Name, Expr -> Expr) -/
  sem generatePat (env : GenerateEnv) (targetName : Name) =
  | PatNamed {ident = PWildcard _} ->
    (assocEmpty, identity)
  | PatNamed {ident = PName n} ->
    (assocInsert {eq=nameEqSym} n targetName assocEmpty, identity)
  | PatBool {val = val} ->
    let wrap = lam cont.
      _if (objMagic (nvar_ targetName))
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
      match generatePat env n pat with (names, innerWrap) in
      let wrap = lam cont.
        bind_
          (nulet_ n (get_ (nvar_ targetName) (int_ i)))
          (innerWrap cont)
      in (names, wrap) in
    match unzip (mapi genOne pats) with (allNames, allWraps) in
    let cond =
      if null pats then _if (null_ (nvar_ targetName))
      else _if (eqi_ (length_ (nvar_ targetName)) (int_ (length pats))) in
    let wrap = lam cont.
      cond
        (foldr (lam f. lam v. f v) cont allWraps)
        _none in
    ( foldl (assocMergePreferRight {eq=nameEqSym}) assocEmpty allNames
    , wrap
    )
  | PatSeqEdge {prefix = [head], middle = middle, postfix = []} ->
    let apply = lam f. lam x. f x in
    let headName = nameSym "_hd" in
    let tailName = nameSym "_tl" in
    match generatePat env headName head with (headNames, headWrap) in
    match middle with PName mid then
      let tl = PatNamed {ident = middle, info = NoInfo (), ty = tyunknown_} in
      match generatePat env tailName tl with (tailNames, tailWrap) in
      let wrap = lam cont.
        _if (null_ (nvar_ targetName))
          _none
          (bindall_ [
            nulet_ headName (head_ (nvar_ targetName)),
            nulet_ tailName (tail_ (nvar_ targetName)),
            headWrap (tailWrap cont)]) in
      (assocMergePreferRight {eq=nameEqSym} headNames tailNames, wrap)
    else
      let wrap = lam cont.
        _if (null_ (nvar_ targetName))
          _none
          (bind_ (nulet_ headName (head_ (nvar_ targetName))) (headWrap cont)) in
      (headNames, wrap)
  | PatSeqEdge {prefix = prefix, middle = middle, postfix = postfix} ->
    let apply = lam f. lam x. f x in
    let mergeNames = assocMergePreferRight {eq=nameEqSym} in
    let minLen = addi (length prefix) (length postfix) in
    let preName = nameSym "_prefix" in
    let tempName = nameSym "_splitTemp" in
    let midName = nameSym "_middle" in
    let postName = nameSym "_postfix" in
    let lenName = nameSym "_len" in
    let genOne = lam targetName. lam i. lam pat.
      let n = nameSym "_seqElem" in
      match generatePat env n pat with (names, innerWrap) in
      let wrap = lam cont.
        bind_
          (nlet_ n tyunknown_ (get_ (nvar_ targetName) (int_ i)))
          (innerWrap cont)
      in (names, wrap) in
    match
      match prefix with [] then (identity, [], targetName) else
      match unzip (mapi (genOne preName) prefix) with (preNames, preWraps) in
      let wrap = lam cont.
        _tuplet [npvar_ preName, npvar_ tempName]
          (splitat_ (nvar_ targetName) (int_ (length prefix)))
          (foldr apply cont preWraps) in
      (wrap, preNames, tempName)
    with (preWrap, preNames, tempName) in
    match
      match postfix with [] then (identity, [], tempName) else
      match unzip (mapi (genOne postName) postfix) with (postNames, postWraps) in
      let wrap = lam cont.
        _tuplet [npvar_ midName, npvar_ postName]
          (splitat_ (nvar_ tempName) (subi_ (nvar_ lenName) (int_ minLen)))
          (foldr apply cont postWraps) in
      (wrap, postNames, midName)
    with (postWrap, postNames, midName) in
    let wrap = lam cont.
      match postfix with [] then
        _if (_isLengthAtLeast (nvar_ targetName) (int_ minLen))
          (preWrap (postWrap cont))
          _none
      else
        bind_
          (nulet_ lenName (length_ (nvar_ targetName)))
          (_if (lti_ (nvar_ lenName) (int_ minLen))
            _none
            (preWrap (postWrap cont))) in
    let names = foldl mergeNames assocEmpty (concat preNames postNames) in
    let names = match middle with PName n then assocInsert {eq=nameEqSym} n midName names else names in
    (names, wrap)
  | PatOr {lpat = lpat, rpat = rpat} ->
    match generatePat env targetName lpat with (lnames, lwrap) then
      match generatePat env targetName rpat with (rnames, rwrap) then
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
    match generatePat env targetName lpat with (lnames, lwrap) then
      match generatePat env targetName rpat with (rnames, rwrap) then
        let names = assocMergePreferRight {eq=nameEqSym} lnames rnames in
        let wrap = lam cont. lwrap (rwrap cont) in
        (names, wrap)
      else never
    else never
  | PatNot {subpat = pat} ->
    match generatePat env targetName pat with (_, innerWrap) then
      let wrap = lam cont.
        _optMatch (innerWrap (_some (OTmTuple {values = []})))
          pvarw_
          _none
          cont in
      (assocEmpty, wrap)
    else never
  | PatRecord t ->
    let genBindingPat = lam patNames. lam fields. lam id. lam pat.
      let ty =
        match mapLookup id fields with Some ty then
          ty
        else
          let strFields = strJoin ", " (map sidToString (mapKeys fields)) in
          errorSingle [t.info] (join ["Field ", sidToString id, " not found in record with fields {", strFields, "}"])
      in
      match mapLookup id patNames with Some n then
        match generatePat env n pat with (names, innerWrap) then
          let wrap = lam cont. innerWrap cont in
          (names, wrap)
        else never
      else never
    in
    if mapIsEmpty t.bindings then
      let wrap = lam cont.
        _omatch_ (objMagic (nvar_ targetName))
          [(OPatTuple {pats = []}, cont)]
      in
      (assocEmpty, wrap)
    else match env with {records = records, constrs = constrs} then
      let targetTy = typeUnwrapAlias env.aliases t.ty in
      match lookupRecordFields targetTy constrs with Some fields then
        let fieldTypes = ocamlTypedFields fields in
        match mapLookup fieldTypes records with Some name then
          let patNames = mapMapWithKey (lam id. lam. nameSym (sidToString id)) t.bindings in
          let genPats = mapValues
            (mapMapWithKey (lam k. lam v. genBindingPat patNames fields k v) t.bindings)
          in
          match unzip genPats with (allNames, allWraps) then
            let f = lam id. lam.
              match mapLookup id patNames with Some n then
                npvar_ n
              else never
            in
            let precord = OPatRecord {bindings = mapMapWithKey f t.bindings} in
            let wrap = lam cont.
              _omatch_ (objMagic (nvar_ targetName))
                [ (OPatCon {ident = name, args = [precord]}, foldr (lam f. lam v. f v) cont allWraps)
                ]
            in
            ( foldl (assocMergePreferRight {eq=nameEqSym}) assocEmpty allNames
            , wrap
            )
          else never
        else
          let msg = join ["Pattern refers to record type that was not handled by type-lifting. ",
                          "This is an internal error."] in
          errorSingle [t.info] msg
      else
        let msg = join ["Pattern refers to an unknown record type. ",
                        "The target term must be annotated with a type."] in
        errorSingle [t.info] msg
    else never
  | PatCon t ->
    match env with {constrs = constrs} then
      match mapLookup t.ident constrs with Some innerTy then
        let conVarName = nameSym "_n" in
        let innerTargetName =
          -- Records are treated differently because we are not allowed to
          -- access an inlined record. Instead of returning the inlined record,
          -- the constructor containing it is returned. When we want to access
          -- the inlined record, the constructor will be treated as a record
          -- specific constructor. This works for both inlined records and
          -- free records, as they are wrapped in this record-specific
          -- constructor.
          match innerTy with TyRecord _ then
            targetName
          else conVarName
        in
        match generatePat env innerTargetName t.subpat with (names, subwrap) then
          let isUnit = match innerTy with TyRecord {fields = fields} then
            mapIsEmpty fields else false in
          let wrap = lam cont.
            _omatch_ (objMagic (nvar_ targetName))
              [ ( OPatCon
                  { ident = t.ident
                  , args = if isUnit then [] else [npvar_ conVarName] -- TODO(vipa, 2021-05-14): This will break if the sub-pattern actually examines the unit
                  }
                , subwrap cont
                ),
                (pvarw_, _none)
              ]
          in
          (names, wrap)
        else never
      else
        let msg = join ["Pattern refers to unknown type constructor: ",
                        nameGetStr t.ident,
                        ". The target term must be annotated with a type."] in
        errorSingle [t.info] msg
    else never
end

let _makeTypeDeclarations = lam typeLiftEnvMap. lam typeLiftEnv.
  use MExprAst in
  use OCamlTopAst in
  let f = lam acc. lam name. lam ty.
    match acc with (tops, recordFieldsToName) then
      match ty with TyRecord tr then
        let fieldTypes = ocamlTypedFields tr.fields in
        match mapLookup fieldTypes recordFieldsToName with Some _ then
          (tops, recordFieldsToName)
        else
          let recordFieldsToName = mapInsert fieldTypes name recordFieldsToName in
          let recordTy = TyRecord {tr with fields = fieldTypes} in
          let decl = OTopVariantTypeDecl {
            ident = nameSym "record",
            constrs = mapInsert name recordTy (mapEmpty nameCmp)
          } in
          (snoc tops decl, recordFieldsToName)
      else match ty with TyVariant {constrs = constrs} then
        let fixConstrType = lam ty.
          let ty = typeUnwrapAlias typeLiftEnvMap ty in
          match ty with TyRecord tr then
            TyRecord {tr with fields = ocamlTypedFields tr.fields}
          else tyunknown_ in
        let constrs = mapMap fixConstrType constrs in
        if mapIsEmpty constrs then (tops, recordFieldsToName)
        else
          let decl = OTopVariantTypeDecl {
            ident = name,
            constrs = constrs
          } in
          (snoc tops decl, recordFieldsToName)
      else (tops, recordFieldsToName)
    else never
  in
  let init = use MExprCmp in ([], mapEmpty (mapCmp cmpType)) in
  assocSeqFold f init typeLiftEnv

let _typeLiftEnvToGenerateEnv = use MExprAst in
  lam typeLiftEnvMap. lam typeLiftEnv. lam recordFieldsToName.
  let f = lam env : GenerateEnv. lam name. lam ty.
    match ty with TyRecord {fields = fields} then
      let fieldTypes = ocamlTypedFields fields in
      match mapLookup fieldTypes recordFieldsToName with Some id then
        {{env with records = mapInsert fieldTypes id env.records}
              with constrs = mapInsert name ty env.constrs}
      else error "Type lifting error"
    else match ty with TyVariant {constrs = constrs} then
      let constrs = mapMap (typeUnwrapAlias typeLiftEnvMap) constrs in
      {env with constrs = mapUnion env.constrs constrs}
    else
      {env with aliases = mapInsert name ty env.aliases}
  in
  assocSeqFold f emptyGenerateEnv typeLiftEnv


lang OCamlTypeDeclGenerate = MExprTypeLift
  sem generateTypeDecls =
  | env ->
    let env : AssocSeq Name Type = env in
    let typeLiftEnvMap = mapFromSeq nameCmp env in
    let topDecls = _makeTypeDeclarations typeLiftEnvMap env in
    match topDecls with (tops, recordFieldsToName) in
      let generateEnv = _typeLiftEnvToGenerateEnv typeLiftEnvMap
                                                  env recordFieldsToName in
      (generateEnv, tops)
end
