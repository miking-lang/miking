include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/builtin.mc"
include "mexpr/eq.mc"
include "mexpr/eval.mc"
include "mexpr/info.mc"
include "mexpr/parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/type-lift.mc"
include "mexpr/cmp.mc"
include "ocaml/ast.mc"
include "ocaml/pprint.mc"
include "ocaml/compile.mc"
include "ocaml/intrinsics-ops.mc"
include "common.mc"
include "external.mc"

type GenerateEnv = {
  constrs : Map Name Type,
  records : Map (Map SID Type) Name,
  aliases : Map Name Type
}

let _emptyGenerateEnv = use MExprCmp in {
  constrs = mapEmpty nameCmp,
  records = mapEmpty (mapCmp cmpType),
  aliases = mapEmpty nameCmp
}

-- Input is a map from name to be introduced to name containing the value to be bound to that location
-- Output is essentially `M.toList input & unzip & \(pats, exprs) -> (OPatTuple pats, TmTuple exprs)`
-- alternatively output is made such that if (_mkFinalPatExpr ... = (pat, expr)) then let 'pat = 'expr
-- (where ' splices things into expressions) binds the appropriate names to the appropriate values
-- INVARIANT: two semantically equal maps produce the same output, i.e., we preserve an equality that is stronger than structural
let _mkFinalPatExpr : AssocMap Name Name -> (Pat, Expr) = use OCamlAst in lam nameMap.
  let cmp = lam n1 : (Name, Name). lam n2 : (Name, Name).
    subi (sym2hash (optionGetOr (negi 1) (nameGetSym n1.0))) (sym2hash (optionGetOr (negi 1) (nameGetSym n2.0))) in
  match unzip (sort cmp (assoc2seq {eq=nameEqSym} nameMap)) with (patNames, exprNames) then
    (OPatTuple {pats = map npvar_ patNames}, OTmTuple {values = map nvar_ exprNames})
  else never

let _objRepr = use OCamlAst in
  lam t. app_ (OTmVarExt {ident = "Obj.repr"}) t
let _objMagic = use OCamlAst in
  lam t. app_ (OTmVarExt {ident = "Obj.magic"}) t

let _omatch_ = lam target. lam arms.
  use OCamlAst in
  match arms with [h] ++ rest
  then OTmMatch { target = target, arms = cons h (map (lam x: (Unknown, Unknown). (x.0, _objMagic x.1)) rest) }
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

let _builtinNameMap : Map String Name =
  let builtinStrs =
    match unzip builtin with (strs, _) then
      strs
    else never
  in
  mapFromList cmpString
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

recursive let unwrapAlias = use MExprAst in
  lam aliases. lam ty.
  match ty with TyVar {ident = ident} then
    match mapLookup ident aliases with Some ty then
      unwrapAlias aliases ty
    else ty
  else ty
end

let toOCamlType = use MExprAst in
  lam ty : Type.
  recursive let work = lam nested : Bool. lam ty : Type.
    match ty with TyRecord t then
      if or (mapIsEmpty t.fields) nested then tyunknown_
      else TyRecord {t with fields = mapMap (work true) t.fields}
    else tyunknown_
  in work false ty

let ocamlTypedFields = lam fields : Map SID Type.
  mapMap toOCamlType fields

let lookupRecordFields = use MExprAst in
  lam ty. lam constrs.
  match ty with TyRecord {fields = fields} then
    Some fields
  else match ty with TyVar {ident = ident} then
    match mapLookup ident constrs with Some (TyRecord {fields = fields}) then
      Some fields
    else None ()
  else None ()

type MatchRecord = {target : Expr, pat : Pat, thn : Expr,
                    els : Expr, ty : Type, info : Info}

lang OCamlMatchGenerate = MExprAst + OCamlAst
  sem matchTargetType (env : GenerateEnv) =
  | t ->
    let t : MatchRecord = t in
    let ty = ty t.target in
    -- If we don't know the type of the target and the pattern describes a
    -- tuple, then we assume the target has that type. We do this to
    -- eliminate the need to add type annotations when matching on tuples,
    -- which happens frequently.
    match ty with TyUnknown _ then
      match t.pat with PatRecord {bindings = bindings} then
        if mapIsEmpty bindings then ty else
        match _record2tuple bindings with Some _ then
          let bindingTypes = mapMap (lam. tyunknown_) bindings in
          match mapLookup bindingTypes env.records with Some id then
            ntyvar_ id
          else
            let msg = join [
              "Pattern specifies undefined tuple type.\n",
              "This was caused by an error in type-lifting."
            ] in
            infoErrorExit t.info msg
        else ty
      else ty
    else ty

  sem generateDefaultMatchCase (env : GenerateEnv) =
  | t ->
    let t : MatchRecord = t in
    let tname = nameSym "_target" in
    let targetTy = matchTargetType env t in
    match generatePat env targetTy tname t.pat with (nameMap, wrap) then
      match _mkFinalPatExpr nameMap with (pat, expr) then
        _optMatch
          (_objMagic
            (bind_ (nulet_ tname (generate env t.target))
                   (generate env (wrap (_some expr)))))
          pat
          (generate env t.thn)
          (generate env t.els)
      else never
    else never

  sem collectNestedMatchesByConstructor (env : GenerateEnv) =
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
        match t.pat with PatCon pc then
          let acc =
            match mapLookup pc.ident acc with Some pats then
              let pats = cons (pc.subpat, t.thn) pats in
              mapInsert pc.ident pats acc
            else
              mapInsert pc.ident [(pc.subpat, t.thn)] acc
          in
          match t.els with TmMatch tm then
            collectMatchTerms acc tm
          else Some (acc, t.els)
        else None ()
      else None ()
    in
    collectMatchTerms (mapEmpty nameCmp) t

  sem generate (env : GenerateEnv) =
  | TmMatch ({pat = (PatBool {val = true})} & t) ->
    _if (_objMagic (generate env t.target)) (generate env t.thn) (generate env t.els)
  | TmMatch ({pat = (PatBool {val = false})} & t) ->
    _if (_objMagic (generate env t.target)) (generate env t.els) (generate env t.thn)
  | TmMatch ({pat = PatInt {val = i}} & t) ->
    let cond = generate env (eqi_ (int_ i) t.target) in
    _if (_objMagic cond) (generate env t.thn) (generate env t.els)
  | TmMatch ({pat = PatChar {val = c}} & t) ->
    let cond = generate env (eqc_ (char_ c) t.target) in
    _if cond (generate env t.thn) (generate env t.els)
  | TmMatch ({pat = PatNamed {ident = PWildcard _}} & t) ->
    generate env t.thn
  | TmMatch ({pat = PatNamed {ident = PName n}} & t) ->
    generate env (bind_
      (nulet_ n t.target)
       t.thn)
  | TmMatch ({pat = PatSeqTot {pats = []}} & t) ->
    let cond = generate env (eqi_ (int_ 0) (length_ t.target)) in
    _if cond (generate env t.thn) (generate env t.els)
  | TmMatch ({info = info, pat = PatRecord pr, thn = TmVar thnv, els = TmNever _} & t) ->
    let binds : [(SID, Pat)] = mapBindings pr.bindings in
    match binds with [(fieldLabel, PatNamed ({ident = PName patName} & p))] then
      if nameEq patName thnv.ident then
        let targetTy = unwrapAlias env.aliases (matchTargetType env t) in
        match lookupRecordFields targetTy env.constrs with Some fields then
          let fieldTypes = ocamlTypedFields fields in
          match mapLookup fieldTypes env.records with Some name then
            let pat = PatNamed p in
            let precord = OPatRecord {bindings = mapFromList cmpSID [(fieldLabel, pat)]} in
            _omatch_ (_objMagic (generate env t.target))
              [(OPatCon {ident = name, args = [precord]}, nvar_ patName)]
          else error "Record type not handled by type-lifting"
        else error (infoErrorString info "Unknown record type")
      else generateDefaultMatchCase env t
    else generateDefaultMatchCase env t
  | TmMatch ({target = TmVar _, pat = PatCon pc, els = TmMatch em} & t) ->
    match collectNestedMatchesByConstructor env t with Some matches then
      match matches with (arms, defaultCase) then
        -- Assign the term of the final else-branch to a variable so that we
        -- don't introduce unnecessary code duplication (the default case could
        -- be large).
        let defaultCaseName = nameSym "defaultCase" in
        let defaultCaseVal = ulam_ "" (generate env defaultCase) in
        let defaultCaseLet = nulet_ defaultCaseName defaultCaseVal in

        let toNestedMatch = lam target : Expr. lam patExpr : [(Pat, Expr)].
          assocSeqFold
            (lam acc. lam pat. lam thn. match_ target pat thn acc)
            (app_ (nvar_ defaultCaseName) unit_)
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
            let innerPatternTerm = toNestedMatch (withType argTy (_objMagic target)) arm.1 in
            (pat, generate env innerPatternTerm)
          else
            let msg = join [
              "Unknown constructor referenced in nested match expression: ",
              nameGetStr arm.0
            ] in
            infoErrorExit t.info msg
        in
        let flattenedMatch =
          _omatch_ (_objMagic (generate env t.target))
            (snoc
                (map f (mapBindings arms))
                (pvarw_, (app_ (nvar_ defaultCaseName) unit_)))
        in bind_ defaultCaseLet flattenedMatch
      else never
    else generateDefaultMatchCase env t
  | TmMatch t -> generateDefaultMatchCase env t

  sem generatePat (env : GenerateEnv) (targetTy : Type) (targetName : Name) =
end

lang OCamlGenerate = MExprAst + OCamlAst + OCamlMatchGenerate
  sem generate (env : GenerateEnv) =
  | TmSeq {tms = tms} ->
    -- NOTE(vipa, 2021-05-14): Assume that explicit Consts have the same type, since the program wouldn't typecheck otherwise
    let innerGenerate = lam tm.
      let tm = generate env tm in
      match tm with TmConst _ then tm
      else _objMagic tm in
    app_
      (_objMagic (OTmVarExt {ident = (intrinsicOpSeq "Helpers.of_array")}))
      (OTmArray {tms = map innerGenerate tms})
  | TmRecord t ->
    if mapIsEmpty t.bindings then TmRecord t
    else
      let ty = unwrapAlias env.aliases t.ty in
      match ty with TyVar {ident = ident} then
        match mapLookup ident env.constrs with Some (TyRecord {fields = fields}) then
          let fieldTypes = ocamlTypedFields fields in
          match mapLookup fieldTypes env.records with Some id then
            let bindings = mapMap (lam e. _objRepr (generate env e)) t.bindings in
            OTmConApp {
              ident = id,
              args = [TmRecord {t with bindings = bindings}]
            }
          else never
        else never
      else never
  | TmRecordUpdate t ->
    let ty = unwrapAlias env.aliases t.ty in
    match ty with TyVar {ident = ident} then
      match mapLookup ident env.constrs with Some (TyRecord {fields = fields}) then
        let fieldTypes = ocamlTypedFields fields in
        match mapLookup fieldTypes env.records with Some id then
          let rec = generate env t.rec in
          let key = sidToString t.key in
          let value = _objRepr (generate env t.value) in
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
          infoErrorExit t.info msg
      else
        let msg = join ["Record update was annotated with an invalid type."] in
        infoErrorExit t.info msg
    else
      let msg = join ["Expected type to be a TyVar. ",
                      "This was caused by an error in the type-lifting."] in
      infoErrorExit t.info msg
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
            args = [TmRecord {r with bindings = mapMap (lam e. _objRepr (generate env e)) r.bindings}]
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
              ty = ty t.body,
              info = infoTm t.body
            } in
            _omatch_ (_objMagic (generate env t.body))
              [ ( OPatCon {ident = id, args = [pat]}
                , OTmConApp {ident = t.ident, args = [reconstructedRecord]}
                )
              ]
        else
          let msg = join ["No record type could be found in the environment. ",
                          "This was caused by an error in the type-lifting."] in
          infoErrorExit t.info msg
    else
      -- NOTE(vipa, 2021-05-11): Argument is not an explicit record, it should be `repr`ed
      OTmConApp {
        ident = t.ident,
        args = [_objRepr (generate env t.body)]
      }
  | TmApp (t & {lhs = lhs & !(TmApp _), rhs = rhs}) ->
  -- NOTE(vipa, 2021-05-17): Putting `magic` around the function in a
  -- function chain makes all the other types flexible, the arguments
  -- can be any type, and the result type can be any type, it's thus
  -- very economical
    TmApp {{t with lhs = _objMagic (generate env lhs)}
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
  | TmExt _ ->
    error "externals expected to be generated in a previous step"
  | t -> smap_Expr_Expr (generate env) t

  /- : Pat -> (AssocMap Name Name, Expr -> Expr) -/
  sem generatePat (env : GenerateEnv) (targetTy : Type) (targetName : Name) =
  | PatNamed {ident = PWildcard _} ->
    (assocEmpty, identity)
  | PatNamed {ident = PName n} ->
    (assocInsert {eq=nameEqSym} n targetName assocEmpty, identity)
  | PatBool {val = val} ->
    let wrap = lam cont.
      _if (_objMagic (nvar_ targetName))
        (if val then cont else _none)
        (if val then _none else cont)
    in (assocEmpty, wrap)
  | PatInt {val = val} ->
    (assocEmpty, lam cont. _if (eqi_ (nvar_ targetName) (int_ val)) cont _none)
  | PatChar {val = val} ->
    (assocEmpty, lam cont. _if (eqc_ (nvar_ targetName) (char_ val)) cont _none)
  | PatSeqTot {pats = pats} ->
    let elemTy =
      match targetTy with TySeq {ty = elemTy} then
        elemTy
      else tyunknown_
    in
    let genOne = lam i. lam pat.
      let n = nameSym "_seqElem" in
      match generatePat env elemTy n pat with (names, innerWrap) then
        let wrap = lam cont.
          bind_
            (nlet_ n tyunknown_ (get_ (nvar_ targetName) (int_ i)))
            (innerWrap cont)
        in (names, wrap)
      else never in
    match unzip (mapi genOne pats) with (allNames, allWraps) then
      let wrap = lam cont.
        _if (eqi_ (length_ (nvar_ targetName)) (int_ (length pats)))
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
    let elemTy =
      match targetTy with TySeq {ty = elemTy} then
        elemTy
      else tyunknown_
    in
    let genOne = lam targetName. lam i. lam pat.
      let n = nameSym "_seqElem" in
      match generatePat env elemTy n pat with (names, innerWrap) then
        let wrap = lam cont.
          bind_
            (nlet_ n tyunknown_ (get_ (nvar_ targetName) (int_ i)))
            (innerWrap cont)
        in (names, wrap)
      else never in
    match unzip (mapi (genOne preName) prefix) with (preNames, preWraps) then
      match unzip (mapi (genOne postName) postfix) with (postNames, postWraps) then
        let names = foldl mergeNames assocEmpty (concat preNames postNames) in
        let names = match middle with PName n then assocInsert {eq=nameEqSym} n midName names else names in
        let wrap = lam cont.
          _if (lti_ (length_ (nvar_ targetName)) (int_ minLen))
            _none
            (_tuplet [npvar_ preName, npvar_ tempName]
              (splitat_ (nvar_ targetName) (int_ (length prefix)))
              (_tuplet [npvar_ midName, npvar_ postName]
                (splitat_ (nvar_ tempName) (subi_ (length_ (nvar_ tempName)) (int_ (length postfix))))
                (foldr apply (foldr apply cont postWraps) preWraps))) in
        (names, wrap)
      else never
    else never
  | PatOr {lpat = lpat, rpat = rpat} ->
    match generatePat env targetTy targetName lpat with (lnames, lwrap) then
      match generatePat env targetTy targetName rpat with (rnames, rwrap) then
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
    match generatePat env targetTy targetName lpat with (lnames, lwrap) then
      match generatePat env targetTy targetName rpat with (rnames, rwrap) then
        let names = assocMergePreferRight {eq=nameEqSym} lnames rnames in
        let wrap = lam cont. lwrap (rwrap cont) in
        (names, wrap)
      else never
    else never
  | PatNot {subpat = pat} ->
    match generatePat env targetTy targetName pat with (_, innerWrap) then
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
          infoErrorExit t.info
            (join ["Field ", sidToString id, " not found in record with fields {", strFields, "}"])
      in
      match mapLookup id patNames with Some n then
        match generatePat env ty n pat with (names, innerWrap) then
          let wrap = lam cont. innerWrap cont in
          (names, wrap)
        else never
      else never
    in
    if mapIsEmpty t.bindings then
      let wrap = lam cont.
        _omatch_ (_objMagic (nvar_ targetName))
          [(OPatTuple {pats = []}, cont)]
      in
      (assocEmpty, wrap)
    else match env with {records = records, constrs = constrs} then
      let targetTy = unwrapAlias env.aliases targetTy in
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
              _omatch_ (_objMagic (nvar_ targetName))
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
          infoErrorExit t.info msg
      else
        let msg = join ["Pattern refers to an unknown record type. ",
                        "The target term must be annotated with a type."] in
        infoErrorExit t.info msg
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
        match generatePat env innerTy innerTargetName t.subpat with (names, subwrap) then
          let isUnit = match innerTy with TyRecord {fields = fields} then
            mapIsEmpty fields else false in
          let wrap = lam cont.
            _omatch_ (_objMagic (nvar_ targetName))
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
        infoErrorExit t.info msg
    else never
end

let _addTypeDeclarations = lam typeLiftEnvMap. lam typeLiftEnv. lam t.
  use MExprAst in
  use OCamlTypeDeclAst in
  let f = lam acc. lam name. lam ty.
    match acc with (t, recordFieldsToName) then
      match ty with TyRecord tr then
        let fieldTypes = ocamlTypedFields tr.fields in
        match mapLookup fieldTypes recordFieldsToName with Some _ then
          (t, recordFieldsToName)
        else
          let recordFieldsToName = mapInsert fieldTypes name recordFieldsToName in
          let recordTy = TyRecord {tr with fields = fieldTypes} in
          (OTmVariantTypeDecl {
            ident = nameSym "record",
            constrs = mapInsert name recordTy (mapEmpty nameCmp),
            inexpr = t
          }, recordFieldsToName)
      else match ty with TyVariant {constrs = constrs} then
        let constrs = mapMap (unwrapAlias typeLiftEnvMap) constrs in
        if mapIsEmpty constrs then (t, recordFieldsToName)
        else
          (OTmVariantTypeDecl {
            ident = name,
            constrs = constrs,
            inexpr = t
          }, recordFieldsToName)
      else (t, recordFieldsToName)
    else never
  in
  let init = use MExprCmp in (t, mapEmpty (mapCmp cmpType)) in
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
      let constrs = mapMap (unwrapAlias typeLiftEnvMap) constrs in
      {env with constrs = mapUnion env.constrs constrs}
    else
      {env with aliases = mapInsert name ty env.aliases}
  in
  assocSeqFold f _emptyGenerateEnv typeLiftEnv


lang OCamlTypeDeclGenerate = MExprTypeLift
  sem generateTypeDecl (env : AssocSeq Name Type) =
  | expr ->
    let typeLiftEnvMap = mapFromList nameCmp env in
    let exprDecls = _addTypeDeclarations typeLiftEnvMap env expr in
    match exprDecls with (expr, recordFieldsToName) then
      let generateEnv = _typeLiftEnvToGenerateEnv typeLiftEnvMap
                                                  env recordFieldsToName in
      (generateEnv, expr)
    else never
end

recursive let _isIntrinsicApp = use OCamlAst in
  lam t.
    match t with TmApp {lhs = TmConst _} then
      true
    else match t with TmApp {lhs = TmVar {ident = ident}} then
      setMem ident _builtinNamesSet
    else match t with TmApp {lhs = (TmApp _) & lhs} then
      _isIntrinsicApp lhs
    else false
end

lang OCamlTest = OCamlGenerate + OCamlTypeDeclGenerate + OCamlPrettyPrint +
                 MExprSym + ConstEq + IntEq + BoolEq + CharEq + FloatEq +
                 MExprTypeAnnot + OCamlGenerateExternalNaive

mexpr

use OCamlTest in

-- Test semantics

-- Parse helper
let parseAsMExpr = lam s.
  use MExprParser in parseExpr (initPos "") s
in

-- Evaluates OCaml expressions [strConvert] given as string, applied
-- to [p], and parses it as a mexpr expression.
let ocamlEval = lam ast.
  let compileOptions = {defaultCompileOptions with optimize = false} in
  let prog = ocamlCompileWithConfig compileOptions (expr2str ast) in
  let res = prog.run "" [] in
  let out = res.stdout in
  (if neqi res.returncode 0 then printLn ""; printLn res.stderr else ());
  prog.cleanup ();
  parseAsMExpr out
in

-- Determines whether two given floating-point numbers are equal within a given
-- epsilon.
let eqFloat = lam f1. lam f2. lam eps.
  let d = absf (subf f1 f2) in
  leqf d eps
in

-- Wraps the OCaml AST in a print term, but makes sure to place it after all
-- type declarations as that would result in a type errror.
recursive let wrapOCamlAstInPrint = lam ast. lam printTerm.
  use OCamlAst in
  match ast with OTmVariantTypeDecl t then
    OTmVariantTypeDecl {t with inexpr = wrapOCamlAstInPrint t.inexpr printTerm}
  else app_ printTerm (_objMagic ast)
in

let printf = lam fmt.
  TmApp {
    lhs = OTmVarExt {ident = "Printf.printf"},
    rhs = OTmString {text = fmt},
    info = NoInfo (),
    ty = tyunknown_
  }
in

let ocamlEvalInt = lam ast.
  ocamlEval (wrapOCamlAstInPrint ast (printf "%d"))
in

let ocamlEvalFloat = lam ast.
  ocamlEval (wrapOCamlAstInPrint ast (printf "%f"))
in

let ocamlEvalBool = lam ast.
  ocamlEval (wrapOCamlAstInPrint ast (printf "%b"))
in

let ocamlEvalChar = lam ast.
  match ocamlEvalInt ast with TmConst (t & {val = CInt n}) then
    TmConst {t with val = CChar {val = int2char n.val}}
  else never
in

utest ocamlEvalInt (int_ 1) with int_ 1 using eqExpr in
utest ocamlEvalFloat (float_ 1.) with float_ 1. using eqExpr in
utest ocamlEvalBool true_ with true_ using eqExpr in
utest ocamlEvalChar (char_ '1') with char_ '1' using eqExpr in

-- Compares evaluation of [mexprAst] as a mexpr and evaluation of
-- [ocamlAst] as a OCaml expression.
let sameSemantics = lam mexprAst. lam ocamlAst.
  let mexprVal =
    use MExprEval in
    eval {env = mapEmpty nameCmp} mexprAst
  in
  match mexprVal with TmConst t then
    match t.val with CInt _ then
      let ocamlVal = ocamlEvalInt ocamlAst in
      match ocamlVal with TmConst {val = CInt _} then
        eqExpr mexprVal ocamlVal
      else error "Values mismatch"
    else match t.val with CFloat {val = f1} then
      let ocamlVal = ocamlEvalFloat ocamlAst in
      match ocamlVal with TmConst {val = CFloat {val = f2}} then
        eqFloat f1 f2 1e-6
      else error "Values mismatch"
    else match t.val with CBool _ then
      let ocamlVal = ocamlEvalBool ocamlAst in
      match ocamlVal with TmConst {val = CBool _} then
        eqExpr mexprVal ocamlVal
      else error "Value mismatch"
    else match t.val with CChar _ then
      let ocamlVal = ocamlEvalChar ocamlAst in
      match ocamlVal with TmConst {val = CChar _} then
        eqExpr mexprVal ocamlVal
      else error "Value mismatch"
    else error "Unsupported constant"
  else dprint mexprVal; error "Unsupported value"
in

let generateEmptyEnv = lam t.
  generate _emptyGenerateEnv t
in

let generateTypeAnnotated = lam t.
  match typeLift (typeAnnot t) with (env, t) then
    match generateTypeDecl env t with (env, t) then
      generate env t
    else never
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
let matchWild1 = symbolize
  (match_ (int_ 1)
     pvarw_
     true_
     false_) in
utest matchWild1 with generateEmptyEnv matchWild1 using sameSemantics in

let matchWild2 = symbolize
  (match_ (int_ 1)
     (pvar_ "n")
     (var_ "n")
     (int_ 2)) in
utest matchWild2 with generateEmptyEnv matchWild2 using sameSemantics in

let matchChar1 = symbolize
 (match_ (char_ 'a')
   (pchar_ 'a')
   true_
   false_) in
utest matchChar1 with generateEmptyEnv matchChar1 using sameSemantics in

let matchChar2 = symbolize
  (match_ (char_ 'a')
    (pchar_ 'b')
    true_
    false_) in
utest matchChar2 with generateEmptyEnv matchChar2 using sameSemantics in

let matchSeq = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3])
    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
    (addi_ (var_ "a") (var_ "b"))
    (int_ 42)) in
utest matchSeq with generateEmptyEnv matchSeq using sameSemantics in

let noMatchSeq1 = symbolize
  (match_ (seq_ [int_ 2, int_ 2, int_ 3])
    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
    (addi_ (var_ "a") (var_ "b"))
    (int_ 42)) in
utest noMatchSeq1 with generateEmptyEnv noMatchSeq1 using sameSemantics in

let noMatchSeqLen = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
    (addi_ (var_ "a") (var_ "b"))
    (int_ 42)) in
utest noMatchSeqLen with generateEmptyEnv noMatchSeqLen using sameSemantics in

let noMatchSeqLen2 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
    (addi_ (var_ "a") (var_ "b"))
    (int_ 42)) in
utest noMatchSeqLen2 with generateEmptyEnv noMatchSeqLen2 using sameSemantics in

let matchOr1 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchOr1 with generateEmptyEnv matchOr1 using sameSemantics in

let matchOr2 = symbolize
  (match_ (seq_ [int_ 2, int_ 1])
    (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchOr2 with generateEmptyEnv matchOr2 using sameSemantics in

let matchOr3 = symbolize
  (match_ (seq_ [int_ 3, int_ 1])
    (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchOr3 with generateEmptyEnv matchOr3 using sameSemantics in

let matchNestedOr1 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
          (pseqtot_ [pint_ 3, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchNestedOr1 with generateEmptyEnv matchNestedOr1 using sameSemantics in

let matchNestedOr2 = symbolize
  (match_ (seq_ [int_ 2, int_ 1])
    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
          (pseqtot_ [pint_ 3, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchNestedOr2 with generateEmptyEnv matchNestedOr2 using sameSemantics in

let matchNestedOr3 = symbolize
  (match_ (seq_ [int_ 3, int_ 7])
    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
          (pseqtot_ [pint_ 3, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchNestedOr3 with generateEmptyEnv matchNestedOr3 using sameSemantics in

let matchNestedOr4 = symbolize
  (match_ (seq_ [int_ 4, int_ 7])
    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
          (pseqtot_ [pint_ 3, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchNestedOr4 with generateEmptyEnv matchNestedOr4 using sameSemantics in

let matchNot1 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pnot_ (pseqtot_ [pint_ 1, pvar_ "a"]))
    true_
    false_) in
utest matchNot1 with generateEmptyEnv matchNot1 using sameSemantics in

let matchNot2 = symbolize
  (match_ (seq_ [int_ 2, int_ 2])
    (pnot_ (pseqtot_ [pint_ 1, pvar_ "a"]))
    true_
    false_) in
utest matchNot2 with generateEmptyEnv matchNot2 using sameSemantics in

let matchAnd1 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pvar_ "b"))
    (addi_ (var_ "a") (get_ (var_ "b") (int_ 1)))
    (int_ 53)) in
utest matchAnd1 with generateEmptyEnv matchAnd1 using sameSemantics in

let matchAnd2 = symbolize
  (match_ (seq_ [int_ 2, int_ 2])
    (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pvar_ "b"))
    (addi_ (var_ "a") (get_ (var_ "b") (int_ 1)))
    (int_ 53)) in
utest matchAnd2 with generateEmptyEnv matchAnd2 using sameSemantics in

let matchAnd3 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ []))
    (var_ "a")
    (int_ 53)) in
utest matchAnd3 with generateEmptyEnv matchAnd3 using sameSemantics in

let matchAnd4 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pand_ (pseqtot_ []) (pseqtot_ [pint_ 1, pvar_ "a"]))
    (var_ "a")
    (int_ 53)) in
utest matchAnd4 with generateEmptyEnv matchAnd4 using sameSemantics in

let matchSeqEdge1 = symbolize
  (match_ (seq_ [int_ 1])
    (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
    (addi_ (var_ "a") (var_ "c"))
    (int_ 75)) in
utest matchSeqEdge1 with generateEmptyEnv matchSeqEdge1 using sameSemantics in

let matchSeqEdge2 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
    (addi_ (var_ "a") (var_ "c"))
    (int_ 75)) in
utest matchSeqEdge2 with generateEmptyEnv matchSeqEdge2 using sameSemantics in

let matchSeqEdge3 = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3])
    (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
    (addi_ (var_ "a") (var_ "c"))
    (int_ 75)) in
utest matchSeqEdge3 with generateEmptyEnv matchSeqEdge3 using sameSemantics in

let matchSeqEdge4 = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
    (pseqedge_ [pvar_ "a", pvar_ "d"] "b" [pvar_ "c"])
    (addi_ (addi_ (var_ "d") (var_ "a")) (var_ "c"))
    (int_ 75)) in
utest matchSeqEdge4 with generateEmptyEnv matchSeqEdge4 using sameSemantics in

let matchSeqEdge5 = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
    (por_ (pseqedge_ [pint_ 2] "b" []) (pseqedge_ [pint_ 1] "b" []))
    (match_ (var_ "b")
      (pseqedgew_ [pvar_ "a"] [pvar_ "c"])
      (addi_ (var_ "a") (var_ "c"))
      (int_ 84))
    (int_ 75)) in
utest matchSeqEdge5 with generateEmptyEnv matchSeqEdge5 using sameSemantics in

let matchSeqEdge6 = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
    (por_ (pseqedge_ [pint_ 2] "b" []) (pseqedge_ [] "b" [pint_ 4]))
    (match_ (var_ "b")
      (pseqedgew_ [pvar_ "a"] [pvar_ "c"])
      (addi_ (var_ "a") (var_ "c"))
      (int_ 84))
    (int_ 75)) in
utest matchSeqEdge6 with generateEmptyEnv matchSeqEdge6 using sameSemantics in

let matchSeqEdge7 = symbolize
  (match_ (seq_ [int_ 1])
    (pseqedgew_ [pvar_ "a"] [])
    (var_ "a")
    (int_ 75)) in
utest matchSeqEdge7 with generateEmptyEnv matchSeqEdge7 using sameSemantics in

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
  eitherMatch (
    match_ (nconapp_ left (int_ 7))
      (npcon_ left (pvar_ "n"))
      (withType tyint_ (var_ "n"))
      (int_ 0))) in
utest stripTypeDecls matchCon1 with generateTypeAnnotated matchCon1 using sameSemantics in

let matchCon2 = symbolize (
  eitherMatch (
    match_ (nconapp_ left (int_ 7))
      (npcon_ right (pvar_ "n"))
      (withType tyint_ (var_ "n"))
      (int_ 0))) in
utest stripTypeDecls matchCon2 with generateTypeAnnotated matchCon2 using sameSemantics in

let matchCon3 = symbolize (
  eitherMatch (
    match_ (nconapp_ left (int_ 7))
      (npcon_ left (pint_ 7))
      (int_ 1)
      (int_ 0))) in
utest stripTypeDecls matchCon3 with generateTypeAnnotated matchCon3 using sameSemantics in

let matchCon4 = symbolize (
  eitherMatch (
    match_ (nconapp_ left (int_ 7))
      (npcon_ right (pint_ 7))
      (int_ 1)
      (int_ 0))) in
utest stripTypeDecls matchCon4 with generateTypeAnnotated matchCon4 using sameSemantics in

let matchNestedCon1 = symbolize (
  eitherMatch (
    match_ (nconapp_ nested (nconapp_ left (int_ 7)))
      (npcon_ nested (pvar_ "n"))
      (int_ 1)
      (int_ 0))) in
utest stripTypeDecls matchNestedCon1 with generateTypeAnnotated matchNestedCon1
using sameSemantics in

let matchNestedCon2 = symbolize (
  eitherMatch (
    match_ (nconapp_ nested (nconapp_ left (int_ 7)))
      (npcon_ nested (npcon_ left (pvar_ "n")))
      (withType tyint_ (var_ "n"))
      (int_ 0))) in
utest stripTypeDecls matchNestedCon2 with generateTypeAnnotated matchNestedCon2
using sameSemantics in

let matchNestedCon3 = symbolize (
  eitherMatch (
    match_ (nconapp_ nested (nconapp_ left (int_ 7)))
      (npcon_ nested (npcon_ left (pint_ 7)))
      (int_ 1)
      (int_ 0))) in
utest stripTypeDecls matchNestedCon3 with generateTypeAnnotated matchNestedCon3
using sameSemantics in

let matchNestedCon4 = symbolize (
  eitherMatch (
    match_ (nconapp_ nested (nconapp_ left (int_ 7)))
      (npcon_ nested (pvar_ "n1"))
      (match_ (var_ "n1")
        (npcon_ left (pvar_ "n2"))
        (var_ "n2")
        (int_ 1))
      (int_ 2))) in
utest stripTypeDecls matchNestedCon4 with generateTypeAnnotated matchNestedCon4
using sameSemantics in

let matchNestedCon5 = symbolize (
  eitherMatch (
    match_ (nconapp_ nested (nconapp_ left (int_ 7)))
      (npcon_ nested (pvar_ "n1"))
      (match_ (var_ "n1")
        (npcon_ right (pvar_ "n2"))
        (var_ "n2")
        (int_ 1))
      (int_ 2))) in
utest stripTypeDecls matchNestedCon5 with generateTypeAnnotated matchNestedCon5
using sameSemantics in

let r = record_ [
  ("a", record_ [
    ("x", int_ 4),
    ("y", true_),
    ("z", seq_ [int_ 1, int_ 2, int_ 3])
  ]),
  ("b", char_ 'x'),
  ("c", int_ 7),
  ("d", float_ 1.2)
] in
let matchRecord1 = symbolize (
  match_ r
    (prec_ [("c", pint_ 3), ("d", pvar_ "n")])
    (var_ "n")
    (float_ 0.0)) in
utest stripTypeDecls matchRecord1 with generateTypeAnnotated matchRecord1
using sameSemantics in

let matchRecord2 = symbolize (
  match_ r
    (prec_ [("c", pvar_ "c"), ("d", pvar_ "n")])
    (var_ "n")
    (float_ 0.5)) in
utest stripTypeDecls matchRecord2 with generateTypeAnnotated matchRecord2
using sameSemantics in

let matchRecord3 = symbolize (
  match_ r
    (prec_ [("d", pvar_ "d"), ("b", pvar_ "ch"), ("c", pint_ 0)])
    (var_ "ch")
    (char_ '0')) in
utest stripTypeDecls matchRecord3 with generateTypeAnnotated matchRecord3
using sameSemantics in

let matchRecord4 = symbolize (
  match_ r
    (prec_ [("d", pvar_ "d"), ("b", pvar_ "ch"), ("c", pint_ 7)])
    (var_ "ch")
    (char_ '0')) in
utest stripTypeDecls matchRecord4 with generateTypeAnnotated matchRecord4
using sameSemantics in

let matchNestedRecord1 = symbolize (
  (match_ r
    (prec_ [("a", prec_ [("x", pvar_ "m")]), ("c", pvar_ "n")])
    (addi_ (var_ "m") (var_ "n"))
    (int_ 0))) in
utest stripTypeDecls matchNestedRecord1 with generateTypeAnnotated matchNestedRecord1
using sameSemantics in

let matchNestedRecord2 = symbolize (
  match_ r
    (prec_ [
      ("a", prec_ [("z", pseqtot_ [pvar_ "m", pint_ 2, pvarw_])]),
      ("c", pvar_ "n")])
    (addi_ (var_ "m") (var_ "n"))
    (int_ 0)) in
utest stripTypeDecls matchNestedRecord2 with generateTypeAnnotated matchNestedRecord2
using sameSemantics in

let matchNestedRecord3 = symbolize (
  match_ r
    (prec_ [
      ("a", prec_ [("y", pvar_ "b"), ("z", pvarw_)])])
    (var_ "b")
    false_) in
utest stripTypeDecls matchNestedRecord3 with generateTypeAnnotated matchNestedRecord3
using sameSemantics in

let tree = nameSym "Tree" in
let tyTree = ntyvar_ tree in
let branch = nameSym "Branch" in
let tyBranch = tyrecord_ [("lhs", tyTree), ("rhs", tyTree)] in
let leaf = nameSym "Leaf" in
let conMatch = lam m.
  bindall_ [
    ntype_ tree tyunknown_,
    ncondef_ branch (tyarrow_ tyBranch tyTree),
    ncondef_ leaf (tyarrow_ tyint_ tyTree),
    ulet_ "x" (nconapp_ branch (record_ [
      ("lhs", nconapp_ branch (record_ [
        ("lhs", nconapp_ leaf (int_ 1)),
        ("rhs", nconapp_ leaf (int_ 3))
      ])),
      ("rhs", nconapp_ leaf (int_ 2))
    ])),
    m
  ] in
let matchRecordCon1 = symbolize (
  conMatch (
    match_ (var_ "x")
      (npcon_ branch (prec_ [
        ("lhs", npcon_ branch (pvarw_)),
        ("rhs", npcon_ leaf (pvar_ "r"))
      ]))
      (var_ "r")
      (int_ 0))) in
utest stripTypeDecls matchRecordCon1 with generateTypeAnnotated matchRecordCon1
using sameSemantics in

let matchRecordCon2 = symbolize (
  conMatch (
    match_ (var_ "x")
      (npcon_ branch (prec_ [
        ("lhs", npcon_ branch (prec_ [
          ("lhs", npcon_ leaf (pvar_ "ll")),
          ("rhs", npcon_ leaf (pint_ 3))
        ])),
        ("rhs", npcon_ leaf (pvar_ "r"))
      ]))
      (addi_ (var_ "r") (var_ "ll"))
      (int_ 0))) in
utest stripTypeDecls matchRecordCon2 with generateTypeAnnotated matchRecordCon2
using sameSemantics in

let matchRecordCon3 = symbolize (
  conMatch (
    match_ (var_ "x")
      (npcon_ branch (prec_ [
        ("lhs", npcon_ branch (prec_ [
          ("lhs", npcon_ leaf (pvar_ "ll")),
          ("rhs", npcon_ leaf (pint_ 0))
        ])),
        ("rhs", npcon_ leaf (pvar_ "r"))
      ]))
      (addi_ (var_ "r") (var_ "ll"))
      (int_ 0))) in
utest stripTypeDecls matchRecordCon3 with generateTypeAnnotated matchRecordCon3
using sameSemantics in

let recordUpdate1 = symbolize (
  match_ (recordupdate_ (record_ [("a", int_ 0)]) "a" (int_ 1))
    (prec_ [("a", pvar_ "a")])
      (var_ "a")
      (int_ 0)) in
utest recordUpdate1 with generateTypeAnnotated recordUpdate1
using sameSemantics in

let recordUpdate2 = symbolize (
  bindall_ [
    ulet_ "r" (record_ [
      ("a", int_ 2), ("b", true_), ("c", float_ 3.14)
    ]),
    ulet_ "r" (recordupdate_ (var_ "r") "c" (float_ 2.0)),
    match_ (var_ "r")
      (prec_ [("c", pvar_ "c")])
      (var_ "c")
      (float_ 0.0)
  ])
in
utest recordUpdate2 with generateTypeAnnotated recordUpdate2
using sameSemantics in

let recordWithLet = symbolize (
  bindall_
  [ ulet_ "r" (record_ [
     ("f", bind_ (ulet_ "x" (int_ 3)) (addi_ (var_ "x") (int_ 1))),
     ("g", ulam_ "x" (var_ "x"))])
  , int_ 42
  ]) in
utest recordWithLet with generateTypeAnnotated recordWithLet
using sameSemantics in

let recordWithLam = symbolize (
  bindall_
  [ ulet_ "r" (record_ [
     ("foo", ulam_ "x" (var_ "x"))])
  , ulet_ "foo" (recordproj_ "foo" (var_ "r"))
  , app_ (var_ "foo") (int_ 42)
  ]) in
utest recordWithLam with generateTypeAnnotated recordWithLam
using sameSemantics in

-- Ints
let addInt1 = addi_ (int_ 1) (int_ 2) in
utest addInt1 with generateEmptyEnv addInt1 using sameSemantics in

let addInt2 = addi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest addInt2 with generateEmptyEnv addInt2 using sameSemantics in

let testMulInt = muli_ (int_ 2) (int_ 3) in
utest testMulInt with generateEmptyEnv testMulInt using sameSemantics in

let testModInt = modi_ (int_ 2) (int_ 3) in
utest testModInt with generateEmptyEnv testModInt using sameSemantics in

let testDivInt = divi_ (int_ 2) (int_ 3) in
utest testDivInt with generateEmptyEnv testDivInt using sameSemantics in

let testNegInt = addi_ (int_ 2) (negi_ (int_ 2)) in
utest testNegInt with generateEmptyEnv testNegInt using sameSemantics in

let compareInt1 = eqi_ (int_ 1) (int_ 2) in
utest compareInt1 with generateEmptyEnv compareInt1 using sameSemantics in

let compareInt2 = lti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt2 with generateEmptyEnv compareInt2 using sameSemantics in

let compareInt3 = leqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt3 with generateEmptyEnv compareInt3 using sameSemantics in

let compareInt4 = gti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt4 with generateEmptyEnv compareInt4 using sameSemantics in

let compareInt5 = geqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt5 with generateEmptyEnv compareInt5 using sameSemantics in

let compareInt6 = neqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt6 with generateEmptyEnv compareInt6 using sameSemantics in

let shiftInt1 = slli_ (int_ 5) (int_ 2) in
utest shiftInt1 with generateEmptyEnv shiftInt1 using sameSemantics in

let shiftInt2 = srli_ (int_ 5) (int_ 2) in
utest shiftInt2 with generateEmptyEnv shiftInt2 using sameSemantics in

let shiftInt3 = srai_ (int_ 5) (int_ 2) in
utest shiftInt3 with generateEmptyEnv shiftInt3 using sameSemantics in

---- Floats
let addFloat1 = addf_ (float_ 1.) (float_ 2.) in
utest addFloat1 with generateEmptyEnv addFloat1 using sameSemantics in

let addFloat2 = addf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest addFloat2 with generateEmptyEnv addFloat2 using sameSemantics in

let testMulFloat = mulf_ (float_ 2.) (float_ 3.) in
utest testMulFloat with generateEmptyEnv testMulFloat using sameSemantics in

let testDivFloat = divf_ (float_ 6.) (float_ 3.) in
utest testDivFloat with generateEmptyEnv testDivFloat using sameSemantics in

let testNegFloat = addf_ (float_ 2.) (negf_ (float_ 2.)) in
utest testNegFloat with generateEmptyEnv testNegFloat using sameSemantics in

let compareFloat1 = eqf_ (float_ 1.) (float_ 2.) in
utest compareFloat1 with generateEmptyEnv compareFloat1 using sameSemantics in

let compareFloat2 = ltf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat2 with generateEmptyEnv compareFloat2 using sameSemantics in

let compareFloat3 = leqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat3 with generateEmptyEnv compareFloat3 using sameSemantics in

let compareFloat4 = gtf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat4 with generateEmptyEnv compareFloat4 using sameSemantics in

let compareFloat5 = geqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat5 with generateEmptyEnv compareFloat5 using sameSemantics in

let compareFloat6 = neqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat6 with generateEmptyEnv compareFloat6 using sameSemantics in

-- Chars
let charLiteral = char_ 'c' in
utest charLiteral with generateEmptyEnv charLiteral using sameSemantics in

let compareChar1 = eqc_ (char_ 'a') (char_ 'b') in
utest compareChar1 with generateEmptyEnv compareChar1 using sameSemantics in

let compareChar2 = eqc_ (char_ 'a') (char_ 'a') in
utest compareChar2 with generateEmptyEnv compareChar2 using sameSemantics in

let testCharToInt = char2int_ (char_ '0') in
utest testCharToInt with generateEmptyEnv testCharToInt using sameSemantics in

let testIntToChar = int2char_ (int_ 48) in
utest testIntToChar with generateEmptyEnv testIntToChar using sameSemantics in

-- Abstractions
let fun =
  symbolize
  (appSeq_
    (ulam_ "@" (ulam_ "%" (addi_ (var_ "@") (var_ "%"))))
    [int_ 1, int_ 2])
in
utest fun with generateEmptyEnv fun using sameSemantics in

let funShadowed =
  symbolize
  (appSeq_
    (ulam_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))))
    [ulam_ "@" (var_ "@"), int_ 2])
in
utest funShadowed with generateEmptyEnv funShadowed using sameSemantics in

-- Lets
let testLet =
  symbolize
  (bindall_ [ulet_ "^" (int_ 1), addi_ (var_ "^") (int_ 2)])
in
utest testLet with generateEmptyEnv testLet using sameSemantics in

let testLetShadowed =
  symbolize
  (bindall_ [ulet_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))),
             app_ (var_ "@") (int_ 1)])
in
utest testLetShadowed with generateEmptyEnv testLetShadowed
using sameSemantics in

let testLetRec =
  symbolize
  (bind_
     (ureclets_add "$" (ulam_ "%" (app_ (var_ "@") (int_ 1)))
     (ureclets_add "@" (ulam_ "" (var_ ""))
     reclets_empty))
   (app_ (var_ "$") (var_ "@")))
in
utest testLetRec with generateEmptyEnv testLetRec using sameSemantics in

-- Sequences
let testEmpty = symbolize (length_ (seq_ [])) in
utest testEmpty with generateEmptyEnv testEmpty using sameSemantics in

let nonEmpty = seq_ [int_ 1, int_ 2, int_ 3] in
let len = length_ nonEmpty in
let fst = get_ nonEmpty (int_ 0) in
let snd = get_ nonEmpty (int_ 1) in
let thrd = get_ nonEmpty (int_ 2) in
utest int_ 3 with generateEmptyEnv len using sameSemantics in
utest int_ 1 with generateEmptyEnv fst using sameSemantics in
utest int_ 2 with generateEmptyEnv snd using sameSemantics in
utest int_ 3 with generateEmptyEnv thrd using sameSemantics in

let testCreate = create_ (int_ 2) (ulam_ "_" (int_ 0)) in
let len = length_ testCreate in
let fst = get_ testCreate (int_ 0) in
let lst = get_ testCreate (int_ 1) in
utest int_ 2 with generateEmptyEnv len using sameSemantics in
utest int_ 0 with generateEmptyEnv fst using sameSemantics in
utest int_ 0 with generateEmptyEnv lst using sameSemantics in

let testSet = set_ (seq_ [int_ 1, int_ 2]) (int_ 0) (int_ 3) in
let len = length_ testSet in
let fst = get_ testSet (int_ 0) in
let snd = get_ testSet (int_ 1) in
utest int_ 2 with generateEmptyEnv len using sameSemantics in
utest int_ 3 with generateEmptyEnv fst using sameSemantics in
utest int_ 2 with generateEmptyEnv snd using sameSemantics in

let testCons = cons_  (int_ 1) (seq_ [int_ 2, int_ 3]) in
let len = length_ testCons in
let fst = get_ testCons (int_ 0) in
let snd = get_ testCons (int_ 1) in
let thrd = get_ testCons (int_ 2) in
utest int_ 3 with generateEmptyEnv len using sameSemantics in
utest int_ 1 with generateEmptyEnv fst using sameSemantics in
utest int_ 2 with generateEmptyEnv snd using sameSemantics in
utest int_ 3 with generateEmptyEnv thrd using sameSemantics in

let testSnoc = snoc_ (seq_ [int_ 1, int_ 2]) (int_ 3) in
let len = length_ testSnoc in
let fst = get_ testSnoc (int_ 0) in
let snd = get_ testSnoc (int_ 1) in
let thrd = get_ testSnoc (int_ 2) in
utest int_ 3 with generateEmptyEnv len using sameSemantics in
utest int_ 1 with generateEmptyEnv fst using sameSemantics in
utest int_ 2 with generateEmptyEnv snd using sameSemantics in
utest int_ 3 with generateEmptyEnv thrd using sameSemantics in

let testReverse = reverse_ (seq_ [int_ 1, int_ 2, int_ 3]) in
let len = length_ testReverse in
let fst = get_ testReverse (int_ 0) in
let snd = get_ testReverse (int_ 1) in
let thrd = get_ testReverse (int_ 2) in
utest int_ 3 with generateEmptyEnv len using sameSemantics in
utest int_ 3 with generateEmptyEnv fst using sameSemantics in
utest int_ 2 with generateEmptyEnv snd using sameSemantics in
utest int_ 1 with generateEmptyEnv thrd using sameSemantics in

let testSeq = seq_ [int_ 1, int_ 2, int_ 3] in
let testSubseq1 = subsequence_ testSeq (int_ 0) (int_ 2) in
let testSubseq2 = subsequence_ testSeq (int_ 1) (int_ 2) in
let testSubseq3 = subsequence_ testSeq (int_ 2) (int_ 100) in
let fst = get_ testSubseq3 (int_ 0) in
utest int_ 2 with generateEmptyEnv (length_ testSubseq1) using sameSemantics in
utest int_ 2 with generateEmptyEnv (length_ testSubseq2) using sameSemantics in
utest int_ 1 with generateEmptyEnv (length_ testSubseq3) using sameSemantics in
utest int_ 3 with generateEmptyEnv fst using sameSemantics in

let testGetFun = bindall_
[ ulet_ "lst" (seq_ [ulam_ "x" (var_ "x")])
, ulet_ "f" (get_ (var_ "lst") (int_ 0))
, ulet_ "_" (app_ (var_ "f") (int_ 1))
, ulet_ "_" (app_ (ulam_ "x" (var_ "x")) (app_ (var_ "f") (int_ 1)))
, ulet_ "_" (addi_ (app_ (var_ "f") (int_ 1)) (int_ 1))
, int_ 1
] in
utest int_ 1 with generateEmptyEnv testGetFun using sameSemantics in

-- splitat
let testStr = str_ "foobar" in
let testSplit0 = (bindall_ [ ulet_ "y" (splitat_ testStr (int_ 3)), tupleproj_ 0 (var_ "y")]) in
let testSplit1 = (bindall_ [ ulet_ "y" (splitat_ testStr (int_ 3)), tupleproj_ 1 (var_ "y")]) in
utest ocamlEvalChar (generateTypeAnnotated (get_ testSplit0 (int_ 0))) with char_ 'f' using eqExpr in
utest ocamlEvalChar (generateTypeAnnotated (get_ testSplit0 (int_ 1))) with char_ 'o' using eqExpr in
utest ocamlEvalChar (generateTypeAnnotated (get_ testSplit0 (int_ 2))) with char_ 'o' using eqExpr in
utest ocamlEvalChar (generateTypeAnnotated (get_ testSplit1 (int_ 0))) with char_ 'b' using eqExpr in
utest ocamlEvalChar (generateTypeAnnotated (get_ testSplit1 (int_ 1))) with char_ 'a' using eqExpr in
utest ocamlEvalChar (generateTypeAnnotated (get_ testSplit1 (int_ 2))) with char_ 'r' using eqExpr in

-- eqsym
let eqsymTest = (bind_ (ulet_ "s" (gensym_ unit_)) (eqsym_ (var_ "s") (var_ "s"))) in
utest ocamlEvalBool (generateEmptyEnv eqsymTest) with true_ using eqExpr in

-- sym2hash
let sym2hashTest = symbolize (bindall_
        [ ulet_ "x" (gensym_ unit_)
        , eqi_ (sym2hash_ (var_ "x")) (sym2hash_ (var_ "x"))]) in

-- Float-Integer conversions
let testFloorfi = floorfi_ (float_ 1.5) in
utest testFloorfi with generateEmptyEnv testFloorfi using sameSemantics in

let testCeilfi = ceilfi_ (float_ 1.5) in
utest testCeilfi with generateEmptyEnv testCeilfi using sameSemantics in

let testRoundfi = roundfi_ (float_ 1.5) in
utest testRoundfi with generateEmptyEnv testRoundfi using sameSemantics in

let testInt2float = int2float_ (int_ 1) in
utest testInt2float with generateEmptyEnv testInt2float using sameSemantics in

let testString2float = string2float_ (str_ "1.5") in
utest testString2float with generateEmptyEnv testString2float using sameSemantics in

let testFloat2string = symbolize (float2string_ (float_ 1.5)) in
utest ocamlEvalChar (generateEmptyEnv (get_ testFloat2string (int_ 0)))
with char_ '1' using eqExpr in
utest ocamlEvalChar (generateEmptyEnv (get_ testFloat2string (int_ 1)))
with char_ '.' using eqExpr in
utest ocamlEvalChar (generateEmptyEnv (get_ testFloat2string (int_ 2)))
with char_ '5' using eqExpr in

-- File operations
let testFileExists = fileExists_ (str_ "test_file_ops") in
utest testFileExists with generateEmptyEnv testFileExists using sameSemantics in

-- -- IO operations
--  NOTE(gizem, 21-03-19): This test file prints an empty string.
let testPrint = symbolize (bind_ (ulet_ "_" (print_ (str_ ""))) (int_ 0)) in
utest testPrint with generateEmptyEnv testPrint using sameSemantics in

let testDPrint = symbolize (bind_ (ulet_ "_" (dprint_ (str_ ""))) (int_ 0)) in
utest testDPrint with generateEmptyEnv testDPrint using sameSemantics in

let testCommand = command_ (str_ "echo \"42\"") in
utest ocamlEval (generateEmptyEnv testCommand) with int_ 42 using eqExpr in

-- Random number generation operations
let testSeededRandomNumber =
 symbolize
 (bindall_ [ulet_ "_" (randSetSeed_ (int_ 42)),
            randIntU_ (int_ 0) (int_ 10)])
in
utest testSeededRandomNumber with generateEmptyEnv testSeededRandomNumber
using sameSemantics in

-- Time operations
let testWallTimeMs = bindall_ [ulet_ "x" (wallTimeMs_ unit_), divf_ (var_ "x") (var_ "x")] in
utest ocamlEvalFloat (generateEmptyEnv testWallTimeMs) with float_ 1.0 using eqExpr in

let testSleepMs = symbolize (bind_ (sleepMs_ (int_ 10)) (int_ 5)) in
utest testSleepMs with generateEmptyEnv testSleepMs using sameSemantics in

-- TODO(oerikss, 2020-12-14): Sys operations are not tested

-- Map intrinsics
let mapEmptyTest = bind_
  (ulet_ "m" (mapEmpty_ (ulam_ "x" (ulam_ "y" (subi_ (var_ "x") (var_ "y"))))))
  (int_ 42) in

utest ocamlEvalInt (generateEmptyEnv mapEmptyTest) with int_ 42 using eqExpr in

let mapInsertFindTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 123) (int_ 90) (var_ "m"))
  , mapFindWithExn_ (int_ 42) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapInsertFindTest)
with int_ 1 using eqExpr in

let mapMemTrueTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapMem_ (int_ 42) (var_ "m")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapMemTrueTest)
with true_ using eqExpr in

let mapMemFalseTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapMem_ (int_ 78) (var_ "m")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapMemFalseTest)
with false_ using eqExpr in

let mapRemoveTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , ulet_ "m" (mapRemove_ (int_ 42) (var_ "m"))
  , mapMem_ (int_ 42) (var_ "m")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapRemoveTest)
with false_ using eqExpr in

let mapFindOrElseTrueTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapFindOrElse_ (ulam_ "" (int_ 123)) (int_ 42) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapFindOrElseTrueTest)
with int_ 1 using eqExpr in

let mapFindOrElseFalseTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapFindOrElse_ (ulam_ "" (int_ 123)) (int_ 3) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapFindOrElseFalseTest)
with int_ 123 using eqExpr in

let mapFindApplyOrElseTrueTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapFindApplyOrElse_
      (ulam_ "x" (addi_ (var_ "x") (int_ 1)))
      (ulam_ "" (int_ 7))
      (int_ 42) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapFindApplyOrElseTrueTest)
with int_ 2 using eqExpr in

let mapFindApplyOrElseFalseTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapFindApplyOrElse_
     (ulam_ "x" (addi_ (var_ "x") (int_ 1)))
     (ulam_ "" (int_ 7))
     (int_ 3) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapFindApplyOrElseFalseTest)
with int_ 7 using eqExpr in

let mapSizeEmptyTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , mapSize_ (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapSizeEmptyTest)
with int_ 0 using eqExpr in

let mapSizeTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 100) (int_ 567) (var_ "m"))
  , mapSize_ (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapSizeTest)
with int_ 2 using eqExpr in

let mapAnyTrueTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , mapAny_ (ulam_ "k" (ulam_ "v" (geqi_ (var_ "k") (var_ "v")))) (var_ "m")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapAnyTrueTest)
with true_ using eqExpr in

let mapAnyFalseTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 0) (negi_ (int_ 1)) (var_ "m"))
  , mapAny_ (ulam_ "k" (ulam_ "v" (eqi_ (var_ "k") (var_ "v")))) (var_ "m")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapAnyFalseTest)
with false_ using eqExpr in

let mapMapTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 3) (int_ 56) (var_ "m"))
  , ulet_ "m" (mapMap_ (ulam_ "v" (addi_ (int_ 44) (var_ "v"))) (var_ "m"))
  , mapFindWithExn_ (int_ 3) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapMapTest)
with int_ 100 using eqExpr in

let mapMapWithKeyTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 3) (int_ 56) (var_ "m"))
  , ulet_ "m"
    (mapMapWithKey_ (ulam_ "k" (ulam_ "v"
      (addi_ (var_ "k") (var_ "v")))) (var_ "m"))
  , mapFindWithExn_ (int_ 3) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapMapWithKeyTest)
with int_ 59 using eqExpr in

let mapFoldWithKeyTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 3) (int_ 56) (var_ "m"))
  , mapFoldWithKey_
      (ulam_ "acc" (ulam_ "k" (ulam_ "v"
        (addi_ (var_ "acc") (addi_ (var_ "k") (var_ "v")))))) (int_ 0) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapFoldWithKeyTest)
with int_ 103 using eqExpr in

let mapFoldWithKeyNonAssociativeTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 3) (int_ 56) (var_ "m"))
  , mapFoldWithKey_
      (ulam_ "acc" (ulam_ "k" (ulam_ "v"
        (addi_ (var_ "acc") (addi_ (muli_ (var_ "k") (int_ 2))
                                   (var_ "v")))))) (int_ 0) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapFoldWithKeyNonAssociativeTest)
with int_ 148 using eqExpr in

let mapEqTrueTest = bindall_
  [ ulet_ "m1" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "m2" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m2" (mapInsert_ (int_ 42) (int_ 2) (var_ "m2"))
  , ulet_ "m2" (mapInsert_ (int_ 3) (int_ 56) (var_ "m2"))
  , mapEq_ (ulam_ "v1" (ulam_ "v2"
      (eqi_ (var_ "v1") (var_ "v2")))) (var_ "m1") (var_ "m2")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapEqTrueTest)
with true_ using eqExpr in

let mapEqFalseTest = bindall_
  [ ulet_ "m1" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "m2" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m2" (mapInsert_ (int_ 42) (int_ 3) (var_ "m2"))
  , ulet_ "m2" (mapInsert_ (int_ 3) (int_ 56) (var_ "m2"))
  , mapEq_ (ulam_ "v1" (ulam_ "v2"
      (eqi_ (var_ "v1") (var_ "v2")))) (var_ "m1") (var_ "m2")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapEqFalseTest)
with false_ using eqExpr in

let mapCmpEqTest = bindall_
  [ ulet_ "m1" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "m2" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m2" (mapInsert_ (int_ 42) (int_ 2) (var_ "m2"))
  , ulet_ "m2" (mapInsert_ (int_ 3) (int_ 56) (var_ "m2"))
  , mapCmp_ (ulam_ "v1" (ulam_ "v2"
      (subi_ (var_ "v1") (var_ "v2")))) (var_ "m1") (var_ "m2")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapCmpEqTest)
with int_ 0 using eqExpr in

let mapCmpNEqTest = bindall_
  [ ulet_ "m1" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "m2" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m2" (mapInsert_ (int_ 42) (int_ 1) (var_ "m2"))
  , ulet_ "m2" (mapInsert_ (int_ 3) (int_ 56) (var_ "m2"))
  , mapCmp_ (ulam_ "v1" (ulam_ "v2"
      (subi_ (var_ "v1") (var_ "v2")))) (var_ "m1") (var_ "m2")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapCmpNEqTest)
with int_ 1 using eqExpr in

let mapGetCmpFunTest = bindall_
  [ ulet_ "m" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "f" (mapGetCmpFun_ (var_ "m"))
  , appf2_ (var_ "f") (int_ 12) (int_ 2)
  ] in
utest ocamlEvalInt (generateEmptyEnv mapGetCmpFunTest)
with int_ 10 using eqExpr in

-- mapBindings
let mapBindingsTest = (bindall_
  [ ulet_ "m1" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , (mapBindings_ (var_ "m1"))
  ]) in
let t00 = (bindall_
         [ let_ "b0" (tytuple_ [tyint_, tyint_]) (get_ mapBindingsTest (int_ 0))
         , tupleproj_ 0 (var_ "b0")
         ]) in
let t01 = (bindall_
         [ let_ "b0" (tytuple_ [tyint_, tyint_]) (get_ mapBindingsTest (int_ 0))
         , tupleproj_ 1 (var_ "b0")
         ]) in
let t10 = (bindall_
         [ let_ "b1" (tytuple_ [tyint_, tyint_]) (get_ mapBindingsTest (int_ 1))
         , tupleproj_ 0 (var_ "b1")
         ]) in
let t11 = (bindall_
         [ let_ "b1" (tytuple_ [tyint_, tyint_]) (get_ mapBindingsTest (int_ 1))
         , tupleproj_ 1 (var_ "b1")
         ]) in

utest ocamlEvalInt (generateTypeAnnotated t00) with int_ 3 using eqExpr in
utest ocamlEvalInt (generateTypeAnnotated t01) with int_ 56 using eqExpr in
utest ocamlEvalInt (generateTypeAnnotated t10) with int_ 42 using eqExpr in
utest ocamlEvalInt (generateTypeAnnotated t11) with int_ 2 using eqExpr in

let mapBindingsTest = bindall_
  [ ulet_ "m1" (mapEmpty_ (uconst_ (CSubi ())))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "seq" (mapBindings_ (var_ "m1"))
  , length_ (var_ "seq")
  ] in

utest ocamlEvalInt (generateEmptyEnv mapBindingsTest) with int_ 2 using eqExpr in

-- References
let refDeRefIntTest = deref_ (ref_ (int_ 1)) in
utest ocamlEvalInt (generateEmptyEnv refDeRefIntTest)
with int_ 1 using eqExpr in

let refModrefDerefIntTest =
  bind_
    (ulet_ "x" (ref_ (int_ 1)))
    (semi_ (modref_ (var_ "x") (int_ 2))
           (deref_ (var_ "x")))
in
utest ocamlEvalInt (generateEmptyEnv refModrefDerefIntTest)
with int_ 2 using eqExpr in

let refDeRefIntSeqTest = get_ (deref_ (ref_ (seq_ (int_ 1)))) (int_ 0) in
utest ocamlEvalInt (generateEmptyEnv refDeRefIntTest)
with int_ 1 using eqExpr in

let refModrefDerefSeqIntTest =
  bind_
    (ulet_ "x" (ref_ (seq_ (int_ 1))))
    (semi_ (modref_ (var_ "x") (seq_ (int_ 2)))
           (get_ (deref_ (var_ "x")) (int_ 0)))
in
utest ocamlEvalInt (generateEmptyEnv refModrefDerefIntTest)
with int_ 2 using eqExpr in

-- Tensor Ops
let tensorCreateGetIntTest =
  tensorGetExn_ tyint_ (tensorCreateInt_ (seq_ []) (ulam_ "x" (int_ 1)))
                       (seq_ [])
in
utest ocamlEvalInt (generateEmptyEnv tensorCreateGetIntTest)
with int_ 1 using eqExpr in

let tensorCreateGetFloatTest =
  tensorGetExn_ tyfloat_ (tensorCreateFloat_ (seq_ [])
                                                 (ulam_ "x" (float_ 1.)))
                         (seq_ [])
in
utest ocamlEvalFloat (generateEmptyEnv tensorCreateGetFloatTest)
with float_ 1. using eqExpr in

let tensorCreateGetCharTest =
  tensorGetExn_ tychar_ (tensorCreate_ tychar_ (seq_ [])
                                               (ulam_ "x" (char_ '1')))
                       (seq_ [])
in
utest ocamlEvalChar (generateEmptyEnv tensorCreateGetCharTest)
with char_ '1' using eqExpr in

let tensorSetIntTest =
  bind_
    (ulet_ "t" (tensorCreateInt_ (seq_ []) (ulam_ "x" (int_ 1))))
    (semi_ (tensorSetExn_ tyint_ (var_ "t")
                                 (seq_ [])
                                 (int_ 2))
           (tensorGetExn_ tyint_ (var_ "t")
                                 (seq_ [])))
in
utest ocamlEvalInt (generateEmptyEnv tensorSetIntTest)
with int_ 2 using eqExpr in

let tensorSetFloatTest =
  bind_
    (ulet_ "t" (tensorCreateFloat_ (seq_ []) (ulam_ "x" (float_ 1.))))
    (semi_ (tensorSetExn_ tyfloat_ (var_ "t")
                                   (seq_ [])
                                   (float_ 2.))
           (tensorGetExn_ tyfloat_ (var_ "t")
                                   (seq_ [])))
in
utest ocamlEvalFloat (generateEmptyEnv tensorSetFloatTest)
with float_ 2. using eqExpr in

let tensorSetCharTest =
  bind_
    (ulet_ "t" (tensorCreate_ tychar_ (seq_ []) (ulam_ "x" (char_ '1'))))
    (semi_ (tensorSetExn_ tychar_ (var_ "t")
                                  (seq_ [])
                                  (char_ '2'))
           (tensorGetExn_ tychar_ (var_ "t")
                                  (seq_ [])))
in
utest ocamlEvalChar (generateEmptyEnv tensorSetCharTest)
with char_ '2' using eqExpr in

let tensorRankIntTest =
  tensorRank_ tyint_ (tensorCreateInt_ (seq_ []) (ulam_ "x" (int_ 1)))
in
utest ocamlEvalInt (generateEmptyEnv tensorRankIntTest)
with int_ 0 using eqExpr in

let tensorRankFloatTest =
  tensorRank_ tyfloat_ (tensorCreateFloat_ (seq_ [])
                       (ulam_ "x" (float_ 1.)))
in
utest ocamlEvalInt (generateEmptyEnv tensorRankFloatTest)
with int_ 0 using eqExpr in

let tensorRankCharTest =
  tensorRank_ tychar_ (tensorCreate_ tychar_ (seq_ []) (ulam_ "x" (char_ '1')))
in
utest ocamlEvalInt (generateEmptyEnv tensorRankCharTest)
with int_ 0 using eqExpr in

let tensorShapeIntTest =
  length_ (tensorShape_ tyint_
                        (tensorCreateInt_ (seq_ [])
                        (ulam_ "x" (int_ 1))))
in
utest ocamlEvalInt (generateEmptyEnv tensorShapeIntTest)
with int_ 0 using eqExpr in

let tensorShapeFloatTest =
  length_ (tensorShape_ tyfloat_
                        (tensorCreateFloat_ (seq_ [])
                        (ulam_ "x" (float_ 1.))))
in
utest ocamlEvalInt (generateEmptyEnv tensorShapeFloatTest)
with int_ 0 using eqExpr in

let tensorShapeCharTest =
  length_ (tensorShape_ tychar_
                        (tensorCreate_ tychar_ (seq_ [])
                        (ulam_ "x" (char_ '1'))))
in
utest ocamlEvalInt (generateEmptyEnv tensorShapeCharTest)
with int_ 0 using eqExpr in

let tensorReshapeIntTest =
  tensorRank_ tyint_
              (tensorReshapeExn_ tyint_
                                 (tensorCreateInt_
                                                (seq_ [int_ 1, int_ 2])
                                                (ulam_ "x" (int_ 1)))
                                 (seq_ [int_ 2]))
in
utest ocamlEvalInt (generateEmptyEnv tensorReshapeIntTest)
with int_ 1 using eqExpr in

let tensorReshapeFloatTest =
  tensorRank_ tyfloat_
              (tensorReshapeExn_ tyfloat_
                                 (tensorCreateFloat_
                                                (seq_ [int_ 1, int_ 2])
                                                (ulam_ "x" (float_ 1.)))
                                 (seq_ [int_ 2]))
in
utest ocamlEvalInt (generateEmptyEnv tensorReshapeFloatTest)
with int_ 1 using eqExpr in

let tensorReshapeCharTest =
  tensorRank_ tychar_
              (tensorReshapeExn_ tychar_
                                 (tensorCreate_ tychar_
                                                (seq_ [int_ 1, int_ 2])
                                                (ulam_ "x" (char_ '1')))
                                 (seq_ [int_ 2]))
in
utest ocamlEvalInt (generateEmptyEnv tensorReshapeCharTest)
with int_ 1 using eqExpr in

let tensorCopyIntTest =
  bind_
  (ulet_ "t" (tensorCreateInt_ (seq_ []) (ulam_ "x" (int_ 2))))
  (semi_ (tensorCopyExn_ tyint_
                         (var_ "t")
                         (tensorCreateInt_ (seq_ []) (ulam_ "x" (int_ 1))))
         (tensorGetExn_ tyint_ (var_ "t") (seq_ [])))
in
utest ocamlEvalInt (generateEmptyEnv tensorCopyIntTest)
with int_ 2 using eqExpr in

let tensorCopyFloatTest =
  bind_
  (ulet_ "t" (tensorCreateFloat_ (seq_ []) (ulam_ "x" (float_ 2.))))
  (semi_ (tensorCopyExn_ tyfloat_
                         (var_ "t")
                         (tensorCreateFloat_
                                        (seq_ [])
                                        (ulam_ "x" (float_ 1.))))
         (tensorGetExn_ tyfloat_ (var_ "t") (seq_ [])))
in
utest ocamlEvalFloat (generateEmptyEnv tensorCopyFloatTest)
with float_ 2. using eqExpr in

let tensorCopyCharTest =
  bind_
  (ulet_ "t" (tensorCreate_ tychar_ (seq_ []) (ulam_ "x" (char_ '2'))))
  (semi_ (tensorCopyExn_ tychar_
                         (var_ "t")
                         (tensorCreate_ tychar_
                                        (seq_ [])
                                        (ulam_ "x" (char_ '1'))))
         (tensorGetExn_ tychar_ (var_ "t") (seq_ [])))
in
utest ocamlEvalChar (generateEmptyEnv tensorCopyCharTest)
with char_ '2' using eqExpr in

let tensorSliceIntTest =
  tensorRank_ tyint_
              (tensorSliceExn_ tyint_
                               (tensorCreateInt_
                                              (seq_ [int_ 1])
                                              (ulam_ "x" (int_ 1)))
                               (seq_ [int_ 0]))
in
utest ocamlEvalInt (generateEmptyEnv tensorSliceIntTest)
with int_ 0 using eqExpr in

let tensorSliceFloatTest =
  tensorRank_ tyfloat_
              (tensorSliceExn_ tyfloat_
                               (tensorCreateFloat_
                                              (seq_ [int_ 1])
                                              (ulam_ "x" (float_ 1.)))
                               (seq_ [int_ 0]))
in
utest ocamlEvalInt (generateEmptyEnv tensorSliceFloatTest)
with int_ 0 using eqExpr in

let tensorSliceCharTest =
  tensorRank_ tychar_
              (tensorSliceExn_ tychar_
                               (tensorCreate_ tychar_
                                              (seq_ [int_ 1])
                                              (ulam_ "x" (char_ '1')))
                               (seq_ [int_ 0]))
in
utest ocamlEvalInt (generateEmptyEnv tensorSliceCharTest)
with int_ 0 using eqExpr in

let tensorSubIntTest =
  tensorRank_ tyint_
              (tensorSubExn_ tyint_
                             (tensorCreateInt_
                                            (seq_ [int_ 1])
                                            (ulam_ "x" (int_ 1)))
                             (int_ 0)
                             (int_ 1))
in
utest ocamlEvalInt (generateEmptyEnv tensorSubIntTest)
with int_ 1 using eqExpr in

let tensorSubFloatTest =
  tensorRank_ tyfloat_
              (tensorSubExn_ tyfloat_
                             (tensorCreateFloat_
                                            (seq_ [int_ 1])
                                            (ulam_ "x" (float_ 1.)))
                             (int_ 0)
                             (int_ 1))
in
utest ocamlEvalInt (generateEmptyEnv tensorSubFloatTest)
with int_ 1 using eqExpr in

let tensorSubCharTest =
  tensorRank_ tychar_
              (tensorSubExn_ tychar_
                             (tensorCreate_ tychar_
                                            (seq_ [int_ 1])
                                            (ulam_ "x" (char_ '1')))
                             (int_ 0)
                             (int_ 1))
in
utest ocamlEvalInt (generateEmptyEnv tensorSubCharTest)
with int_ 1 using eqExpr in

let tensorIteriIntTest =
  bind_
    (ulet_ "t" (tensorCreateInt_ (seq_ []) (ulam_ "x" (int_ 1))))
    (semi_ (tensorIteri_ tyint_
                         (ulam_ "i" (ulam_ "t" unit_))
                         (var_ "t"))
           (tensorGetExn_ tyint_
                          (var_ "t")
                          (seq_ [])))
in
utest ocamlEvalInt (generateEmptyEnv tensorIteriIntTest)
with int_ 1 using eqExpr in

let tensorIteriFloatTest =
  bind_
    (ulet_ "t" (tensorCreateFloat_ (seq_ []) (ulam_ "x" (float_ 1.))))
    (semi_ (tensorIteri_ tyfloat_
                         (ulam_ "i" (ulam_ "t" unit_))
                         (var_ "t"))
           (tensorGetExn_ tyfloat_
                          (var_ "t")
                          (seq_ [])))
in
utest ocamlEvalFloat (generateEmptyEnv tensorIteriFloatTest)
with float_ 1. using eqExpr in

let tensorIteriCharTest =
  bind_
    (ulet_ "t" (tensorCreate_ tychar_ (seq_ []) (ulam_ "x" (char_ '1'))))
    (semi_ (tensorIteri_ tychar_
                         (ulam_ "i" (ulam_ "t" unit_))
                         (var_ "t"))
           (tensorGetExn_ tychar_
                          (var_ "t")
                          (seq_ [])))
in
utest ocamlEvalChar (generateEmptyEnv tensorIteriCharTest)
with char_ '1' using eqExpr in

-- Externals

let generateWithExternals = lam ast.
  match chooseAndGenerateExternals globalExternalMap ast with (m, ast) then
    generateEmptyEnv ast
  else never
in

let extZeroTest =
  bind_
    (ext_ "testZero" false tyfloat_)
    (var_ "testZero")
in
utest ocamlEvalFloat (generateWithExternals extZeroTest)
with float_ 0. using eqExpr in

let extExpTest =
  bind_
    (ext_ "testExp" false (tyarrow_ tyfloat_ tyfloat_))
    (app_ (var_ "testExp") (float_ 0.))
in
utest ocamlEvalFloat (generateWithExternals extExpTest)
with float_ 1. using eqExpr in

let extListMapTest = symbolize (
bind_
  (ext_ "testListMap"
        false
        (tyarrows_ [tyarrow_ (tyvar_ "a") (tyvar_ "b"),
                    tyseq_ (tyvar_ "a"),
                    tyseq_ (tyvar_ "b")]))
  (get_
    (appSeq_
      (var_ "testListMap")
        [ulam_ "x" (addi_ (var_ "x") (int_ 1)),
         seq_ [int_ 0, int_ 1]])
    (int_ 0)))
in
utest ocamlEvalInt (generateWithExternals extListMapTest)
with int_ 1 using eqExpr in

let extListConcatMapTest = symbolize (
bind_
  (ext_ "testListConcatMap"
        false
        (tyarrows_ [tyarrow_ (tyvar_ "a") (tyseq_ (tyvar_ "b")),
                    tyseq_ (tyvar_ "a"),
                    tyseq_ (tyvar_ "b")]))
  (get_
    (appSeq_
      (var_ "testListConcatMap")
        [ulam_ "x" (seq_ [addi_ (var_ "x") (int_ 1)]),
         seq_ [int_ 0, int_ 1]])
    (int_ 0)))
in
utest ocamlEvalInt (generateWithExternals extListConcatMapTest)
with int_ 1 using eqExpr in

-- TODO(larshum, 2021-03-06): Add tests for boot parser intrinsics
()
