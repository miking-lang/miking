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
  sem getPatName : PatName -> Option Name
  sem getPatName =
  | PWildcard _ -> None ()
  | PName id -> Some id

  sem getPatNamedId : Pat -> Option Name
  sem getPatNamedId =
  | PatNamed {ident = id} -> getPatName id
  | p ->
    errorSingle [infoPat p] "Nested pattern found in OCaml code generation"

  sem bindPat : Expr -> Expr -> Pat -> Expr
  sem bindPat acc target =
  | p ->
    match getPatNamedId p with Some patId then
      bind_ (nulet_ patId target) acc
    else acc

  sem generateMatchBaseCase : GenerateEnv -> Expr -> Expr
  sem generateMatchBaseCase env =
  | TmMatch (t & {pat = PatNamed {ident = PWildcard _}}) -> generate env t.thn
  | TmMatch (t & {pat = PatNamed {ident = PName id}}) ->
    bind_
      (nulet_ id (generate env t.target))
      (generate env t.thn)
  | TmMatch (t & {pat = PatBool {val = val}}) ->
    let thn = generate env t.thn in
    let els = generate env t.els in
    _if (objMagic (generate env t.target))
      (if val then thn else els)
      (objMagic (if val then els else thn))
  | TmMatch (t & {pat = PatInt {val = val}}) ->
    _if (eqi_ (objMagic (generate env t.target)) (int_ val))
      (generate env t.thn) (objMagic (generate env t.els))
  | TmMatch (t & {pat = PatChar {val = val}}) ->
    _if (eqc_ (objMagic (generate env t.target)) (char_ val))
      (generate env t.thn) (objMagic (generate env t.els))
  | TmMatch (t & {pat = PatSeqTot {pats = pats}}) ->
    let n = length pats in
    let targetId = nameSym "_target" in
    -- Bind the variables in the sequence pattern before evaluating the then
    -- branch expression, in case the branch is taken.
    let thn =
      foldl
        (lam acc. lam pi.
          match pi with (pat, idx) in
          bindPat acc (get_ (nvar_ targetId) (int_ idx)) pat)
        (generate env t.thn) (mapi (lam i. lam p. (p, i)) pats) in
    let cond =
      let target = nvar_ targetId in
      if eqi n 0 then null_ target
      else eqi_ (length_ target) (int_ n)
    in
    bind_
      (nulet_ targetId (objMagic (generate env t.target)))
      (_if cond thn (objMagic (generate env t.els)))
  | TmMatch (t & {pat = PatSeqEdge {prefix = prefix, middle = middle, postfix = postfix}}) ->
    let n1 = length prefix in
    let n2 = length postfix in
    let targetId = nameSym "_target" in
    let lenId = nameSym "n" in
    let cond = _isLengthAtLeast (nvar_ targetId) (addi_ (int_ n1) (int_ n2)) in
    -- NOTE(larshum, 2022-12-20): Add a binding for each of the non-wildcard
    -- patterns in the sequence pattern, starting with the postfix and prefix,
    -- followed by the middle.
    let prefixIndexedPats = mapi (lam i. lam p. (p, int_ i)) prefix in
    let postfixIndexedPats =
      mapi
        (lam i. lam p. (p, subi_ (nvar_ lenId) (int_ (addi i 1))))
        (reverse postfix) in
    let thn =
      let thn = generate env t.thn in
      let thn =
        foldl
          (lam acc. lam pi.
            match pi with (pat, idx) in
            bindPat acc (get_ (nvar_ targetId) idx) pat)
          thn (concat postfixIndexedPats prefixIndexedPats) in
      match middle with PName id then
        let midExpr =
          subsequence_ (nvar_ targetId) (int_ n1)
            (subi_ (nvar_ lenId) (addi_ (int_ n1) (int_ n2)))
        in
        bind_ (nulet_ id midExpr) thn
      else thn
    in
    bindall_ [
      nulet_ targetId (objMagic (generate env t.target)),
      nulet_ lenId (length_ (nvar_ targetId)),
      _if cond thn (objMagic (generate env t.els))]
  | TmMatch (t & {pat = PatRecord {bindings = bindings, ty = ty}}) ->
    if mapIsEmpty bindings then
      generate env t.thn
    else
      match env with {records = records, constrs = constrs} in
      let targetTy = typeUnwrapAlias env.aliases ty in
      match lookupRecordFields targetTy constrs with Some fields then
        let fieldTypes = ocamlTypedFields fields in
        match mapLookup fieldTypes records with Some name then
          let recPat = OPatRecord {bindings = bindings} in
          let conPat = OPatCon {ident = name, args = [recPat]} in
          OTmMatch {
            target = objMagic (generate env t.target),
            arms = [(conPat, generate env t.thn)]}
        else
          let msg = join [
            "The OCaml code generation failed due to a bug in the ",
            "type-lifting.\nThe match pattern refers to a record type that ",
            "was not included in the type-lifting."] in
          errorSingle [t.info] msg
      else
        let msg = join [
          "Pattern refers to an unknown record type.\n",
          "The type must be known in the OCaml code generation."] in
        errorSingle [t.info] msg
  | TmMatch (t & {pat = PatCon {ident = ident, subpat = subpat}}) ->
    match env with {constrs = constrs} in
    match mapLookup ident constrs with Some innerTy then
      let containsRecord = match innerTy with TyRecord _ then true else false in
      let targetId = nameSym "_target" in
      -- NOTE(larshum, 2022-12-20): We make use of inline records in
      -- constructors when compiling to OCaml. In this case, we cannot access
      -- them directly, so we access them via the constructor directly.
      let ocamlSubpat =
        let patName =
          if containsRecord then PWildcard ()
          else
            match getPatNamedId subpat with Some id then PName id
            else PWildcard ()
        in
        PatNamed {ident = patName, info = infoPat subpat, ty = tyPat subpat}
      in
      let thn =
        let thn = generate env t.thn in
        if containsRecord then
          match getPatNamedId subpat with Some id then
            bind_ (nulet_ id (nvar_ targetId)) thn
          else thn
        else thn
      in
      let conPat = OPatCon {ident = ident, args = [ocamlSubpat]} in
      bind_
        (nulet_ targetId (objMagic (generate env t.target)))
        (OTmMatch {target = nvar_ targetId,
                   arms = [ (conPat, thn)
                          , (pvarw_, objMagic (generate env t.els)) ]})
    else
      let msg = join [
        "Match pattern refers to unknown type constructor ",
        nameGetStr ident] in
      errorSingle [t.info] msg
  | TmMatch {pat = PatAnd _ | PatOr _ | PatNot _, info = info} ->
    errorSingle [info] "Regular patterns are not supported by OCaml backend"
  | TmMatch t ->
    errorSingle [t.info] "Match expression is not supported by OCaml backend"

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
  | TmMatch t -> generateMatchBaseCase env (TmMatch t)
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
