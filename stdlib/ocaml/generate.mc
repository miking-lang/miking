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
include "ocaml/ast.mc"
include "ocaml/pprint.mc"
include "ocaml/compile.mc"
include "common.mc"

type GenerateEnv = {
  constrs : Map Name Type,
  records : Map (Map SID Type) Name,
  aliases : Map Name Type
}

let _emptyGenerateEnv = {
  constrs = mapEmpty nameCmp,
  records = mapEmpty (mapCmp _cmpType),
  aliases = mapEmpty nameCmp
}

let _seqOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Intrinsics.Mseq." op}

let _symbOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Intrinsics.Symb." op}

let _floatOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Intrinsics.FloatConversion." op}

let _fileOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Intrinsics.File." op}

let _ioOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Intrinsics.IO." op}

let _sysOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Intrinsics.MSys." op}

let _randOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Intrinsics.RNG." op}

let _timeOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Intrinsics.Time." op}

let _numTensorOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Tensor.Num." op}

let _noNumTensorOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Tensor.NoNum." op}

let _bootparserOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Bootparser." op}

let _mapOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Intrinsics.Mmap." op}

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

-- Construct a match expression that matches against an option
let _someName = "Option.Some"
let _noneName = "Option.None"
let _optMatch = use OCamlAst in lam target. lam somePat. lam someExpr. lam noneExpr.
  OTmMatch
  { target = target
  , arms =
    [ (OPatConExt {ident = _someName, args = [somePat]}, someExpr)
    , (OPatConExt {ident = _noneName, args = []}, noneExpr)]}
let _some = use OCamlAst in lam val. OTmConAppExt {ident = _someName, args = [val]}
let _none = use OCamlAst in OTmConAppExt {ident = _noneName, args = []}
let _if = use OCamlAst in lam cond. lam thn. lam els. OTmMatch {target = cond, arms = [(ptrue_, thn), (pfalse_, els)]}
let _tuplet = use OCamlAst in lam pats. lam val. lam body. OTmMatch {target = val, arms = [(OPatTuple {pats = pats}, body)]}

let _builtinNameMap : Map String Name =
  mapUnion
    builtinNameMap
    (mapFromList cmpString
      (map (lam s. (s, nameSym s)) ["ofArray"]))

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

lang OCamlGenerate = MExprAst + OCamlAst
  sem generate (env : GenerateEnv) =
  | TmSeq {tms = tms} ->
    app_ (nvar_ (_intrinsicName "ofArray")) (OTmArray {tms = map (generate env) tms})
  | TmMatch ({pat = (PatBool {val = true})} & t) ->
    _if (generate env t.target) (generate env t.thn) (generate env t.els)
  | TmMatch ({pat = (PatBool {val = false})} & t) ->
    _if (generate env t.target) (generate env t.els) (generate env t.thn)
  | TmMatch ({pat = PatInt {val = i}} & t) ->
    let cond = generate env (eqi_ (int_ i) t.target) in
    _if cond (generate env t.thn) (generate env t.els)
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
  | TmMatch t ->
    let tname = nameSym "_target" in
    let targetTy =
      let ty = ty t.target in
      -- If we don't know the type of the target and the pattern describes a
      -- tuple, then we assume the target has that type. We do this to
      -- eliminate the need to add type annotations when matching on tuples,
      -- which happens frequently.
      match ty with TyUnknown _ then
        match t.pat with PatRecord {bindings = bindings} then
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
    in
    match generatePat env targetTy tname t.pat with (nameMap, wrap) then
      match _mkFinalPatExpr nameMap with (pat, expr) then
        _optMatch
          (bind_ (nulet_ tname (generate env t.target)) (wrap (_some expr)))
          pat
          (generate env t.thn)
          (generate env t.els)
      else never
    else never
  | TmRecord t ->
    if mapIsEmpty t.bindings then TmRecord t
    else
      let ty = unwrapAlias env.aliases t.ty in
      match ty with TyVar {ident = ident} then
        match mapLookup ident env.constrs with Some (TyRecord {fields = fields}) then
          match mapLookup fields env.records with Some id then
            let bindings = mapMap (generate env) t.bindings in
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
        match mapLookup fields env.records with Some id then
          let rec = generate env t.rec in
          let key = sidToString t.key in
          let value = generate env t.value in
          let inlineRecordName = nameSym "rec" in
          OTmMatch {
            target = rec,
            arms = [
              ( OPatCon {ident = id, args = [npvar_ inlineRecordName]}
              , OTmConApp {ident = id, args = [
                  recordupdate_ (nvar_ inlineRecordName) key value
                ]}
              )
            ]
          }
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
    let defaultCase = lam body.
      OTmConApp {
        ident = t.ident,
        args = [generate env body]
      }
    in
    let tyBody = unwrapAlias env.aliases (ty t.body) in
    match tyBody with TyVar {ident = ident} then
      match mapLookup ident env.constrs with Some (TyRecord {fields = fields}) then
        match mapLookup fields env.records with Some id then
          let body = generate env t.body in
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
          let thn =
            -- Do not use an inline record when the constructor takes an
            -- argument of unknown type.
            match mapLookup t.ident env.constrs with Some (TyUnknown _) then
              OTmConApp {ident = t.ident, args = [generate env reconstructedRecord]}
            else
              OTmConApp {ident = t.ident, args = [reconstructedRecord]}
          in
          OTmMatch {
            target = generate env t.body,
            arms = [(OPatCon {ident = id, args = [pat]}, thn)]
          }
        else
          let msg = join ["No record type could be found in the environment. ",
                          "This was caused by an error in the type-lifting."] in
          infoErrorExit t.info msg
      else defaultCase t.body
    else defaultCase t.body
  | TmNever t ->
    let msg = "Reached a never term, which should be impossible in a well-typed program." in
    TmApp {
      lhs = OTmVarExt {ident = "failwith"},
      rhs = OTmString {text = escapeString (infoErrorString t.info msg)},
      ty = t.ty,
      info = NoInfo ()
    }
  | t -> smap_Expr_Expr (generate env) t

  /- : Pat -> (AssocMap Name Name, Expr -> Expr) -/
  sem generatePat (env : GenerateEnv) (targetTy : Type) (targetName : Name) =
  | PatNamed {ident = PWildcard _} ->
    (assocEmpty, identity)
  | PatNamed {ident = PName n} ->
    (assocInsert {eq=nameEqSym} n targetName assocEmpty, identity)
  | PatBool {val = val} ->
    let wrap = lam cont.
      _if (nvar_ targetName)
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
          infoErrorExit t.info (join ["Field ", sidToString id, " not found in record"])
      in
      match mapLookup id patNames with Some n then
        match generatePat env ty n pat with (names, innerWrap) then
          let wrap = lam cont. innerWrap cont in
          (names, wrap)
        else never
      else never
    in
    let lookupRecordFields = lam ty. lam constrs.
      match ty with TyRecord {fields = fields} then
        Some fields
      else match ty with TyVar {ident = ident} then
        match mapLookup ident constrs with Some rec then
          match rec with TyRecord {fields = fields} then
            Some fields
          else None ()
        else None ()
      else None ()
    in
    if mapIsEmpty t.bindings then
      let wrap = lam cont.
        OTmMatch {
          target = nvar_ targetName,
          arms = [(OPatTuple {pats = []}, cont)]
        }
      in
      (assocEmpty, wrap)
    else match env with {records = records, constrs = constrs} then
      let targetTy = unwrapAlias env.aliases targetTy in
      match lookupRecordFields targetTy constrs with Some fields then
        match mapLookup fields records with Some name then
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
              OTmMatch {
                target = nvar_ targetName,
                arms = [
                  (OPatCon {ident = name, args = [precord]}, foldr (lam f. lam v. f v) cont allWraps)
                ]
              }
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
          let wrap = lam cont.
            OTmMatch {
              target = nvar_ targetName,
              arms = [
                (OPatCon {ident = t.ident, args = [npvar_ conVarName]}, subwrap cont),
                (pvarw_, _none)
              ]
            }
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

let _objTyped = lam.
  use OCamlExternal in
  OTmVarExt {ident = "Obj.t"}

let _typeLiftEnvToGenerateEnv = lam typeLiftEnvMap. lam typeLiftEnv.
  use MExprAst in
  let f = lam env : GenerateEnv. lam name. lam ty.
    match ty with TyRecord {fields = fields} then
      {{env with records = mapInsert fields name env.records}
            with constrs = mapInsert name ty env.constrs}
    else match ty with TyVariant {constrs = constrs} then
      let constrs = mapMap (unwrapAlias typeLiftEnvMap) constrs in
      {env with constrs = mapUnion env.constrs constrs}
    else
      {env with aliases = mapInsert name ty env.aliases}
  in
  assocSeqFold f _emptyGenerateEnv typeLiftEnv

let _addTypeDeclarations = lam typeLiftEnvMap. lam typeLiftEnv. lam t.
  use MExprAst in
  use OCamlTypeDeclAst in
  let f = lam t. lam name. lam ty.
    match ty with TyRecord {fields = fields} then
      OTmVariantTypeDecl {
        ident = nameSym "record",
        constrs = mapInsert name ty (mapEmpty nameCmp),
        inexpr = t
      }
    else match ty with TyVariant {constrs = constrs} then
      let constrs = mapMap (unwrapAlias typeLiftEnvMap) constrs in
      if mapIsEmpty constrs then t
      else
        OTmVariantTypeDecl {
          ident = name,
          constrs = constrs,
          inexpr = t
        }
    else t
  in
  assocSeqFold f t typeLiftEnv

lang OCamlTypeDeclGenerate = MExprTypeLift
  sem generateTypeDecl (env : AssocSeq Name Type) =
  | expr ->
    let typeLiftEnvMap = mapFromList nameCmp env in
    let generateEnv = _typeLiftEnvToGenerateEnv typeLiftEnvMap env in
    let expr = _addTypeDeclarations typeLiftEnvMap env expr in
    (generateEnv, expr)
end

recursive let _isIntrinsicApp = use OCamlAst in
  lam t.
    match t with TmApp {lhs = TmConst _} then
      true
    else match t with TmApp {lhs = TmVar {ident = ident}} then
      mapMem ident builtinNameTypeMap
    else match t with TmApp {lhs = (TmApp _) & lhs} then
      _isIntrinsicApp lhs
    else false
end

let _objRepr = use OCamlAst in
  lam t. app_ (OTmVarExt {ident = "Obj.repr"}) t
let _objObj = use OCamlAst in
  lam t. app_ (OTmVarExt {ident = "Obj.obj"}) t

let _preamble =
  use OCamlAst in

  let objObjVar = lam a. _objObj (nvar_ a) in

  let mkBody = lam op. lam args.
    nulams_ args (_objRepr (foldl (lam t. lam a. t (objObjVar a)) op args))
  in

  let intr0 = lam str. lam op.
    nulet_ (_intrinsicName str) (mkBody op [])
  in

  let intr1 = lam str. lam op.
      nulet_ (_intrinsicName str)
        (let a = nameSym "a" in
         mkBody op [a])
  in

  let intr2 = lam str. lam op.
      nulet_ (_intrinsicName str)
        (let a = nameSym "a" in
         let b = nameSym "b" in
         mkBody op [a, b])
  in

  let intr3 = lam str. lam op.
      nulet_ (_intrinsicName str)
        (let a = nameSym "a" in
         let b = nameSym "b" in
         let c = nameSym "c" in
         mkBody op [a, b, c])
  in

  let intr4 = lam str. lam op.
      nulet_ (_intrinsicName str)
        (let a = nameSym "a" in
         let b = nameSym "b" in
         let c = nameSym "c" in
         let d = nameSym "d" in
         mkBody op [a, b, c, d])
  in

  bindall_
    [ intr2 "addi" addi_
    , intr2 "subi" subi_
    , intr2 "muli" muli_
    , intr2 "divi" divi_
    , intr2 "modi" modi_
    , intr1 "negi" negi_
    , intr2 "lti" lti_
    , intr2 "leqi" leqi_
    , intr2 "gti" gti_
    , intr2 "geqi" geqi_
    , intr2 "eqi" eqi_
    , intr2 "neqi" neqi_
    , intr2 "slli" slli_
    , intr2 "srli" srli_
    , intr2 "srai" srai_
    , intr2 "addf" addf_
    , intr2 "subf" subf_
    , intr2 "mulf" mulf_
    , intr2 "divf" divf_
    , intr1 "negf" negf_
    , intr2 "ltf" ltf_
    , intr2 "leqf" leqf_
    , intr2 "gtf" gtf_
    , intr2 "geqf" geqf_
    , intr2 "eqf" eqf_
    , intr2 "neqf" neqf_
    , intr1 "floorfi" (appf1_ (_floatOp "floorfi"))
    , intr1 "ceilfi" (appf1_ (_floatOp "ceilfi"))
    , intr1 "roundfi" (appf1_ (_floatOp "roundfi"))
    , intr1 "int2float" int2float_
    , intr1 "string2float" (appf1_ (_floatOp "string2float"))
    , intr2 "eqc" eqc_
    , intr1 "char2int" char2int_
    , intr1 "int2char" int2char_
    , intr2 "create" (appf2_ (_seqOp "create"))
    , intr1 "length" (appf1_ (_seqOp "length"))
    , intr2 "concat" (appf2_ (_seqOp "concat"))
    , intr2 "get" (appf2_ (_seqOp "get"))
    , intr3 "set" (appf3_ (_seqOp "set"))
    , intr2 "cons" (appf2_ (_seqOp "cons"))
    , intr2 "snoc" (appf2_ (_seqOp "snoc"))
    , intr2 "splitAt" (appf2_ (_seqOp "split_at"))
    , intr1 "reverse" (appf1_ (_seqOp "reverse"))
    , intr3 "subsequence" (appf3_ (_seqOp "subsequence"))
    , intr1 "ofArray" (appf1_ (_seqOp "Helpers.of_array"))
    , intr1 "print" (appf1_ (_ioOp "print"))
    , intr1 "dprint" (appf1_ (_ioOp "dprint"))
    , intr1 "readLine" (appf1_ (_ioOp "read_line"))
    , intr0 "argv" (_sysOp "argv")
    , intr1 "readFile" (appf1_ (_fileOp "read"))
    , intr2 "writeFile" (appf2_ (_fileOp "write"))
    , intr1 "fileExists" (appf1_ (_fileOp "exists"))
    , intr1 "deleteFile" (appf1_ (_fileOp "delete"))
    , intr1 "error" (appf1_ (_sysOp "error"))
    , intr1 "exit" (appf1_ (_sysOp "exit"))
    , intr1 "command" (appf1_ (_sysOp "command"))
    , intr2 "eqsym" (appf2_ (_symbOp "eqsym"))
    , intr1 "gensym" (appf1_ (_symbOp "gensym"))
    , intr1 "sym2hash" (appf1_ (_symbOp "hash"))
    , intr2 "randIntU" (appf2_ (_randOp "int_u"))
    , intr1 "randSetSeed" (appf1_ (_randOp "set_seed"))
    , intr1 "wallTimeMs" (appf1_ (_timeOp "get_wall_time_ms"))
    , intr1 "sleepMs" (appf1_ (_timeOp "sleep_ms"))
    , intr1 "bootParserParseMExprString" (appf1_ (_bootparserOp "parseMExprString"))
    , intr1 "bootParserParseMCoreFile" (appf1_ (_bootparserOp "parseMCoreFile"))
    , intr1 "bootParserGetId" (appf1_ (_bootparserOp "getId"))
    , intr2 "bootParserGetTerm" (appf2_ (_bootparserOp "getTerm"))
    , intr2 "bootParserGetType" (appf2_ (_bootparserOp "getType"))
    , intr2 "bootParserGetString" (appf2_ (_bootparserOp "getString"))
    , intr2 "bootParserGetInt" (appf2_ (_bootparserOp "getInt"))
    , intr2 "bootParserGetFloat" (appf2_ (_bootparserOp "getFloat"))
    , intr2 "bootParserGetListLength" (appf2_ (_bootparserOp "getListLength"))
    , intr2 "bootParserGetConst" (appf2_ (_bootparserOp "getConst"))
    , intr2 "bootParserGetPat" (appf2_ (_bootparserOp "getPat"))
    , intr2 "bootParserGetInfo" (appf2_ (_bootparserOp "getInfo"))
    , intr1 "mapEmpty" (appf1_ (_mapOp "empty"))
    , intr3 "mapInsert" (appf3_ (_mapOp "insert"))
    , intr2 "mapRemove" (appf2_ (_mapOp "remove"))
    , intr2 "mapFindWithExn" (appf2_ (_mapOp "find"))
    , intr3 "mapFindOrElse" (appf3_ (_mapOp "find_or_else"))
    , intr4 "mapFindApplyOrElse" (appf4_ (_mapOp "find_apply_or_else"))
    , intr1 "mapBindings" (appf1_ (_mapOp "bindings"))
    , intr1 "mapSize" (appf1_ (_mapOp "size"))
    , intr2 "mapMem" (appf2_ (_mapOp "mem"))
    , intr2 "mapAny" (appf2_ (_mapOp "any"))
    , intr2 "mapMap" (appf2_ (_mapOp "map"))
    , intr2 "mapMapWithKey" (appf2_ (_mapOp "map_with_key"))
    , intr3 "mapFoldWithKey" (appf3_ (_mapOp "fold_with_key"))
    , intr3 "mapEq" (appf3_ (_mapOp "eq"))
    , intr3 "mapCmp" (appf3_ (_mapOp "cmp"))
    , intr3 "mapGetCmpFun" (appf3_ (_mapOp "key_cmp"))
    , intr1 "ref" ref_
    , intr1 "deref" deref_
    , intr2 "modref" modref_
    ]

lang OCamlObjWrap = MExprAst + OCamlAst
  sem intrinsic2name =
  | CAddi _ -> nvar_ (_intrinsicName "addi")
  | CSubi _ -> nvar_ (_intrinsicName "subi")
  | CMuli _ -> nvar_ (_intrinsicName "muli")
  | CDivi _ -> nvar_ (_intrinsicName "divi")
  | CModi _ -> nvar_ (_intrinsicName "modi")
  | CNegi _ -> nvar_ (_intrinsicName "negi")
  | CLti _ -> nvar_ (_intrinsicName "lti")
  | CLeqi _ -> nvar_ (_intrinsicName "leqi")
  | CGti _ -> nvar_ (_intrinsicName "gti")
  | CGeqi _ -> nvar_ (_intrinsicName "geqi")
  | CEqi _ -> nvar_ (_intrinsicName "eqi")
  | CNeqi _ -> nvar_ (_intrinsicName "neqi")
  | CSlli _ -> nvar_ (_intrinsicName "slli")
  | CSrli _ -> nvar_ (_intrinsicName "srli")
  | CSrai _ -> nvar_ (_intrinsicName "srai")
  | CAddf _ -> nvar_ (_intrinsicName "addf")
  | CSubf _ -> nvar_ (_intrinsicName "subf")
  | CMulf _ -> nvar_ (_intrinsicName "mulf")
  | CDivf _ -> nvar_ (_intrinsicName "divf")
  | CNegf _ -> nvar_ (_intrinsicName "negf")
  | CLtf _ -> nvar_ (_intrinsicName "ltf")
  | CLeqf _ -> nvar_ (_intrinsicName "leqf")
  | CGtf _ -> nvar_ (_intrinsicName "gtf")
  | CGeqf _ -> nvar_ (_intrinsicName "geqf")
  | CEqf _ -> nvar_ (_intrinsicName "eqf")
  | CNeqf _ -> nvar_ (_intrinsicName "neqf")
  | CFloorfi _ -> nvar_ (_intrinsicName "floorfi")
  | CCeilfi _ -> nvar_ (_intrinsicName "ceilfi")
  | CRoundfi _ -> nvar_ (_intrinsicName "roundfi")
  | CInt2float _ -> nvar_ (_intrinsicName "int2float")
  | CString2float _ -> nvar_ (_intrinsicName "string2float")
  | CEqc _ -> nvar_ (_intrinsicName "eqc")
  | CChar2Int _ -> nvar_ (_intrinsicName "char2int")
  | CInt2Char _ -> nvar_ (_intrinsicName "int2char")
  | CCreate _ -> nvar_ (_intrinsicName "create")
  | CLength _ -> nvar_ (_intrinsicName "length")
  | CConcat _ -> nvar_ (_intrinsicName "concat")
  | CGet _ -> nvar_ (_intrinsicName "get")
  | CSet _ -> nvar_ (_intrinsicName "set")
  | CCons _ -> nvar_ (_intrinsicName "cons")
  | CSnoc _ -> nvar_ (_intrinsicName "snoc")
  | CSplitAt _ -> nvar_ (_intrinsicName "splitAt")
  | CReverse _ -> nvar_ (_intrinsicName "reverse")
  | CSubsequence _ -> nvar_ (_intrinsicName "subsequence")
  | CPrint _ -> nvar_ (_intrinsicName "print")
  | CDPrint _ -> nvar_ (_intrinsicName "dprint")
  | CReadLine _ -> nvar_ (_intrinsicName "readLine")
  | CArgv _ -> nvar_ (_intrinsicName "argv")
  | CFileRead _ -> nvar_ (_intrinsicName "readFile")
  | CFileWrite _ -> nvar_ (_intrinsicName "writeFile")
  | CFileExists _ -> nvar_ (_intrinsicName "fileExists")
  | CFileDelete _ -> nvar_ (_intrinsicName "deleteFile")
  | CError _ -> nvar_ (_intrinsicName "error")
  | CExit _ -> nvar_ (_intrinsicName "exit")
  | CCommand _ -> nvar_ (_intrinsicName "command")
  | CEqsym _ -> nvar_ (_intrinsicName "eqsym")
  | CGensym _ -> nvar_ (_intrinsicName "gensym")
  | CSym2hash _ -> nvar_ (_intrinsicName "sym2hash")
  | CRandIntU _ -> nvar_ (_intrinsicName "randIntU")
  | CRandSetSeed _ -> nvar_ (_intrinsicName "randSetSeed")
  | CWallTimeMs _ -> nvar_ (_intrinsicName "wallTimeMs")
  | CSleepMs _ -> nvar_ (_intrinsicName "sleepMs")
  | CMapEmpty _ -> nvar_ (_intrinsicName "mapEmpty")
  | CMapInsert _ -> nvar_ (_intrinsicName "mapInsert")
  | CMapRemove _ -> nvar_ (_intrinsicName "mapRemove")
  | CMapFindWithExn _ -> nvar_ (_intrinsicName "mapFindWithExn")
  | CMapFindOrElse _ -> nvar_ (_intrinsicName "mapFindOrElse")
  | CMapFindApplyOrElse _ -> nvar_ (_intrinsicName "mapFindApplyOrElse")
  | CMapBindings _ -> nvar_ (_intrinsicName "mapBindings")
  | CMapSize _ -> nvar_ (_intrinsicName "mapSize")
  | CMapMem _ -> nvar_ (_intrinsicName "mapMem")
  | CMapAny _ -> nvar_ (_intrinsicName "mapAny")
  | CMapMap _ -> nvar_ (_intrinsicName "mapMap")
  | CMapMapWithKey _ -> nvar_ (_intrinsicName "mapMapWithKey")
  | CMapFoldWithKey _ -> nvar_ (_intrinsicName "mapFoldWithKey")
  | CMapEq _ -> nvar_ (_intrinsicName "mapEq")
  | CMapCmp _ -> nvar_ (_intrinsicName "mapCmp")
  | CMapGetCmpFun _ -> nvar_ (_intrinsicName "mapGetCmpFun")
  | CTensorCreate _ -> nvar_ (_intrinsicName "tensorCreate")
  | CTensorGetExn _ -> nvar_ (_intrinsicName "tensorGetExn")
  | CTensorSetExn _ -> nvar_ (_intrinsicName "tensorSetExn")
  | CTensorRank _ -> nvar_ (_intrinsicName "tensorRank")
  | CTensorShape _ -> nvar_ (_intrinsicName "tensorShape")
  | CTensorReshapeExn _ -> nvar_ (_intrinsicName "tensorReshapeExn")
  | CTensorCopyExn _ -> nvar_ (_intrinsicName "tensorCopyExn")
  | CTensorSliceExn _ -> nvar_ (_intrinsicName "tensorSliceExn")
  | CTensorSubExn _ -> nvar_ (_intrinsicName "tensorSubExn")
  | CTensorIteri _ -> nvar_ (_intrinsicName "tensorIteri")
  | CBootParserParseMExprString _ -> nvar_ (_intrinsicName "bootParserParseMExprString")
  | CBootParserGetId _ -> nvar_ (_intrinsicName "bootParserGetId")
  | CBootParserGetTerm _ -> nvar_ (_intrinsicName "bootParserGetTerm")
  | CBootParserGetString _ -> nvar_ (_intrinsicName "bootParserGetString")
  | CBootParserGetInt _ -> nvar_ (_intrinsicName "bootParserGetInt")
  | CBootParserGetFloat _ -> nvar_ (_intrinsicName "bootParserGetFloat")
  | CBootParserGetListLength _ -> nvar_ (_intrinsicName "bootParserGetListLength")
  | CBootParserGetConst _ -> nvar_ (_intrinsicName "bootParserGetConst")
  | CBootParserGetPat _ -> nvar_ (_intrinsicName "bootParserGetPat")
  | CBootParserGetInfo _ -> nvar_ (_intrinsicName "bootParserGetInfo")
  | CRef _ -> nvar_ (_intrinsicName "ref")
  | CModRef _ -> nvar_ (_intrinsicName "modref")
  | CDeRef _ -> nvar_ (_intrinsicName "deref")
  | t -> dprintLn t; error "Intrinsic not implemented"

  sem objWrapRec (isApp : Bool) =
  | (TmConst {val = (CInt _) | (CFloat _) | (CChar _) | (CBool _)}) & t ->
    _objRepr t
  | TmConst {val = c} -> intrinsic2name c
  | TmApp t ->
    if _isIntrinsicApp (TmApp t) then
      TmApp {{t with lhs = objWrapRec true t.lhs}
                with rhs = _objRepr (objWrapRec false t.rhs)}
    else
      TmApp {{t with lhs =
                  if isApp then
                    objWrapRec true t.lhs
                  else
                    _objObj (_objRepr (objWrapRec true t.lhs))}
                with rhs = objWrapRec false t.rhs}
  | TmRecord t ->
    if mapIsEmpty t.bindings then
      _objRepr (TmRecord t)
    else
      let bindings = mapMap (lam expr. objWrapRec false expr) t.bindings in
      TmRecord {t with bindings = bindings}
  | (OTmArray {tms = tms}) & t ->
    let isConstArray = all (lam expr.
      match expr with TmConst _ then true else false) tms in
    if isConstArray then
      _objRepr t
    else
      _objRepr (smap_Expr_Expr (objWrapRec false) t)
  | (OTmConApp _) & t -> _objRepr (smap_Expr_Expr (objWrapRec false) t)
  | OTmMatch t ->
    _objObj
    (OTmMatch {{t with target = _objObj (_objRepr (objWrapRec false t.target))}
                  with arms = map (lam p : (Pat, Expr).
                                    (p.0, _objRepr (objWrapRec false p.1)))
                                  t.arms})
  | t -> smap_Expr_Expr (objWrapRec false) t

  sem objWrap =
  | OTmVariantTypeDecl t ->
    OTmVariantTypeDecl {t with inexpr = objWrap t.inexpr}
  | t -> _objObj (objWrapRec false t)
end

lang OCamlTest = OCamlGenerate + OCamlTypeDeclGenerate + OCamlPrettyPrint +
                 MExprSym + ConstEq + IntEq + BoolEq + CharEq + FloatEq +
                 MExprTypeAnnot + OCamlObjWrap

mexpr

use OCamlTest in

-- Test semantics

-- Parse helper
let parseAsMExpr = lam s.
  use MExprParser in parseExpr (initPos "") s
in

-- NOTE(oerikss, 2021-03-05): We pre- pretty-print the preamble here to make
-- the test run faster. This is an ugly hack!
let preambleStr =
  let str = expr2str (bind_ _preamble (int_ 0)) in
  let len = length str in
  subsequence str 0 (subi len 1)
in

-- NOTE(larshum, 2021-03-08): Adds the preamble to the top of a given term,
-- but places it after all variant type declarations.
recursive let withPreamble = lam t.
  match t with OTmVariantTypeDecl tt then
    OTmVariantTypeDecl {tt with inexpr = withPreamble tt.inexpr}
  else
    OTmPreambleText {text = preambleStr, inexpr = t}
in

-- Evaluates OCaml expressions [strConvert] given as string, applied
-- to [p], and parses it as a mexpr expression.
let ocamlEval = lam ast.
  let ast = withPreamble ast in
  let res = ocamlCompileWithConfig {warnings=false} (expr2str ast) in
  let out = (res.run "" []).stdout in
  res.cleanup ();
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
  else app_ printTerm ast
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
    eval {env = builtinEnv} mexprAst
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
  else error "Unsupported value"
in

let generateEmptyEnv = lam t.
  objWrap (generate _emptyGenerateEnv t)
in

let generateTypeAnnotated = lam t.
  match typeLift (typeAnnot t) with (env, t) then
    match generateTypeDecl env t with (env, t) then
      objWrap (generate env t)
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
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 123) (int_ 90) (var_ "m"))
  , mapFindWithExn_ (int_ 42) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapInsertFindTest)
with int_ 1 using eqExpr in

let mapMemTrueTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapMem_ (int_ 42) (var_ "m")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapMemTrueTest)
with true_ using eqExpr in

let mapMemFalseTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapMem_ (int_ 78) (var_ "m")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapMemFalseTest)
with false_ using eqExpr in

let mapRemoveTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , ulet_ "m" (mapRemove_ (int_ 42) (var_ "m"))
  , mapMem_ (int_ 42) (var_ "m")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapRemoveTest)
with false_ using eqExpr in

let mapFindOrElseTrueTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapFindOrElse_ (ulam_ "" (int_ 123)) (int_ 42) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapFindOrElseTrueTest)
with int_ 1 using eqExpr in

let mapFindOrElseFalseTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapFindOrElse_ (ulam_ "" (int_ 123)) (int_ 3) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapFindOrElseFalseTest)
with int_ 123 using eqExpr in

let mapFindApplyOrElseTrueTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapFindApplyOrElse_
      (ulam_ "x" (addi_ (var_ "x") (int_ 1)))
      (ulam_ "" (int_ 7))
      (int_ 42) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapFindApplyOrElseTrueTest)
with int_ 2 using eqExpr in

let mapFindApplyOrElseFalseTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapFindApplyOrElse_
     (ulam_ "x" (addi_ (var_ "x") (int_ 1)))
     (ulam_ "" (int_ 7))
     (int_ 3) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapFindApplyOrElseFalseTest)
with int_ 7 using eqExpr in

let mapSizeEmptyTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , mapSize_ (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapSizeEmptyTest)
with int_ 0 using eqExpr in

let mapSizeTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 100) (int_ 567) (var_ "m"))
  , mapSize_ (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapSizeTest)
with int_ 2 using eqExpr in

let mapAnyTrueTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , mapAny_ (ulam_ "k" (ulam_ "v" (geqi_ (var_ "k") (var_ "v")))) (var_ "m")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapAnyTrueTest)
with true_ using eqExpr in

let mapAnyFalseTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 0) (negi_ (int_ 1)) (var_ "m"))
  , mapAny_ (ulam_ "k" (ulam_ "v" (eqi_ (var_ "k") (var_ "v")))) (var_ "m")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapAnyFalseTest)
with false_ using eqExpr in

let mapMapTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 3) (int_ 56) (var_ "m"))
  , ulet_ "m" (mapMap_ (ulam_ "v" (addi_ (int_ 44) (var_ "v"))) (var_ "m"))
  , mapFindWithExn_ (int_ 3) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapMapTest)
with int_ 100 using eqExpr in

let mapMapWithKeyTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
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
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 3) (int_ 56) (var_ "m"))
  , mapFoldWithKey_
      (ulam_ "acc" (ulam_ "k" (ulam_ "v"
        (addi_ (var_ "acc") (addi_ (var_ "k") (var_ "v")))))) (int_ 0) (var_ "m")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapFoldWithKeyTest)
with int_ 103 using eqExpr in

let mapFoldWithKeyNonAssociativeTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
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
  [ ulet_ "m1" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "m2" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m2" (mapInsert_ (int_ 42) (int_ 2) (var_ "m2"))
  , ulet_ "m2" (mapInsert_ (int_ 3) (int_ 56) (var_ "m2"))
  , mapEq_ (ulam_ "v1" (ulam_ "v2"
      (eqi_ (var_ "v1") (var_ "v2")))) (var_ "m1") (var_ "m2")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapEqTrueTest)
with true_ using eqExpr in

let mapEqFalseTest = bindall_
  [ ulet_ "m1" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "m2" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m2" (mapInsert_ (int_ 42) (int_ 3) (var_ "m2"))
  , ulet_ "m2" (mapInsert_ (int_ 3) (int_ 56) (var_ "m2"))
  , mapEq_ (ulam_ "v1" (ulam_ "v2"
      (eqi_ (var_ "v1") (var_ "v2")))) (var_ "m1") (var_ "m2")
  ] in
utest ocamlEvalBool (generateEmptyEnv mapEqFalseTest)
with false_ using eqExpr in

let mapCmpEqTest = bindall_
  [ ulet_ "m1" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "m2" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m2" (mapInsert_ (int_ 42) (int_ 2) (var_ "m2"))
  , ulet_ "m2" (mapInsert_ (int_ 3) (int_ 56) (var_ "m2"))
  , mapCmp_ (ulam_ "v1" (ulam_ "v2"
      (subi_ (var_ "v1") (var_ "v2")))) (var_ "m1") (var_ "m2")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapCmpEqTest)
with int_ 0 using eqExpr in

let mapCmpNEqTest = bindall_
  [ ulet_ "m1" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "m2" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "m2" (mapInsert_ (int_ 42) (int_ 1) (var_ "m2"))
  , ulet_ "m2" (mapInsert_ (int_ 3) (int_ 56) (var_ "m2"))
  , mapCmp_ (ulam_ "v1" (ulam_ "v2"
      (subi_ (var_ "v1") (var_ "v2")))) (var_ "m1") (var_ "m2")
  ] in
utest ocamlEvalInt (generateEmptyEnv mapCmpNEqTest)
with int_ 1 using eqExpr in

let mapGetCmpFunTest = bindall_
  [ ulet_ "m" (mapEmpty_ (const_ (CSubi ())))
  , ulet_ "f" (mapGetCmpFun_ (var_ "m"))
  , appf2_ (var_ "f") (int_ 12) (int_ 2)
  ] in
utest ocamlEvalInt (generateEmptyEnv mapGetCmpFunTest)
with int_ 10 using eqExpr in

-- mapBindings
let mapBindingsTest = (bindall_
  [ ulet_ "m1" (mapEmpty_ (const_ (CSubi ())))
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
  [ ulet_ "m1" (mapEmpty_ (const_ (CSubi ())))
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

-- TODO(larshum, 2021-03-06): Add tests for boot parser, and tensor
-- intrinsics

()
