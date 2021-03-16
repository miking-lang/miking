include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
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

type GenerateEnv = {
  constrs : Map Name Type,
  records : Map (Map SID Type) Name
}

let _emptyGenerateEnv = {
  constrs = mapEmpty nameCmp,
  records = mapEmpty (mapCmp _cmpType)
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

let _numTensorOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Tensor.Num." op}

let _noNumTensorOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Tensor.NoNum." op}

let _bootparserOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Bootparser." op}

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

let _addiName = nameSym "addi"
let _subiName = nameSym "subi"
let _muliName = nameSym "muli"
let _diviName = nameSym "divi"
let _modiName = nameSym "modi"
let _negiName = nameSym "negi"
let _ltiName = nameSym "lti"
let _leqiName = nameSym "leqi"
let _gtiName = nameSym "gti"
let _geqiName = nameSym "geqi"
let _eqiName = nameSym "eqi"
let _neqiName = nameSym "neqi"
let _slliName = nameSym "slli"
let _srliName = nameSym "srli"
let _sraiName = nameSym "srai"
let _addfName = nameSym "addf"
let _subfName = nameSym "subf"
let _mulfName = nameSym "mulf"
let _divfName = nameSym "divf"
let _negfName = nameSym "negf"
let _ltfName = nameSym "ltf"
let _leqfName = nameSym "leqf"
let _gtfName = nameSym "gtf"
let _geqfName = nameSym "geq"
let _eqfName = nameSym "eqf"
let _neqfName = nameSym "neqf"
let _floorfiName = nameSym "floorfi"
let _ceilfiName = nameSym "ceilfi"
let _roundfiName = nameSym "roundfi"
let _int2floatName = nameSym "int2float"
let _string2floatName = nameSym "string2float"
let _eqcName = nameSym "eqc"
let _char2intName = nameSym "char2int"
let _int2charName = nameSym "int2char"
let _createName = nameSym "create"
let _lengthName = nameSym "length"
let _concatName = nameSym "concat"
let _getName = nameSym "get"
let _setName = nameSym "set"
let _consName = nameSym "cons"
let _snocName = nameSym "snoc"
let _splitAtName = nameSym "splitAt"
let _reverseName = nameSym "reverse"
let _subsequenceName = nameSym "subsequence"
let _ofArrayName = nameSym "of_array"
let _printName = nameSym "print"
let _readLineName = nameSym "readLine"
let _readBytesAsStringName = nameSym "readBytesAsString"
let _argvName = nameSym "argv"
let _readFileName = nameSym "readFile"
let _writeFileName = nameSym "writeFile"
let _fileExistsName = nameSym "fileExists"
let _deleteFileName = nameSym "deleteFile"
let _errorName = nameSym "error"
let _exitName = nameSym "exit"
let _eqsymName = nameSym "eqsym"
let _gensymName = nameSym "gensym"
let _sym2hashName = nameSym "sym2hash"
let _randIntUName = nameSym "randIntU"
let _randSetSeedName = nameSym "randSetSeed"
let _wallTimeMsName = nameSym "wallTime"
let _sleepMsName = nameSym "sleepMs"
let _mapEmptyName = nameSym "mapEmpty"
let _mapInsertName = nameSym "mapInsert"
let _mapRemoveName = nameSym "mapRemove"
let _mapFindName = nameSym "mapFind"
let _mapAnyName = nameSym "mapAny"
let _mapMemName = nameSym "mapMem"
let _mapMapName = nameSym "mapMap"
let _mapMapWithKeyName = nameSym "mapMapWithKey"
let _mapBindingsName = nameSym "mapBindings"
let _tensorCreateName = nameSym "tensorCreate"
let _tensorGetExnName = nameSym "tensorGetExn"
let _tensorSetExnName = nameSym "tensorSetExn"
let _tensorRankName = nameSym "tensorRank"
let _tensorShapeName = nameSym "tensorShape"
let _tensorReshapeExnName = nameSym "tensorReshapeExn"
let _tensorCopyExnName = nameSym "tensorCopyExn"
let _tensorSliceExnName = nameSym "tensorSliceExn"
let _tensorSubExnName = nameSym "tensorSubExn"
let _tensorIteriName = nameSym "tensorIteri"
let _bootParserParseMExprStringName = nameSym "bootParserParseMExprString"
let _bootParserGetIdName = nameSym "bootParserGetId"
let _bootParserGetTermName = nameSym "bootParserGetTerm"
let _bootParserGetStringName = nameSym "bootParserGetString"
let _bootParserGetIntName = nameSym "bootParserGetInt"
let _bootParserGetFloatName = nameSym "bootParserGetFloat"
let _bootParserGetListLengthName = nameSym "bootParserGetListLength"
let _bootParserGetConstName = nameSym "bootParserGetConst"
let _bootParserGetPatName = nameSym "bootParserGetPat"
let _bootParserGetInfoName = nameSym "bootParserGetInfo"

lang OCamlGenerate = MExprAst + OCamlAst
  sem generate (env : GenerateEnv) =
  | TmSeq {tms = tms} ->
    app_ (nvar_ _ofArrayName) (OTmArray {tms = map (generate env) tms})
  | TmMatch {target = target, pat = pat, thn = thn, els = els} ->
    let tname = nameSym "_target" in
    match generatePat env (ty target) tname pat with (nameMap, wrap) then
      match _mkFinalPatExpr nameMap with (pat, expr) then
        _optMatch
          (bind_ (nulet_ tname (generate env target)) (wrap (_some expr)))
          pat
          (generate env thn)
          (generate env els)
      else never
    else never
  | TmRecord t ->
    if mapIsEmpty t.bindings then TmRecord t
    else
      match t.ty with TyVar {ident = ident} then
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
  | TmType t -> generate env t.inexpr
  | TmConDef t -> generate env t.inexpr
  | TmConApp t ->
    let body =
      match t.body with TmRecord r then
        TmRecord {r with bindings = mapMap (generate env) r.bindings}
      else generate env t.body
    in
    OTmConApp {
      ident = t.ident,
      args = [body]
    }
  | t -> smap_Expr_Expr (generate env) t

  /- : Pat -> (AssocMap Name Name, Expr -> Expr) -/
  sem generatePat (env : GenerateEnv) (targetTy : Type) (targetName : Name) =
  | PatNamed {ident = PWildcard _} -> (assocEmpty, identity)
  | PatNamed {ident = PName n} -> (assocInsert {eq=nameEqSym} n targetName assocEmpty, identity)
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
    let genOne = lam i. lam pat.
      let n = nameSym "_seqElem" in
      match generatePat env targetTy n pat with (names, innerWrap) then
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
    let genOne = lam targetName. lam i. lam pat.
      let n = nameSym "_seqElem" in
      match generatePat env targetTy n pat with (names, innerWrap) then
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
          infoErrorExit t.info (join ["Field ", id, " not found in record"])
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
        match mapLookup ident constrs with Some (TyRecord {fields = fields}) then
          Some fields
        else None ()
      else None ()
    in
    match env with {records = records, constrs = constrs} then
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

let _typeLiftEnvToGenerateEnv = lam typeLiftEnv.
  use MExprAst in
  let f = lam env. lam entry.
    match entry with (name, ty) then
      match ty with TyRecord {fields = fields} then
        {{env with records = mapInsert fields name env.records}
              with constrs = mapInsert name ty env.constrs}
      else match ty with TyVariant {constrs = constrs} then
        {env with constrs = mapUnion env.constrs constrs}
      else env
    else never
  in
  foldl f _emptyGenerateEnv typeLiftEnv

let _addTypeDeclarations = lam typeLiftEnv. lam t.
  use MExprAst in
  use OCamlTypeDeclAst in
  let f = lam t. lam envEntry.
    match envEntry with (name, ty) then
      match ty with TyRecord {fields = fields} then
        let objTypedFields = mapMap _objTyped fields in
        OTmVariantTypeDecl {
          ident = nameSym "record",
          constrs = mapInsert name ty (mapEmpty nameCmp),
          inexpr = t
        }
      else match ty with TyVariant {constrs = constrs} then
        OTmVariantTypeDecl {
          ident = name,
          constrs = constrs,
          inexpr = t
        }
      else t
    else never
  in
  foldl f t typeLiftEnv

lang OCamlTypeDeclGenerate = MExprTypeLift
  sem generateTypeDecl =
  | expr ->
    match typeLift expr with (env, t) then
      let generateEnv = _typeLiftEnvToGenerateEnv env in
      let t = _addTypeDeclarations env t in
      (generateEnv, t)
    else never
end

recursive let _isIntrinsicApp = use OCamlAst in
  lam t.
    match t with TmApp {lhs = TmConst _} then
      true
    else match t with TmApp {lhs = (TmApp _) & lhs} then
      _isIntrinsicApp lhs
    else false
end

let _objRepr = use OCamlAst in
  lam t. app_ (OTmVarExt {ident = "Obj.repr"}) t
let _objObj = use OCamlAst in
  lam t. app_ (OTmVarExt {ident = "Obj.obj"}) t

let _preamble =
  let objObjVar = lam a. _objObj (nvar_ a) in

  let mkBody = lam op. lam args.
    nulams_ args (_objRepr (foldl (lam t. lam a. t (objObjVar a)) op args))
  in

  let intr0 = lam name. lam op.
    nulet_ name (mkBody op [])
  in

  let intr1 = lam name. lam op.
      nulet_ name
        (let a = nameSym "a" in
         mkBody op [a])
  in

  let intr2 = lam name. lam op.
      nulet_ name
        (let a = nameSym "a" in
         let b = nameSym "b" in
         mkBody op [a, b])
  in

  let intr3 = lam name. lam op.
      nulet_ name
        (let a = nameSym "a" in
         let b = nameSym "b" in
         let c = nameSym "c" in
         mkBody op [a, b, c])
  in

  bindall_ [
      intr2 _addiName addi_
    , intr2 _subiName subi_
    , intr2 _muliName muli_
    , intr2 _diviName divi_
    , intr2 _modiName modi_
    , intr1 _negiName negi_
    , intr2 _ltiName lti_
    , intr2 _leqiName leqi_
    , intr2 _gtiName gti_
    , intr2 _geqiName geqi_
    , intr2 _eqiName eqi_
    , intr2 _neqiName neqi_
    , intr2 _slliName slli_
    , intr2 _srliName srli_
    , intr2 _sraiName srai_
    , intr2 _addfName addf_
    , intr2 _subfName subf_
    , intr2 _mulfName mulf_
    , intr2 _divfName divf_
    , intr1 _negfName negf_
    , intr2 _ltfName ltf_
    , intr2 _leqfName leqf_
    , intr2 _gtfName gtf_
    , intr2 _geqfName geqf_
    , intr2 _eqfName eqf_
    , intr2 _neqfName neqf_
    , intr1 _floorfiName (appf1_ (_floatOp "floorfi"))
    , intr1 _ceilfiName (appf1_ (_floatOp "ceilfi"))
    , intr1 _roundfiName (appf1_ (_floatOp "roundfi"))
    , intr1 _int2floatName int2float_
    , intr1 _string2floatName (appf1_ (_floatOp "string2float"))
    , intr2 _eqcName eqc_
    , intr1 _char2intName char2int_
    , intr1 _int2charName int2char_
    , intr2 _createName (appf2_ (_seqOp "create"))
    , intr1 _lengthName (appf1_ (_seqOp "length"))
    , intr2 _concatName (appf2_ (_seqOp "concat"))
    , intr2 _getName (appf2_ (_seqOp "get"))
    , intr3 _setName (appf3_ (_seqOp "set"))
    , intr2 _consName (appf2_ (_seqOp "cons"))
    , intr2 _snocName (appf2_ (_seqOp "snoc"))
    , intr2 _splitAtName (appf2_ (_seqOp "split_at"))
    , intr1 _reverseName (appf1_ (_seqOp "reverse"))
    , intr3 _subsequenceName (appf3_ (_seqOp "subsequence"))
    , intr1 _ofArrayName (appf1_ (_seqOp "Helpers.of_array"))
    , intr1 _printName (appf1_ (_ioOp "print"))
    , intr1 _readLineName (appf1_ (_ioOp "read_line"))
    , intr0 _argvName (_sysOp "argv")
    , intr1 _readFileName (appf1_ (_fileOp "read"))
    , intr2 _writeFileName (appf2_ (_fileOp "write"))
    , intr1 _fileExistsName (appf1_ (_fileOp "exists"))
    , intr1 _deleteFileName (appf1_ (_fileOp "delete"))
    , intr1 _errorName (appf1_ (_sysOp "error"))
    , intr1 _exitName (appf1_ (_sysOp "exit"))
    , intr2 _eqsymName (appf2_ (_symbOp "eqsym"))
    , intr1 _gensymName (appf1_ (_symbOp "gensym"))
    , intr1 _sym2hashName (appf1_ (_symbOp "hash"))
    , intr2 _randIntUName (appf2_ (_randOp "int_u"))
    , intr1 _randSetSeedName (appf1_ (_randOp "set_seed"))
    , intr1 _wallTimeMsName (appf1_ (_timeOp "get_wall_time_ms"))
    , intr1 _sleepMsName (appf1_ (_timeOp "sleep_ms"))
    , intr1 _bootParserParseMExprStringName (appf1_ (_bootparserOp "parseMExprString"))
    , intr1 _bootParserGetIdName (appf1_ (_bootparserOp "getId"))
    , intr2 _bootParserGetTermName (appf2_ (_bootparserOp "getTerm"))
    , intr2 _bootParserGetStringName (appf2_ (_bootparserOp "getString"))
    , intr2 _bootParserGetIntName (appf2_ (_bootparserOp "getInt"))
    , intr2 _bootParserGetFloatName (appf2_ (_bootparserOp "getFloat"))
    , intr2 _bootParserGetListLengthName (appf2_ (_bootparserOp "getListLength"))
    , intr2 _bootParserGetConstName (appf2_ (_bootparserOp "getConst"))
    , intr2 _bootParserGetPatName (appf2_ (_bootparserOp "getPat"))
    , intr1 _bootParserGetInfoName (appf1_ (_bootparserOp "getInfo"))
  ]

lang OCamlObjWrap = MExprAst + OCamlAst
  sem intrinsic2name =
  | CAddi _ -> nvar_ _addiName
  | CSubi _ -> nvar_ _subiName
  | CMuli _ -> nvar_ _muliName
  | CDivi _ -> nvar_ _diviName
  | CModi _ -> nvar_ _modiName
  | CNegi _ -> nvar_ _negiName
  | CLti _ -> nvar_ _ltiName
  | CLeqi _ -> nvar_ _leqiName
  | CGti _ -> nvar_ _gtiName
  | CGeqi _ -> nvar_ _geqiName
  | CEqi _ -> nvar_ _eqiName
  | CNeqi _ -> nvar_ _neqiName
  | CSlli _ -> nvar_ _slliName
  | CSrli _ -> nvar_ _srliName
  | CSrai _ -> nvar_ _sraiName
  | CAddf _ -> nvar_ _addfName
  | CSubf _ -> nvar_ _subfName
  | CMulf _ -> nvar_ _mulfName
  | CDivf _ -> nvar_ _divfName
  | CNegf _ -> nvar_ _negfName
  | CLtf _ -> nvar_ _ltfName
  | CLeqf _ -> nvar_ _leqfName
  | CGtf _ -> nvar_ _gtfName
  | CGeqf _ -> nvar_ _geqfName
  | CEqf _ -> nvar_ _eqfName
  | CNeqf _ -> nvar_ _neqfName
  | CFloorfi _ -> nvar_ _floorfiName
  | CCeilfi _ -> nvar_ _ceilfiName
  | CRoundfi _ -> nvar_ _roundfiName
  | CInt2float _ -> nvar_ _int2floatName
  | CString2float _ -> nvar_ _string2floatName
  | CEqc _ -> nvar_ _eqcName
  | CChar2Int _ -> nvar_ _char2intName
  | CInt2Char _ -> nvar_ _int2charName
  | CCreate _ -> nvar_ _createName
  | CLength _ -> nvar_ _lengthName
  | CConcat _ -> nvar_ _concatName
  | CGet _ -> nvar_ _getName
  | CSet _ -> nvar_ _setName
  | CCons _ -> nvar_ _consName
  | CSnoc _ -> nvar_ _snocName
  | CSplitAt _ -> nvar_ _splitAtName
  | CReverse _ -> nvar_ _reverseName
  | CSubsequence _ -> nvar_ _subsequenceName
  | CPrint _ -> nvar_ _printName
  | CReadLine _ -> nvar_ _readLineName
  | CArgv _ -> nvar_ _argvName
  | CFileRead _ -> nvar_ _readFileName
  | CFileWrite _ -> nvar_ _writeFileName
  | CFileExists _ -> nvar_ _fileExistsName
  | CFileDelete _ -> nvar_ _deleteFileName
  | CError _ -> nvar_ _errorName
  | CExit _ -> nvar_ _exitName
  | CEqsym _ -> nvar_ _eqsymName
  | CGensym _ -> nvar_ _gensymName
  | CSym2hash _ -> nvar_ _sym2hashName
  | CRandIntU _ -> nvar_ _randIntUName
  | CRandSetSeed _ -> nvar_ _randSetSeedName
  | CWallTimeMs _ -> nvar_ _wallTimeMsName
  | CSleepMs _ -> nvar_ _sleepMsName
  | CMapEmpty _ -> nvar_ _mapEmptyName
  | CMapInsert _ -> nvar_ _mapInsertName
  | CMapRemove _ -> nvar_ _mapRemoveName
  | CMapFind _ -> nvar_ _mapFindName
  | CMapAny _ -> nvar_ _mapAnyName
  | CMapMem _ -> nvar_ _mapMemName
  | CMapMap _ -> nvar_ _mapMapName
  | CMapMapWithKey _ -> nvar_ _mapMapWithKeyName
  | CMapBindings _ -> nvar_ _mapBindingsName
  | CTensorCreate _ -> nvar_ _tensorCreateName
  | CTensorGetExn _ -> nvar_ _tensorGetExnName
  | CTensorSetExn _ -> nvar_ _tensorSetExnName
  | CTensorRank _ -> nvar_ _tensorRankName
  | CTensorShape _ -> nvar_ _tensorShapeName
  | CTensorReshapeExn _ -> nvar_ _tensorReshapeExnName
  | CTensorCopyExn _ -> nvar_ _tensorCopyExnName
  | CTensorSliceExn _ -> nvar_ _tensorSliceExnName
  | CTensorSubExn _ -> nvar_ _tensorSubExnName
  | CTensorIteri _ -> nvar_ _tensorIteriName
  | CBootParserParseMExprString _ -> nvar_ _bootParserParseMExprStringName
  | CBootParserGetId _ -> nvar_ _bootParserGetIdName
  | CBootParserGetTerm _ -> nvar_ _bootParserGetTermName
  | CBootParserGetString _ -> nvar_ _bootParserGetStringName
  | CBootParserGetInt _ -> nvar_ _bootParserGetIntName
  | CBootParserGetFloat _ -> nvar_ _bootParserGetFloatName
  | CBootParserGetListLength _ -> nvar_ _bootParserGetListLengthName
  | CBootParserGetConst _ -> nvar_ _bootParserGetConstName
  | CBootParserGetPat _ -> nvar_ _bootParserGetPatName
  | CBootParserGetInfo _ -> nvar_ _bootParserGetInfoName
  | t -> dprintLn t; error "Intrinsic not implemented"

  sem objWrapRec =
  | (TmConst {val = (CInt _) | (CFloat _) | (CChar _) | (CBool _)}) & t ->
    _objRepr t
  | TmApp t ->
    if _isIntrinsicApp t.lhs then
      TmApp {{t with lhs = objWrapRec t.lhs}
                with rhs = _objRepr (objWrapRec t.rhs)}
    else
      TmApp {{t with lhs = objWrapRec t.lhs}
                with rhs = objWrapRec t.rhs}
  | TmConst {val = c} ->
    intrinsic2name c
  | (OTmArray _) & t -> _objRepr (smap_Expr_Expr objWrapRec t)
  | (OTmConApp _) & t -> _objRepr (smap_Expr_Expr objWrapRec t)
  | OTmMatch t ->
    OTmMatch {{t with target = _objObj (objWrapRec t.target)}
                 with arms = map (lam p. (p.0, _objRepr (objWrapRec p.1))) t.arms}
  | t -> smap_Expr_Expr objWrapRec t

  sem objWrap =
  | OTmVariantTypeDecl t ->
    OTmVariantTypeDecl {t with inexpr = objWrap t.inexpr}
  | t -> objWrapRec (_objObj t)
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

-- Evaluates OCaml expressions [strConvert] given as string, applied
-- to [p], and parses it as a mexpr expression.
let ocamlEval = lam p.
  let res = ocamlCompileWithConfig {warnings=false} (expr2str p) in
  let out = (res.run "" []).stdout in
  res.cleanup ();
  parseAsMExpr out
in

-- NOTE(oerikss, 2021-03-05): We pre- pretty-print the preamble here the make
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
    rhs = OTmString {text = fmt}
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
  ocamlEval (wrapOCamlAstInPrint ast (printf "'%c'"))
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
    eval {env = []} mexprAst
  in
  let ocamlAst = withPreamble ocamlAst in
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
  match generateTypeDecl (typeAnnot t) with (env, t) then
    objWrap (generate env t)
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

-- TODO(Oscar Eriksson, 2020-11-16) Test splitAt when we have implemented tuple
-- projection.

-- TODO(Oscar Eriksson, 2020-11-30) Test symbol operations when we have
-- implemented tuples/records.

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
-- let testPrint = print_ (str_ "tested print") in
-- utest testPrint with generate testPrint using sameSemantics in

-- Random number generation operations
let testSeededRandomNumber =
 symbolize
 (bindall_ [ulet_ "_" (randSetSeed_ (int_ 42)),
            randIntU_ (int_ 0) (int_ 10)])
in
utest testSeededRandomNumber with generateEmptyEnv testSeededRandomNumber
using sameSemantics in

-- Time operations

-- NOTE(larshum, 2020-12-14): Cannot test time operations until unit types
-- are supported.

-- let testWallTimeMs = wallTimeMs_ unit_ in
-- utest testWallTimeMs with generateEmptyEnv testWallTimeMs using sameSemantics in

-- let testSleepMs = sleepMs_ (int_ 10) in
-- utest testSleepMs with generateEmptyEnv testSleepMs using sameSemantics in

-- TODO(oerikss, 2020-12-14): Sys operations are not tested

-- TODO(larshum, 2021-03-06): Add tests for boot parser, map and tensor
-- intrinsics

()
