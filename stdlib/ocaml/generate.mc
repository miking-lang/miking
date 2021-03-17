include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "ocaml/ast.mc"
include "ocaml/pprint.mc"
include "mexpr/parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/eval.mc"
include "mexpr/eq.mc"
include "ocaml/compile.mc"

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

let _mapOp = use OCamlAst in lam op. OTmVarExt {ident = concat "Boot.Intrinsics.Mmap." op}

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
let _tuplet = use OCamlAst in lam pats. lam val. lam body. OTmMatch {target = val, arms = [(OPTuple {pats = pats}, body)]}

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
let _getName = nameSym "getName"
let _setName = nameSym "setName"
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
let _mapFindWithExnName = nameSym "mapFindWithExn"
let _mapFindOrElseName = nameSym "mapFindOrElse"
let _mapFindApplyOrElseName = nameSym "mapFindApplyOrElse"
let _mapBindingsName = nameSym "mapBindings"
let _mapSizeName = nameSym "mapSize"
let _mapMemName = nameSym "mapMem"
let _mapAnyName = nameSym "mapAny"
let _mapMapName = nameSym "mapMap"
let _mapMapWithKeyName = nameSym "mapMapWithKey"
let _mapFoldWithKeyName = nameSym "mapFoldWithKey"
let _mapEqName = nameSym "mapEq"
let _mapCmpName = nameSym "mapCmp"
let _mapGetCmpFunHelperName = nameSym "mapGetCmpFunHelper"
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
  sem generate =
  | TmSeq {tms = tms} ->
    app_ (nvar_ _ofArrayName) (OTmArray {tms = map generate tms})
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
      match generatePat n pat with (names, innerWrap) then
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
      match generatePat n pat with (names, innerWrap) then
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
    match generatePat targetName lpat with (lnames, lwrap) then
      match generatePat targetName rpat with (rnames, rwrap) then
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
    match generatePat targetName lpat with (lnames, lwrap) then
      match generatePat targetName rpat with (rnames, rwrap) then
        let names = assocMergePreferRight {eq=nameEqSym} lnames rnames in
        let wrap = lam cont. lwrap (rwrap cont) in
        (names, wrap)
      else never
    else never
  | PatNot {subpat = pat} ->
    match generatePat targetName pat with (_, innerWrap) then
      let wrap = lam cont.
        _optMatch (innerWrap (_some (OTmTuple {values = []})))
          pvarw_
          _none
          cont in
      (assocEmpty, wrap)
    else never
end

recursive let _isIntrinsicApp = use OCamlAst in
  lam lhs.
    match lhs with TmConst _ then true
    else match lhs with TmApp {lhs = TmConst _} then true
    else match lhs with TmApp {lhs = (TmApp _) & lhs} then
      _isIntrinsicApp lhs
    else false
end

let _objTName = nameSym "Obj.t"
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

  let intr4 = lam name. lam op.
      nulet_ name
        (let a = nameSym "a" in
         let b = nameSym "b" in
         let c = nameSym "c" in
         let d = nameSym "d" in
         mkBody op [a, b, c, d])
  in

  bindall_
    [ intr2 _addiName addi_
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
    , intr1 _mapEmptyName (appf1_ (_mapOp "empty"))
    , intr3 _mapInsertName (appf3_ (_mapOp "insert"))
    , intr2 _mapRemoveName (appf2_ (_mapOp "remove"))
    , intr2 _mapFindWithExnName (appf2_ (_mapOp "find"))
    , intr3 _mapFindOrElseName (appf3_ (_mapOp "find_or_else"))
    , intr4 _mapFindApplyOrElseName (appf4_ (_mapOp "find_apply_or_else"))
    , intr1 _mapBindingsName (appf1_ (_mapOp "bindings"))
    , intr1 _mapSizeName (appf1_ (_mapOp "size"))
    , intr2 _mapMemName (appf2_ (_mapOp "mem"))
    , intr2 _mapAnyName (appf2_ (_mapOp "any"))
    , intr2 _mapMapName (appf2_ (_mapOp "map"))
    , intr2 _mapMapWithKeyName (appf2_ (_mapOp "map_with_key"))
    , intr3 _mapFoldWithKeyName (appf3_ (_mapOp "fold_with_key"))
    , intr3 _mapEqName (appf3_ (_mapOp "eq"))
    , intr3 _mapCmpName (appf3_ (_mapOp "cmp"))
    , intr3 _mapGetCmpFunHelperName (appf3_ (_mapOp "key_cmp"))
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
  | CMapFindWithExn _ -> nvar_ _mapFindWithExnName
  | CMapFindOrElse _ -> nvar_ _mapFindOrElseName
  | CMapFindApplyOrElse _ -> nvar_ _mapFindApplyOrElseName
  | CMapBindings _ -> nvar_ _mapBindingsName
  | CMapSize _ -> nvar_ _mapSizeName
  | CMapMem _ -> nvar_ _mapMemName
  | CMapAny _ -> nvar_ _mapAnyName
  | CMapMap _ -> nvar_ _mapMapName
  | CMapMapWithKey _ -> nvar_ _mapMapWithKeyName
  | CMapFoldWithKey _ -> nvar_ _mapFoldWithKeyName
  | CMapEq _ -> nvar_ _mapEqName
  | CMapCmp _ -> nvar_ _mapCmpName
  | CMapGetCmpFun _ ->
    let k1 = nameSym "k1" in
    let k2 = nameSym "k2" in
    nulam_ k1 (nulam_ k2
       (appf2_ (nvar_ _mapGetCmpFunHelperName) (nvar_ k1) (nvar_ k2)))
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
  | OTmMatch t ->
    OTmMatch {{t with target = _objObj (objWrapRec t.target)}
                 with arms = map (lam p. (p.0, _objRepr (objWrapRec p.1))) t.arms}
  | t -> smap_Expr_Expr objWrapRec t

  sem _objWrapNoPremable =
  | t -> objWrapRec (_objObj t)

  sem objWrap =
  | t ->
    bind_ _preamble (_objWrapNoPremable t)
end

lang OCamlTest = OCamlGenerate + OCamlPrettyPrint + MExprSym + ConstEq
                 + IntEq + BoolEq + CharEq + FloatEq + OCamlObjWrap

mexpr

use OCamlTest in

-- Test semantics

-- Parse helper
let parseAsMExpr = lam s.
  use MExprParser in parseExpr (initPos "") s
in

-- Evaluates OCaml expressions [strConvert] given as string, applied
-- to [p], and parses it as a mexpr expression.
let ocamlEval = lam strConvert. lam p.
  let res =
    ocamlCompileWithConfig {warnings=false}
                           (join ["print_string (", strConvert, "(", p, "))"])
  in
  let out = (res.run "" []).stdout in
  res.cleanup ();
  parseAsMExpr out
in

-- NOTE(oerikss, 2021-03-05): We pre- pretty-print the premable here to make
-- the test run faster. This is an ugly hack!
let premableStr =
  let str = expr2str (bind_ _preamble (int_ 0)) in
  let len = length str in
  subsequence str 0 (subi len 1)
in

-- NOTE(oerikss, 2021-03-05): Here we paste the pre- pretty-printed preamable
-- to our program. This is part of the above mentioned hack.
let ocamlExpr2str = lam ast.
  concat premableStr (expr2str ast)
in

let ocamlEvalInt = lam ast.
  ocamlEval "string_of_int" (ocamlExpr2str ast)
in

let ocamlEvalFloat = lam ast.
  ocamlEval "string_of_float" (ocamlExpr2str ast)
in

let ocamlEvalBool = lam ast.
  ocamlEval "string_of_bool" (ocamlExpr2str ast)
in

let ocamlEvalChar = lam ast.
  ocamlEval "Printf.sprintf \"'%c'\"" (ocamlExpr2str ast)
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

  match mexprVal with TmConst t then
    match t.val with CInt _ then
      let ocamlVal = ocamlEvalInt ocamlAst in
      match ocamlVal with TmConst {val = CInt _} then
        eqExpr mexprVal ocamlVal
      else error "Value mismatch"
    else match t.val with CFloat _ then
      let ocamlVal = ocamlEvalFloat ocamlAst in
      match ocamlVal with TmConst {val = CFloat _} then
        eqExpr mexprVal ocamlVal
      else error "Value mismatch"
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

let objWrapGenerate = lam a. _objWrapNoPremable (generate a) in

-- Match
let matchChar1 = symbolize
 (match_ (char_ 'a')
   (pchar_ 'a')
   true_
   false_) in
 utest matchChar1 with objWrapGenerate matchChar1 using sameSemantics in

 let matchChar2 = symbolize
   (match_ (char_ 'a')
     (pchar_ 'b')
     true_
     false_) in
 utest matchChar2 with objWrapGenerate matchChar2 using sameSemantics in

let matchSeq = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3])
    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
    (addi_ (var_ "a") (var_ "b"))
    (int_ 42)) in
utest matchSeq with objWrapGenerate matchSeq using sameSemantics in

let noMatchSeq1 = symbolize
  (match_ (seq_ [int_ 2, int_ 2, int_ 3])
    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
    (addi_ (var_ "a") (var_ "b"))
    (int_ 42)) in
utest noMatchSeq1 with objWrapGenerate noMatchSeq1 using sameSemantics in

let noMatchSeqLen = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
    (addi_ (var_ "a") (var_ "b"))
    (int_ 42)) in
utest noMatchSeqLen with objWrapGenerate noMatchSeqLen using sameSemantics in

let noMatchSeqLen2 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
    (addi_ (var_ "a") (var_ "b"))
    (int_ 42)) in
utest noMatchSeqLen2 with objWrapGenerate noMatchSeqLen2 using sameSemantics in

let matchOr1 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchOr1 with objWrapGenerate matchOr1 using sameSemantics in

let matchOr2 = symbolize
  (match_ (seq_ [int_ 2, int_ 1])
    (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchOr2 with objWrapGenerate matchOr2 using sameSemantics in

let matchOr3 = symbolize
  (match_ (seq_ [int_ 3, int_ 1])
    (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchOr3 with objWrapGenerate matchOr3 using sameSemantics in

let matchNestedOr1 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
          (pseqtot_ [pint_ 3, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchNestedOr1 with objWrapGenerate matchNestedOr1 using sameSemantics in

let matchNestedOr2 = symbolize
  (match_ (seq_ [int_ 2, int_ 1])
    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
          (pseqtot_ [pint_ 3, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchNestedOr2 with objWrapGenerate matchNestedOr2 using sameSemantics in

let matchNestedOr3 = symbolize
  (match_ (seq_ [int_ 3, int_ 7])
    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
          (pseqtot_ [pint_ 3, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchNestedOr3 with objWrapGenerate matchNestedOr3 using sameSemantics in

let matchNestedOr4 = symbolize
  (match_ (seq_ [int_ 4, int_ 7])
    (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
          (pseqtot_ [pint_ 3, pvar_ "a"]))
    (var_ "a")
    (int_ 42)) in
utest matchNestedOr4 with objWrapGenerate matchNestedOr4 using sameSemantics in

let matchNot1 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pnot_ (pseqtot_ [pint_ 1, pvar_ "a"]))
    true_
    false_) in
utest matchNot1 with objWrapGenerate matchNot1 using sameSemantics in

let matchNot2 = symbolize
  (match_ (seq_ [int_ 2, int_ 2])
    (pnot_ (pseqtot_ [pint_ 1, pvar_ "a"]))
    true_
    false_) in
utest matchNot2 with objWrapGenerate matchNot2 using sameSemantics in

let matchAnd1 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pvar_ "b"))
    (addi_ (var_ "a") (get_ (var_ "b") (int_ 1)))
    (int_ 53)) in
utest matchAnd1 with objWrapGenerate matchAnd1 using sameSemantics in

let matchAnd2 = symbolize
  (match_ (seq_ [int_ 2, int_ 2])
    (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pvar_ "b"))
    (addi_ (var_ "a") (get_ (var_ "b") (int_ 1)))
    (int_ 53)) in
utest matchAnd2 with objWrapGenerate matchAnd2 using sameSemantics in

let matchAnd3 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ []))
    (var_ "a")
    (int_ 53)) in
utest matchAnd3 with objWrapGenerate matchAnd3 using sameSemantics in

let matchAnd4 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pand_ (pseqtot_ []) (pseqtot_ [pint_ 1, pvar_ "a"]))
    (var_ "a")
    (int_ 53)) in
utest matchAnd4 with objWrapGenerate matchAnd4 using sameSemantics in

let matchSeqEdge1 = symbolize
  (match_ (seq_ [int_ 1])
    (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
    (addi_ (var_ "a") (var_ "c"))
    (int_ 75)) in
utest matchSeqEdge1 with objWrapGenerate matchSeqEdge1 using sameSemantics in

let matchSeqEdge2 = symbolize
  (match_ (seq_ [int_ 1, int_ 2])
    (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
    (addi_ (var_ "a") (var_ "c"))
    (int_ 75)) in
utest matchSeqEdge2 with objWrapGenerate matchSeqEdge2 using sameSemantics in

let matchSeqEdge3 = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3])
    (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
    (addi_ (var_ "a") (var_ "c"))
    (int_ 75)) in
utest matchSeqEdge3 with objWrapGenerate matchSeqEdge3 using sameSemantics in

let matchSeqEdge4 = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
    (pseqedge_ [pvar_ "a", pvar_ "d"] "b" [pvar_ "c"])
    (addi_ (addi_ (var_ "d") (var_ "a")) (var_ "c"))
    (int_ 75)) in
utest matchSeqEdge4 with objWrapGenerate matchSeqEdge4 using sameSemantics in

let matchSeqEdge5 = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
    (por_ (pseqedge_ [pint_ 2] "b" []) (pseqedge_ [pint_ 1] "b" []))
    (match_ (var_ "b")
      (pseqedgew_ [pvar_ "a"] [pvar_ "c"])
      (addi_ (var_ "a") (var_ "c"))
      (int_ 84))
    (int_ 75)) in
utest matchSeqEdge5 with objWrapGenerate matchSeqEdge5 using sameSemantics in

let matchSeqEdge6 = symbolize
  (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
    (por_ (pseqedge_ [pint_ 2] "b" []) (pseqedge_ [] "b" [pint_ 4]))
    (match_ (var_ "b")
      (pseqedgew_ [pvar_ "a"] [pvar_ "c"])
      (addi_ (var_ "a") (var_ "c"))
      (int_ 84))
    (int_ 75)) in
utest matchSeqEdge6 with objWrapGenerate matchSeqEdge6 using sameSemantics in

let matchSeqEdge7 = symbolize
  (match_ (seq_ [int_ 1])
    (pseqedgew_ [pvar_ "a"] [])
    (var_ "a")
    (int_ 75)) in
utest matchSeqEdge7 with objWrapGenerate matchSeqEdge7 using sameSemantics in

-- Ints
let addInt1 = addi_ (int_ 1) (int_ 2) in
utest addInt1 with objWrapGenerate addInt1 using sameSemantics in

let addInt2 = addi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest addInt2 with objWrapGenerate addInt2 using sameSemantics in

let testMulInt = muli_ (int_ 2) (int_ 3) in
utest testMulInt with objWrapGenerate testMulInt using sameSemantics in

let testModInt = modi_ (int_ 2) (int_ 3) in
utest testModInt with objWrapGenerate testModInt using sameSemantics in

let testDivInt = divi_ (int_ 2) (int_ 3) in
utest testDivInt with objWrapGenerate testDivInt using sameSemantics in

let testNegInt = addi_ (int_ 2) (negi_ (int_ 2)) in
utest testNegInt with objWrapGenerate testNegInt using sameSemantics in

let compareInt1 = eqi_ (int_ 1) (int_ 2) in
utest compareInt1 with objWrapGenerate compareInt1 using sameSemantics in

let compareInt2 = lti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt2 with objWrapGenerate compareInt2 using sameSemantics in

let compareInt3 = leqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt3 with objWrapGenerate compareInt3 using sameSemantics in

let compareInt4 = gti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt4 with objWrapGenerate compareInt4 using sameSemantics in

let compareInt5 = geqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt5 with objWrapGenerate compareInt5 using sameSemantics in

let compareInt6 = neqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest compareInt6 with objWrapGenerate compareInt6 using sameSemantics in

let shiftInt1 = slli_ (int_ 5) (int_ 2) in
utest shiftInt1 with objWrapGenerate shiftInt1 using sameSemantics in

let shiftInt2 = srli_ (int_ 5) (int_ 2) in
utest shiftInt2 with objWrapGenerate shiftInt2 using sameSemantics in

let shiftInt3 = srai_ (int_ 5) (int_ 2) in
utest shiftInt3 with objWrapGenerate shiftInt3 using sameSemantics in

---- Floats
let addFloat1 = addf_ (float_ 1.) (float_ 2.) in
utest addFloat1 with objWrapGenerate addFloat1 using sameSemantics in

let addFloat2 = addf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest addFloat2 with objWrapGenerate addFloat2 using sameSemantics in

let testMulFloat = mulf_ (float_ 2.) (float_ 3.) in
utest testMulFloat with objWrapGenerate testMulFloat using sameSemantics in

let testDivFloat = divf_ (float_ 6.) (float_ 3.) in
utest testDivFloat with objWrapGenerate testDivFloat using sameSemantics in

let testNegFloat = addf_ (float_ 2.) (negf_ (float_ 2.)) in
utest testNegFloat with objWrapGenerate testNegFloat using sameSemantics in

let compareFloat1 = eqf_ (float_ 1.) (float_ 2.) in
utest compareFloat1 with objWrapGenerate compareFloat1 using sameSemantics in

let compareFloat2 = ltf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat2 with objWrapGenerate compareFloat2 using sameSemantics in

let compareFloat3 = leqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat3 with objWrapGenerate compareFloat3 using sameSemantics in

let compareFloat4 = gtf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat4 with objWrapGenerate compareFloat4 using sameSemantics in

let compareFloat5 = geqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat5 with objWrapGenerate compareFloat5 using sameSemantics in

let compareFloat6 = neqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
utest compareFloat6 with objWrapGenerate compareFloat6 using sameSemantics in


-- Chars
let charLiteral = char_ 'c' in
utest charLiteral with objWrapGenerate charLiteral
using sameSemantics in

let compareChar1 = eqc_ (char_ 'a') (char_ 'b') in
utest compareChar1 with objWrapGenerate compareChar1 using sameSemantics in

let compareChar2 = eqc_ (char_ 'a') (char_ 'a') in
utest compareChar2 with objWrapGenerate compareChar2 using sameSemantics in

let testCharToInt = char2int_ (char_ '0') in
utest testCharToInt with objWrapGenerate testCharToInt using sameSemantics in

let testIntToChar = int2char_ (int_ 48) in
utest testIntToChar with objWrapGenerate testIntToChar using sameSemantics in


-- Abstractions
let fun =
  symbolize
  (appSeq_
    (ulam_ "@" (ulam_ "%" (addi_ (var_ "@") (var_ "%"))))
    [int_ 1, int_ 2])
in
utest fun with objWrapGenerate fun using sameSemantics in

let funShadowed =
  symbolize
  (appSeq_
    (ulam_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))))
    [ulam_ "@" (var_ "@"), int_ 2])
in
utest funShadowed with objWrapGenerate funShadowed using sameSemantics in

-- Lets
 let testLet =
  symbolize
  (bindall_ [ulet_ "^" (int_ 1), addi_ (var_ "^") (int_ 2)])
in
utest testLet with objWrapGenerate testLet using sameSemantics in

let testLetShadowed =
  symbolize
  (bindall_ [ulet_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))),
             app_ (var_ "@") (int_ 1)])
in
utest testLetShadowed with objWrapGenerate testLetShadowed
using sameSemantics in

let testLetRec =
  symbolize
  (bind_
     (ureclets_add "$" (ulam_ "%" (app_ (var_ "@") (int_ 1)))
     (ureclets_add "@" (ulam_ "" (var_ ""))
     reclets_empty))
   (app_ (var_ "$") (var_ "@")))
in
utest testLetRec with objWrapGenerate testLetRec using sameSemantics in

-- Sequences
let testEmpty = symbolize (length_ (seq_ [])) in
utest testEmpty with objWrapGenerate testEmpty using sameSemantics in

let nonEmpty = seq_ [int_ 1, int_ 2, int_ 3] in
let len = length_ nonEmpty in
let fst = get_ nonEmpty (int_ 0) in
let snd = get_ nonEmpty (int_ 1) in
let thrd = get_ nonEmpty (int_ 2) in
utest int_ 3 with objWrapGenerate len using sameSemantics in
utest int_ 1 with objWrapGenerate fst using sameSemantics in
utest int_ 2 with objWrapGenerate snd using sameSemantics in
utest int_ 3 with objWrapGenerate thrd using sameSemantics in

let testCreate = create_ (int_ 2) (ulam_ "_" (int_ 0)) in
let len = length_ testCreate in
let fst = get_ testCreate (int_ 0) in
let lst = get_ testCreate (int_ 1) in
utest int_ 2 with objWrapGenerate len using sameSemantics in
utest int_ 0 with objWrapGenerate fst using sameSemantics in
utest int_ 0 with objWrapGenerate lst using sameSemantics in

let testSet = set_ (seq_ [int_ 1, int_ 2]) (int_ 0) (int_ 3) in
let len = length_ testSet in
let fst = get_ testSet (int_ 0) in
let snd = get_ testSet (int_ 1) in
utest int_ 2 with objWrapGenerate len using sameSemantics in
utest int_ 3 with objWrapGenerate fst using sameSemantics in
utest int_ 2 with objWrapGenerate snd using sameSemantics in

let testCons = cons_  (int_ 1) (seq_ [int_ 2, int_ 3]) in
let len = length_ testCons in
let fst = get_ testCons (int_ 0) in
let snd = get_ testCons (int_ 1) in
let thrd = get_ testCons (int_ 2) in
utest int_ 3 with objWrapGenerate len using sameSemantics in
utest int_ 1 with objWrapGenerate fst using sameSemantics in
utest int_ 2 with objWrapGenerate snd using sameSemantics in
utest int_ 3 with objWrapGenerate thrd using sameSemantics in

let testSnoc = snoc_ (seq_ [int_ 1, int_ 2]) (int_ 3) in
let len = length_ testSnoc in
let fst = get_ testSnoc (int_ 0) in
let snd = get_ testSnoc (int_ 1) in
let thrd = get_ testSnoc (int_ 2) in
utest int_ 3 with objWrapGenerate len using sameSemantics in
utest int_ 1 with objWrapGenerate fst using sameSemantics in
utest int_ 2 with objWrapGenerate snd using sameSemantics in
utest int_ 3 with objWrapGenerate thrd using sameSemantics in

let testReverse = reverse_ (seq_ [int_ 1, int_ 2, int_ 3]) in
let len = length_ testReverse in
let fst = get_ testReverse (int_ 0) in
let snd = get_ testReverse (int_ 1) in
let thrd = get_ testReverse (int_ 2) in
utest int_ 3 with objWrapGenerate len using sameSemantics in
utest int_ 3 with objWrapGenerate fst using sameSemantics in
utest int_ 2 with objWrapGenerate snd using sameSemantics in
utest int_ 1 with objWrapGenerate thrd using sameSemantics in

let testSeq = seq_ [int_ 1, int_ 2, int_ 3] in
let testSubseq1 = subsequence_ testSeq (int_ 0) (int_ 2) in
let testSubseq2 = subsequence_ testSeq (int_ 1) (int_ 2) in
let testSubseq3 = subsequence_ testSeq (int_ 2) (int_ 100) in
let fst = get_ testSubseq3 (int_ 0) in
utest int_ 2 with objWrapGenerate (length_ testSubseq1) using sameSemantics in
utest int_ 2 with objWrapGenerate (length_ testSubseq2) using sameSemantics in
utest int_ 1 with objWrapGenerate (length_ testSubseq3) using sameSemantics in
utest int_ 3 with objWrapGenerate fst using sameSemantics in

-- -- TODO(Oscar Eriksson, 2020-11-16) Test splitAt when we have implemented tuple
-- -- projection.

-- -- TODO(Oscar Eriksson, 2020-11-30) Test symbol operations when we have
-- -- implemented tuples/records.

-- Float-Integer conversions
let testFloorfi = floorfi_ (float_ 1.5) in
utest testFloorfi with objWrapGenerate testFloorfi using sameSemantics in

let testCeilfi = ceilfi_ (float_ 1.5) in
utest testCeilfi with objWrapGenerate testCeilfi using sameSemantics in

let testRoundfi = roundfi_ (float_ 1.5) in
utest testRoundfi with objWrapGenerate testRoundfi using sameSemantics in

let testInt2float = int2float_ (int_ 1) in
utest testInt2float with objWrapGenerate testInt2float using sameSemantics in

let testString2float = string2float_ (str_ "1.5") in
utest testString2float with objWrapGenerate testString2float using sameSemantics in

-- File operations
let testFileExists = fileExists_ (str_ "test_file_ops") in
utest testFileExists with objWrapGenerate testFileExists using sameSemantics in

-- -- IO operations
-- let testPrint = print_ (str_ "tested print") in
-- utest testPrint with generate testPrint using sameSemantics in

-- Random number generation operations
let testSeededRandomNumber =
 symbolize
 (bindall_ [ulet_ "_" (randSetSeed_ (int_ 42)),
            randIntU_ (int_ 0) (int_ 10)])
in
utest testSeededRandomNumber with objWrapGenerate testSeededRandomNumber
using sameSemantics in

-- Time operations

-- NOTE(larshum, 2020-12-14): Cannot test time operations until unit types
-- are supported.

-- let testWallTimeMs = wallTimeMs_ unit_ in
-- utest testWallTimeMs with objWrapGenerate testWallTimeMs using sameSemantics in

-- let testSleepMs = sleepMs_ (int_ 10) in
-- utest testSleepMs with objWrapGenerate testSleepMs using sameSemantics in

-- TODO(oerikss, 2020-12-14): Sys operations are not tested

-- Map intrinsics
let mapEmptyTest = bind_
  (ulet_ "m" (mapEmpty_ (ulam_ "x" (ulam_ "y" (subi_ (var_ "x") (var_ "y"))))))
  (int_ 42) in

utest ocamlEvalInt (objWrapGenerate mapEmptyTest) with int_ 42 using eqExpr in

let mapInsertFindTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 123) (int_ 90) (var_ "m"))
  , mapFindWithExn_ (int_ 42) (var_ "m")
  ] in
utest ocamlEvalInt (objWrapGenerate mapInsertFindTest)
with int_ 1 using eqExpr in

let mapMemTrueTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapMem_ (int_ 42) (var_ "m")
  ] in
utest ocamlEvalBool (objWrapGenerate mapMemTrueTest)
with true_ using eqExpr in

let mapMemFalseTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapMem_ (int_ 78) (var_ "m")
  ] in
utest ocamlEvalBool (objWrapGenerate mapMemFalseTest)
with false_ using eqExpr in

let mapRemoveTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , ulet_ "m" (mapRemove_ (int_ 42) (var_ "m"))
  , mapMem_ (int_ 42) (var_ "m")
  ] in
utest ocamlEvalBool (objWrapGenerate mapRemoveTest)
with false_ using eqExpr in

let mapFindOrElseTrueTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapFindOrElse_ (ulam_ "" (int_ 123)) (int_ 42) (var_ "m")
  ] in
utest ocamlEvalInt (objWrapGenerate mapFindOrElseTrueTest)
with int_ 1 using eqExpr in

let mapFindOrElseFalseTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapFindOrElse_ (ulam_ "" (int_ 123)) (int_ 3) (var_ "m")
  ] in
utest ocamlEvalInt (objWrapGenerate mapFindOrElseFalseTest)
with int_ 123 using eqExpr in

let mapFindApplyOrElseTrueTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapFindApplyOrElse_
      (ulam_ "x" (addi_ (var_ "x") (int_ 1)))
      (ulam_ "" (int_ 7))
      (int_ 42) (var_ "m")
  ] in
utest ocamlEvalInt (objWrapGenerate mapFindApplyOrElseTrueTest)
with int_ 2 using eqExpr in

let mapFindApplyOrElseFalseTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , mapFindApplyOrElse_
     (ulam_ "x" (addi_ (var_ "x") (int_ 1)))
     (ulam_ "" (int_ 7))
     (int_ 3) (var_ "m")
  ] in
utest ocamlEvalInt (objWrapGenerate mapFindApplyOrElseFalseTest)
with int_ 7 using eqExpr in

let mapSizeEmptyTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , mapSize_ (var_ "m")
  ] in
utest ocamlEvalInt (objWrapGenerate mapSizeEmptyTest)
with int_ 0 using eqExpr in

let mapSizeTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 1) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 100) (int_ 567) (var_ "m"))
  , mapSize_ (var_ "m")
  ] in
utest ocamlEvalInt (objWrapGenerate mapSizeTest)
with int_ 2 using eqExpr in

let mapAnyTrueTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , mapAny_ (ulam_ "k" (ulam_ "v" (geqi_ (var_ "k") (var_ "v")))) (var_ "m")
  ] in
utest ocamlEvalBool (objWrapGenerate mapAnyTrueTest)
with true_ using eqExpr in

let mapAnyFalseTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 0) (negi_ (int_ 1)) (var_ "m"))
  , mapAny_ (ulam_ "k" (ulam_ "v" (eqi_ (var_ "k") (var_ "v")))) (var_ "m")
  ] in
utest ocamlEvalBool (objWrapGenerate mapAnyFalseTest)
with false_ using eqExpr in

let mapMapTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 3) (int_ 56) (var_ "m"))
  , ulet_ "m" (mapMap_ (ulam_ "v" (addi_ (int_ 44) (var_ "v"))) (var_ "m"))
  , mapFindWithExn_ (int_ 3) (var_ "m")
  ] in
utest ocamlEvalInt (objWrapGenerate mapMapTest)
with int_ 100 using eqExpr in

let mapMapWithKeyTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 3) (int_ 56) (var_ "m"))
  , ulet_ "m"
    (mapMapWithKey_ (ulam_ "k" (ulam_ "v"
      (addi_ (var_ "k") (var_ "v")))) (var_ "m"))
  , mapFindWithExn_ (int_ 3) (var_ "m")
  ] in
utest ocamlEvalInt (objWrapGenerate mapMapWithKeyTest)
with int_ 59 using eqExpr in

let mapFoldWithKeyTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m" (mapInsert_ (int_ 42) (int_ 2) (var_ "m"))
  , ulet_ "m" (mapInsert_ (int_ 3) (int_ 56) (var_ "m"))
  , mapFoldWithKey_
      (ulam_ "acc" (ulam_ "k" (ulam_ "v"
        (addi_ (var_ "acc") (addi_ (var_ "k") (var_ "v")))))) (int_ 0) (var_ "m")
  ] in
utest ocamlEvalInt (objWrapGenerate mapFoldWithKeyTest)
with int_ 103 using eqExpr in

let mapEqTrueTest = bindall_
  [ ulet_ "m1" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "m2" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m2" (mapInsert_ (int_ 42) (int_ 2) (var_ "m2"))
  , ulet_ "m2" (mapInsert_ (int_ 3) (int_ 56) (var_ "m2"))
  , mapEq_ (ulam_ "v1" (ulam_ "v2"
      (eqi_ (var_ "v1") (var_ "v2")))) (var_ "m1") (var_ "m2")
  ] in
utest ocamlEvalBool (objWrapGenerate mapEqTrueTest)
with true_ using eqExpr in

let mapEqFalseTest = bindall_
  [ ulet_ "m1" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "m2" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m2" (mapInsert_ (int_ 42) (int_ 3) (var_ "m2"))
  , ulet_ "m2" (mapInsert_ (int_ 3) (int_ 56) (var_ "m2"))
  , mapEq_ (ulam_ "v1" (ulam_ "v2"
      (eqi_ (var_ "v1") (var_ "v2")))) (var_ "m1") (var_ "m2")
  ] in
utest ocamlEvalBool (objWrapGenerate mapEqFalseTest)
with false_ using eqExpr in

let mapCmpEqTest = bindall_
  [ ulet_ "m1" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "m2" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m2" (mapInsert_ (int_ 42) (int_ 2) (var_ "m2"))
  , ulet_ "m2" (mapInsert_ (int_ 3) (int_ 56) (var_ "m2"))
  , mapCmp_ (ulam_ "v1" (ulam_ "v2"
      (subi_ (var_ "v1") (var_ "v2")))) (var_ "m1") (var_ "m2")
  ] in
utest ocamlEvalInt (objWrapGenerate mapCmpEqTest)
with int_ 0 using eqExpr in

let mapCmpNEqTest = bindall_
  [ ulet_ "m1" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m1" (mapInsert_ (int_ 42) (int_ 2) (var_ "m1"))
  , ulet_ "m1" (mapInsert_ (int_ 3) (int_ 56) (var_ "m1"))
  , ulet_ "m2" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "m2" (mapInsert_ (int_ 42) (int_ 1) (var_ "m2"))
  , ulet_ "m2" (mapInsert_ (int_ 3) (int_ 56) (var_ "m2"))
  , mapCmp_ (ulam_ "v1" (ulam_ "v2"
      (subi_ (var_ "v1") (var_ "v2")))) (var_ "m1") (var_ "m2")
  ] in
utest ocamlEvalInt (objWrapGenerate mapCmpNEqTest)
with int_ 1 using eqExpr in

let mapGetCmpFunTest = bindall_
  [ ulet_ "m" (mapEmpty_ (TmConst {val = CSubi {}}))
  , ulet_ "f" (mapGetCmpFun_ (var_ "m"))
  , appf2_ (var_ "f") (int_ 12) (int_ 2)
  ] in
utest ocamlEvalInt (objWrapGenerate mapGetCmpFunTest)
with int_ 10 using eqExpr in

-- TODO(Linnea, 2020-03-12): Test mapBindings when we have tuple projections.

-- TODO(larshum, 2021-03-06): Add tests for boot parser, and tensor
-- intrinsics

()
