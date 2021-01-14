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
  let mkOp = lam op. nameSym (join [prefix, op]) in
  foldl (lam a. lam op. hashmapInsert hashmapStrTraits op (mkOp op) a)
        hashmapEmpty
        ops

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
  "roundfi",
  "string2float"
]

let _floatOp = _op (_opHashMap "Boot.Intrinsics.FloatConversion." _floatOps)

let _fileOps = [
  "read",
  "write",
  "exists",
  "delete"
]

let _fileOp = _op (_opHashMap "Boot.Intrinsics.File." _fileOps)

let _ioOps = [
  "print",
  "read_line"
]

let _ioOp = _op (_opHashMap "Boot.Intrinsics.IO." _ioOps)

let _sysOps = [
  "exit",
  "error",
  "argv"
]

let _sysOp = _op (_opHashMap "Boot.Intrinsics.MSys." _sysOps)

let _randOps = [
  "int_u",
  "set_seed"
]

let _randOp = _op (_opHashMap "Boot.Intrinsics.RNG." _randOps)

let _timeOps = [
  "get_wall_time_ms",
  "sleep_ms"
]

let _timeOp = _op (_opHashMap "Boot.Intrinsics.Time." _timeOps)

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
  -- Int-Float Conversion intrinsics
  | CFloorfi {} -> _floatOp "floorfi"
  | CCeilfi {} -> _floatOp "ceilfi"
  | CRoundfi {} -> _floatOp "roundfi"
  | CString2float {} -> _floatOp "string2float"
  -- File intrinsics
  | CFileRead {} -> _fileOp "read"
  | CFileWrite {} -> _fileOp "write"
  | CFileExists {} -> _fileOp "exists"
  | CFileDelete {} -> _fileOp "delete"
  -- Random number generation intrinsics
  | CRandIntU {} -> _randOp "int_u"
  | CRandSetSeed {} -> _randOp "set_seed"
  -- Time Intrinsics
  | CWallTimeMs {} -> _timeOp "get_wall_time_ms"
  | CSleepMs {} -> _timeOp "sleep_ms"
  -- Sys intrinsics
  | CExit {} -> _sysOp "exit"
  | CError {} -> _sysOp "error"
  | CArgv {} -> _sysOp "argv"
  -- IO intrinsics
  | CPrint {} -> _ioOp "print"
  | CReadLine {} -> _ioOp "read_line"
  -- Base case
  | v -> TmConst { val = v }

  sem generate =
  | TmSeq {tms = tms} ->
    let tms =
      if null tms then []
      else
        match head tms with TmConst {val = CChar _} then
          map (lam x. match x with TmConst {val = CChar {val = n}} then n
               else never)
              tms
        else map generate tms
    in
    foldr (lam tm. lam a. appSeq_ cons_ [tm, a])
          empty_
          tms
  -- | TmConst {val = val} -> generateConst val
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

let _objReprName = nameSym "Obj.repr"
let _objTName = nameSym "Obj.t"
let _objObjName = nameSym "Obj.obj"

let _objRepr = lam t. app_ (nvar_ _objReprName) t
let _objObj = lam t. app_ (nvar_ _objObjName) t

recursive let _isIntrinsicApp = use OCamlAst in
  lam t.
    match t with TmApp {lhs = TmConst _} then
      true
    else match t with TmApp {lhs = TmApp _} then
      _isIntrinsicApp t.lhs
    else false
end

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
let _makeSeqName = nameSym "makeSeq"
let _lengthName = nameSym "length"
let _concatName = nameSym "concat"
let _getName = nameSym "getName"
let _setName = nameSym "setName"
let _consName = nameSym "cons"
let _snocName = nameSym "snoc"
let _splitAtName = nameSym "splitAt"
let _reverseName = nameSym "reverse"
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
    , intr2 _makeSeqName (appf2_ (_seqOp "make"))
    , intr1 _lengthName (appf1_ (_seqOp "length"))
    , intr2 _concatName (appf2_ (_seqOp "concat"))
    , intr2 _getName (appf2_ (_seqOp "get"))
    , intr3 _setName (appf3_ (_seqOp "set"))
    , intr2 _consName (appf2_ (_seqOp "cons"))
    , intr2 _snocName (appf2_ (_seqOp "snoc"))
    , intr2 _splitAtName (appf2_ (_seqOp "split_at"))
    , intr1 _reverseName (appf1_ (_seqOp "reverse"))
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
  ]

lang OCamlObjWrap = OCamlAst
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
  | CMakeSeq _ -> nvar_ _makeSeqName
  | CLength _ -> nvar_ _lengthName
  | CConcat _ -> nvar_ _concatName
  | CGet _ -> nvar_ _getName
  | CSet _ -> nvar_ _setName
  | CCons _ -> nvar_ _consName
  | CSnoc _ -> nvar_ _snocName
  | CSplitAt _ -> nvar_ _splitAtName
  | CReverse _ -> nvar_ _reverseName
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
  | t -> error "Intrinsic not implemented"

  sem objWrapRec =
  | (TmConst {val = (CInt _) | (CFloat _) | (CChar _) | (CBool _)}) & t ->
    _objRepr t
  | TmConst {val = c} ->
    intrinsic2name c
  | t -> smap_Expr_Expr objWrapRec t

  sem objWrap =
  | t ->
    bind_ _preamble (_objObj (objWrapRec t))
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
let ocamlEval = lam p. lam strConvert.
  let t1 = wallTimeMs () in

  let res =
  let subprocess = pyimport "subprocess" in
  let blt = pyimport "builtins" in
    let res = ocamlCompileWithConfig {warnings=false} (join ["print_string (", strConvert, "(", p, "))"]) in
    let out = (res.run "" []).stdout in
    let _ = res.cleanup () in
    parseAsMExpr out
  in
  let t2 = wallTimeMs () in
  let _ = print (join ["-- ocamlEval: ", float2string (divf (subf t2 t1) 1000.), " s\n"]) in
  res
in

-- Compares evaluation of [mexprAst] as a mexpr and evaluation of
-- [ocamlAst] as a OCaml expression.
let sameSemantics = lam mexprAst. lam ocamlAst.
  let start = wallTimeMs () in
  let mexprVal =
    use MExprEval in
    let t1 = wallTimeMs () in
    let res = eval {env = []} mexprAst in
    let t2 = wallTimeMs () in
    let _ = print (join ["-- MExpr eval: ", float2string (divf (subf t2 t1) 1000.), " s\n"]) in
    res
  in
  let res =
  match mexprVal with TmConst t then
    match t.val with CInt _ then
      let t1 = wallTimeMs () in
      let str = expr2str ocamlAst in
      -- let _ = print str in
      let t2 = wallTimeMs () in
      let _ = print (join ["-- expr2str: ", float2string (divf (subf t2 t1) 1000.), " s\n"]) in
      let ocamlVal = ocamlEval (str) "string_of_int" in
      match ocamlVal with TmConst {val = CInt _} then
        let t1 = wallTimeMs () in
        let res = eqExpr mexprVal ocamlVal in
        let t2 = wallTimeMs () in
        let _ = print (join ["-- eqExpr: ", float2string (divf (subf t2 t1) 1000.), " s\n"]) in
        res
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
  let eend = wallTimeMs () in
  let _ = print (join ["-- sameSemantics: ", float2string (divf (subf eend start) 1000.), " s\n"]) in
  res
in

let objWrapGenerate = lam a. objWrap (generate a) in

-- Match
-- let matchChar1 = symbolize
--   (match_ (char_ 'a')
--     (pchar_ 'a')
--     true_
--     false_) in
-- utest matchChar1 with objWrapGenerate matchChar1 using sameSemantics in
--
-- let matchChar2 = symbolize
--   (match_ (char_ 'a')
--     (pchar_ 'b')
--     true_
--     false_) in
-- utest matchChar2 with objWrapGenerate matchChar2 using sameSemantics in
--
-- let matchSeq = symbolize
--   (match_ (seq_ [int_ 1, int_ 2, int_ 3])
--     (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
--     (addi_ (var_ "a") (var_ "b"))
--     (int_ 42)) in
-- utest matchSeq with objWrapGenerate matchSeq using sameSemantics in
--
-- let noMatchSeq1 = symbolize
--   (match_ (seq_ [int_ 2, int_ 2, int_ 3])
--     (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
--     (addi_ (var_ "a") (var_ "b"))
--     (int_ 42)) in
-- utest noMatchSeq1 with objWrapGenerate noMatchSeq1 using sameSemantics in
--
-- let noMatchSeqLen = symbolize
--   (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
--     (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
--     (addi_ (var_ "a") (var_ "b"))
--     (int_ 42)) in
-- utest noMatchSeqLen with objWrapGenerate noMatchSeqLen using sameSemantics in
--
-- let noMatchSeqLen2 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
--     (addi_ (var_ "a") (var_ "b"))
--     (int_ 42)) in
-- utest noMatchSeqLen2 with objWrapGenerate noMatchSeqLen2 using sameSemantics in
--
-- let matchOr1 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchOr1 with objWrapGenerate matchOr1 using sameSemantics in
--
-- let matchOr2 = symbolize
--   (match_ (seq_ [int_ 2, int_ 1])
--     (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchOr2 with objWrapGenerate matchOr2 using sameSemantics in
--
-- let matchOr3 = symbolize
--   (match_ (seq_ [int_ 3, int_ 1])
--     (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchOr3 with objWrapGenerate matchOr3 using sameSemantics in
--
-- let matchNestedOr1 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--           (pseqtot_ [pint_ 3, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchNestedOr1 with objWrapGenerate matchNestedOr1 using sameSemantics in
--
-- let matchNestedOr2 = symbolize
--   (match_ (seq_ [int_ 2, int_ 1])
--     (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--           (pseqtot_ [pint_ 3, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchNestedOr2 with objWrapGenerate matchNestedOr2 using sameSemantics in
--
-- let matchNestedOr3 = symbolize
--   (match_ (seq_ [int_ 3, int_ 7])
--     (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--           (pseqtot_ [pint_ 3, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchNestedOr3 with objWrapGenerate matchNestedOr3 using sameSemantics in
--
-- let matchNestedOr4 = symbolize
--   (match_ (seq_ [int_ 4, int_ 7])
--     (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--           (pseqtot_ [pint_ 3, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchNestedOr4 with objWrapGenerate matchNestedOr4 using sameSemantics in
--
-- let matchNot1 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (pnot_ (pseqtot_ [pint_ 1, pvar_ "a"]))
--     true_
--     false_) in
-- utest matchNot1 with objWrapGenerate matchNot1 using sameSemantics in
--
-- let matchNot2 = symbolize
--   (match_ (seq_ [int_ 2, int_ 2])
--     (pnot_ (pseqtot_ [pint_ 1, pvar_ "a"]))
--     true_
--     false_) in
-- utest matchNot2 with objWrapGenerate matchNot2 using sameSemantics in
--
-- let matchAnd1 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pvar_ "b"))
--     (addi_ (var_ "a") (get_ (var_ "b") (int_ 1)))
--     (int_ 53)) in
-- utest matchAnd1 with objWrapGenerate matchAnd1 using sameSemantics in
--
-- let matchAnd2 = symbolize
--   (match_ (seq_ [int_ 2, int_ 2])
--     (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pvar_ "b"))
--     (addi_ (var_ "a") (get_ (var_ "b") (int_ 1)))
--     (int_ 53)) in
-- utest matchAnd2 with objWrapGenerate matchAnd2 using sameSemantics in
--
-- let matchAnd3 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ []))
--     (var_ "a")
--     (int_ 53)) in
-- utest matchAnd3 with objWrapGenerate matchAnd3 using sameSemantics in
--
-- let matchAnd4 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (pand_ (pseqtot_ []) (pseqtot_ [pint_ 1, pvar_ "a"]))
--     (var_ "a")
--     (int_ 53)) in
-- utest matchAnd4 with objWrapGenerate matchAnd4 using sameSemantics in
--
-- let matchSeqEdge1 = symbolize
--   (match_ (seq_ [int_ 1])
--     (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
--     (addi_ (var_ "a") (var_ "c"))
--     (int_ 75)) in
-- utest matchSeqEdge1 with objWrapGenerate matchSeqEdge1 using sameSemantics in
--
-- let matchSeqEdge2 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
--     (addi_ (var_ "a") (var_ "c"))
--     (int_ 75)) in
-- utest matchSeqEdge2 with objWrapGenerate matchSeqEdge2 using sameSemantics in
--
-- let matchSeqEdge3 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2, int_ 3])
--     (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
--     (addi_ (var_ "a") (var_ "c"))
--     (int_ 75)) in
-- utest matchSeqEdge3 with objWrapGenerate matchSeqEdge3 using sameSemantics in
--
-- let matchSeqEdge4 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
--     (pseqedge_ [pvar_ "a", pvar_ "d"] "b" [pvar_ "c"])
--     (addi_ (addi_ (var_ "d") (var_ "a")) (var_ "c"))
--     (int_ 75)) in
-- utest matchSeqEdge4 with objWrapGenerate matchSeqEdge4 using sameSemantics in
--
-- let matchSeqEdge5 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
--     (por_ (pseqedge_ [pint_ 2] "b" []) (pseqedge_ [pint_ 1] "b" []))
--     (match_ (var_ "b")
--       (pseqedgew_ [pvar_ "a"] [pvar_ "c"])
--       (addi_ (var_ "a") (var_ "c"))
--       (int_ 84))
--     (int_ 75)) in
-- utest matchSeqEdge5 with objWrapGenerate matchSeqEdge5 using sameSemantics in
--
-- let matchSeqEdge6 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
--     (por_ (pseqedge_ [pint_ 2] "b" []) (pseqedge_ [] "b" [pint_ 4]))
--     (match_ (var_ "b")
--       (pseqedgew_ [pvar_ "a"] [pvar_ "c"])
--       (addi_ (var_ "a") (var_ "c"))
--       (int_ 84))
--     (int_ 75)) in
-- utest matchSeqEdge6 with objWrapGenerate matchSeqEdge6 using sameSemantics in
--
-- let matchSeqEdge7 = symbolize
--   (match_ (seq_ [int_ 1])
--     (pseqedgew_ [pvar_ "a"] [])
--     (var_ "a")
--     (int_ 75)) in
-- utest matchSeqEdge7 with objWrapGenerate matchSeqEdge7 using sameSemantics in
--
-- Ints
let addInt1 = addi_ (int_ 1) (int_ 2) in
let t1 = wallTimeMs () in
let p = objWrapGenerate addInt1 in
let t2 = wallTimeMs () in
let _ = print (join ["\n-- objWrapGenerate: ", float2string (divf (subf t2 t1) 1000.), " s\n"]) in
utest addInt1 with p using sameSemantics in

-- let addInt2 = addi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
-- utest addInt2 with p using sameSemantics in

-- let testMulInt = muli_ (int_ 2) (int_ 3) in
-- utest testMulInt with objWrapGenerate testMulInt using sameSemantics in
--
-- let testModInt = modi_ (int_ 2) (int_ 3) in
-- utest testModInt with objWrapGenerate testModInt using sameSemantics in
--
-- let testDivInt = divi_ (int_ 2) (int_ 3) in
-- utest testDivInt with objWrapGenerate testDivInt using sameSemantics in
--
-- let testNegInt = addi_ (int_ 2) (negi_ (int_ 2)) in
-- utest testNegInt with objWrapGenerate testNegInt using sameSemantics in
--
-- let compareInt1 = eqi_ (int_ 1) (int_ 2) in
-- utest compareInt1 with objWrapGenerate compareInt1 using sameSemantics in
--
-- let compareInt2 = lti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
-- utest compareInt2 with objWrapGenerate compareInt2 using sameSemantics in
--
-- let compareInt3 = leqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
-- utest compareInt3 with objWrapGenerate compareInt3 using sameSemantics in
--
-- let compareInt4 = gti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
-- utest compareInt4 with objWrapGenerate compareInt4 using sameSemantics in
--
-- let compareInt5 = geqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
-- utest compareInt5 with objWrapGenerate compareInt5 using sameSemantics in
--
-- let compareInt6 = neqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
-- utest compareInt6 with objWrapGenerate compareInt6 using sameSemantics in
--
-- let shiftInt1 = slli_ (int_ 5) (int_ 2) in
-- utest shiftInt1 with objWrapGenerate shiftInt1 using sameSemantics in
--
-- let shiftInt2 = srli_ (int_ 5) (int_ 2) in
-- utest shiftInt2 with objWrapGenerate shiftInt2 using sameSemantics in
--
-- let shiftInt3 = srai_ (int_ 5) (int_ 2) in
-- utest shiftInt3 with objWrapGenerate shiftInt3 using sameSemantics in
--
-- -- Floats
-- let addFloat1 = addf_ (float_ 1.) (float_ 2.) in
-- utest addFloat1 with objWrapGenerate addFloat1 using sameSemantics in
--
-- let addFloat2 = addf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
-- utest addFloat2 with objWrapGenerate addFloat2 using sameSemantics in
--
-- let testMulFloat = mulf_ (float_ 2.) (float_ 3.) in
-- utest testMulFloat with objWrapGenerate testMulFloat using sameSemantics in
--
-- let testDivFloat = divf_ (float_ 6.) (float_ 3.) in
-- utest testDivFloat with objWrapGenerate testDivFloat using sameSemantics in
--
-- let testNegFloat = addf_ (float_ 2.) (negf_ (float_ 2.)) in
-- utest testNegFloat with objWrapGenerate testNegFloat using sameSemantics in
--
-- let compareFloat1 = eqf_ (float_ 1.) (float_ 2.) in
-- utest compareFloat1 with objWrapGenerate compareFloat1 using sameSemantics in
--
-- let compareFloat2 = ltf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
-- utest compareFloat2 with objWrapGenerate compareFloat2 using sameSemantics in
--
-- let compareFloat3 = leqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
-- utest compareFloat3 with objWrapGenerate compareFloat3 using sameSemantics in
--
-- let compareFloat4 = gtf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
-- utest compareFloat4 with objWrapGenerate compareFloat4 using sameSemantics in
--
-- let compareFloat5 = geqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
-- utest compareFloat5 with objWrapGenerate compareFloat5 using sameSemantics in
--
-- let compareFloat6 = neqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
-- utest compareFloat6 with objWrapGenerate compareFloat6 using sameSemantics in
--
-- -- Chars
-- let charLiteral = char_ 'c' in
-- utest charLiteral with objWrapGenerate charLiteral
-- using sameSemantics in
--
-- let compareChar1 = eqc_ (char_ 'a') (char_ 'b') in
-- utest compareChar1 with objWrapGenerate compareChar1 using sameSemantics in
--
-- let compareChar2 = eqc_ (char_ 'a') (char_ 'a') in
-- utest compareChar2 with objWrapGenerate compareChar2 using sameSemantics in
--
-- let testCharToInt = char2int_ (char_ '0') in
-- utest testCharToInt with objWrapGenerate testCharToInt using sameSemantics in
--
-- let testIntToChar = int2char_ (int_ 48) in
-- utest testIntToChar with objWrapGenerate testIntToChar using sameSemantics in
--
-- -- Abstractions
-- let fun =
--   symbolize
--   (appSeq_
--     (ulam_ "@" (ulam_ "%" (addi_ (var_ "@") (var_ "%"))))
--     [int_ 1, int_ 2])
-- in
-- utest fun with objWrapGenerate fun using sameSemantics in
--
-- let funShadowed =
--   symbolize
--   (appSeq_
--     (ulam_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))))
--     [ulam_ "@" (var_ "@"), int_ 2])
-- in
-- utest funShadowed with objWrapGenerate funShadowed using sameSemantics in
--
-- -- Lets
-- let testLet =
--   symbolize
--   (bindall_ [ulet_ "^" (int_ 1), addi_ (var_ "^") (int_ 2)])
-- in
-- utest testLet with objWrapGenerate testLet using sameSemantics in
--
-- let testLetShadowed =
--   symbolize
--   (bindall_ [ulet_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))),
--              app_ (var_ "@") (int_ 1)])
-- in
-- utest testLetShadowed with objWrapGenerate testLetShadowed
-- using sameSemantics in
--
-- let testLetRec =
--   symbolize
--   (bind_
--      (ureclets_add "$" (ulam_ "%" (app_ (var_ "@") (int_ 1)))
--      (ureclets_add "@" (ulam_ "" (var_ ""))
--      reclets_empty))
--    (app_ (var_ "$") (var_ "@")))
-- in
-- utest testLetRec with objWrapGenerate testLetRec using sameSemantics in
--
-- -- Sequences
-- let testEmpty = symbolize (length_ (seq_ [])) in
-- utest testEmpty with objWrapGenerate testEmpty using sameSemantics in
--
-- let nonEmpty = seq_ [int_ 1, int_ 2, int_ 3] in
-- let len = length_ nonEmpty in
-- let fst = get_ nonEmpty (int_ 0) in
-- let snd = get_ nonEmpty (int_ 1) in
-- let thrd = get_ nonEmpty (int_ 2) in
-- utest int_ 3 with objWrapGenerate len using sameSemantics in
-- utest int_ 1 with objWrapGenerate fst using sameSemantics in
-- utest int_ 2 with objWrapGenerate snd using sameSemantics in
-- utest int_ 3 with objWrapGenerate thrd using sameSemantics in
--
-- let testMake = makeseq_ (int_ 2) (int_ 0) in
-- let len = length_ testMake in
-- let fst = get_ testMake (int_ 0) in
-- let lst = get_ testMake (int_ 1) in
-- utest int_ 2 with objWrapGenerate len using sameSemantics in
-- utest int_ 0 with objWrapGenerate fst using sameSemantics in
-- utest int_ 0 with objWrapGenerate lst using sameSemantics in
--
-- let testSet = set_ (seq_ [int_ 1, int_ 2]) (int_ 0) (int_ 3) in
-- let len = length_ testSet in
-- let fst = get_ testSet (int_ 0) in
-- let snd = get_ testSet (int_ 1) in
-- utest int_ 2 with objWrapGenerate len using sameSemantics in
-- utest int_ 3 with objWrapGenerate fst using sameSemantics in
-- utest int_ 2 with objWrapGenerate snd using sameSemantics in
--
-- let testCons = cons_  (int_ 1) (seq_ [int_ 2, int_ 3]) in
-- let len = length_ testCons in
-- let fst = get_ testCons (int_ 0) in
-- let snd = get_ testCons (int_ 1) in
-- let thrd = get_ testCons (int_ 2) in
-- utest int_ 3 with objWrapGenerate len using sameSemantics in
-- utest int_ 1 with objWrapGenerate fst using sameSemantics in
-- utest int_ 2 with objWrapGenerate snd using sameSemantics in
-- utest int_ 3 with objWrapGenerate thrd using sameSemantics in
--
-- let testSnoc = snoc_ (seq_ [int_ 1, int_ 2]) (int_ 3) in
-- let len = length_ testSnoc in
-- let fst = get_ testSnoc (int_ 0) in
-- let snd = get_ testSnoc (int_ 1) in
-- let thrd = get_ testSnoc (int_ 2) in
-- utest int_ 3 with objWrapGenerate len using sameSemantics in
-- utest int_ 1 with objWrapGenerate fst using sameSemantics in
-- utest int_ 2 with objWrapGenerate snd using sameSemantics in
-- utest int_ 3 with objWrapGenerate thrd using sameSemantics in
--
-- let testReverse = reverse_ (seq_ [int_ 1, int_ 2, int_ 3]) in
-- let len = length_ testReverse in
-- let fst = get_ testReverse (int_ 0) in
-- let snd = get_ testReverse (int_ 1) in
-- let thrd = get_ testReverse (int_ 2) in
-- utest int_ 3 with objWrapGenerate len using sameSemantics in
-- utest int_ 3 with objWrapGenerate fst using sameSemantics in
-- utest int_ 2 with objWrapGenerate snd using sameSemantics in
-- utest int_ 1 with objWrapGenerate thrd using sameSemantics in
--
-- -- TODO(Oscar Eriksson, 2020-11-16) Test splitAt when we have implemented tuple
-- -- projection.
--
-- -- TODO(Oscar Eriksson, 2020-11-30) Test symbol operations when we have
-- -- implemented tuples/records.
--
-- -- Float-Integer conversions
-- let testFloorfi = floorfi_ (float_ 1.5) in
-- utest testFloorfi with objWrapGenerate testFloorfi using sameSemantics in
--
-- let testCeilfi = ceilfi_ (float_ 1.5) in
-- utest testCeilfi with objWrapGenerate testCeilfi using sameSemantics in
--
-- let testRoundfi = roundfi_ (float_ 1.5) in
-- utest testRoundfi with objWrapGenerate testRoundfi using sameSemantics in
--
-- let testInt2float = int2float_ (int_ 1) in
-- utest testInt2float with objWrapGenerate testInt2float using sameSemantics in
--
-- let testString2float = string2float_ (str_ "1.5") in
-- utest testString2float with objWrapGenerate testString2float using sameSemantics in
--
-- -- File operations
-- let testFileExists = fileExists_ (str_ "test_file_ops") in
-- utest testFileExists with objWrapGenerate testFileExists using sameSemantics in

-- IO operations
-- let testPrint = print_ (str_ "tested print") in
-- utest testPrint with generate testPrint using sameSemantics in

-- Random number generation operations
-- let testUnseededRandomNumber = randIntU_ (int_ 1) (int_ 4) in
-- utest testUnseededRandomNumber with objWrapGenerate testUnseededRandomNumber
-- using sameSemantics in

-- let testSeededRandomNumber =
--  symbolize
--  (bindall_ [ulet_ "_" (randSetSeed_ (int_ 42)),
--             randIntU_ (int_ 0) (int_ 10)])
-- in
-- utest testSeededRandomNumber with objWrapGenerate testSeededRandomNumber
-- using sameSemantics in

-- Time operations

-- NOTE(larshum, 2020-12-14): Cannot test time operations until unit types
-- are supported.

-- let testWallTimeMs = wallTimeMs_ unit_ in
-- utest testWallTimeMs with objWrapGenerate testWallTimeMs using sameSemantics in

-- let testSleepMs = sleepMs_ (int_ 10) in
-- utest testSleepMs with objWrapGenerate testSleepMs using sameSemantics in

-- TODO(oerikss, 2020-12-14): Sys operations are not tested

-- Obj wrap
-- let add = objWrap (addi_ (int_ 1) (int_ 2)) in
-- utest add with objWrapGenerate add using sameSemantics in
-- let _ = dprint w in

()
