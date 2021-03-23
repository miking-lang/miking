include "mexpr/ast.mc"
include "map.mc"
include "stringid.mc"

let _intType = use MExprAst in TyInt {info = NoInfo ()}
let _floatType = use MExprAst in TyFloat {info = NoInfo ()}
let _boolType = use MExprAst in TyBool {info = NoInfo ()}
let _charType = use MExprAst in TyChar {info = NoInfo ()}
let _unknownType = use MExprAst in TyUnknown {info = NoInfo ()}

let _seqType = use MExprAst in
  lam elemTy.
  TySeq {ty = elemTy, info = NoInfo ()}
let _strType = _seqType _charType
let _arrowType = use MExprAst in
  lam from. lam to.
  TyArrow {from = from, to = to, info = NoInfo ()}
let _recordType = use MExprAst in
  lam fields.
  TyRecord {
    fields = mapFromList cmpSID (map (lam b. (stringToSid b.0, b.1)) fields),
    info = NoInfo ()
  }
let _tupleType = lam types.
  _recordType (mapi (lam i. lam ty. (int2string i, ty)) types)
let _unitType = _recordType []

-- Use TyUnknown as a placeholder for terms that cannot be represented using
-- the existing types.
let _symType = _unknownType
let _refType = _unknownType
let _mapType = _unknownType
let _tensorType = _unknownType
let _parseTreeType = _unknownType
let _genericType = _unknownType
let _genericSeqType = _seqType _genericType

let builtin = use MExprAst in
  [ ("addi", CAddi (), _arrowType _intType (_arrowType _intType _intType))
  , ("subi", CSubi (), _arrowType _intType (_arrowType _intType _intType))
  , ("muli", CMuli (), _arrowType _intType (_arrowType _intType _intType))
  , ("divi", CDivi (), _arrowType _intType (_arrowType _intType _intType))
  , ("modi", CModi (), _arrowType _intType (_arrowType _intType _intType))
  , ("negi", CNegi (), _arrowType _intType _intType)
  , ("lti", CLti (), _arrowType _intType (_arrowType _intType _boolType))
  , ("leqi", CLeqi (), _arrowType _intType (_arrowType _intType _boolType))
  , ("gti", CGti (), _arrowType _intType (_arrowType _intType _boolType))
  , ("geqi", CGeqi (), _arrowType _intType (_arrowType _intType _boolType))
  , ("eqi", CEqi (), _arrowType _intType (_arrowType _intType _boolType))
  , ("neqi", CNeqi (), _arrowType _intType (_arrowType _intType _boolType))
  , ("slli", CSlli (), _arrowType _intType (_arrowType _intType _intType))
  , ("srli", CSrli (), _arrowType _intType (_arrowType _intType _intType))
  , ("srai", CSrai (), _arrowType _intType (_arrowType _intType _intType))
  -- , ("arity", Carity ())   -- Arity is not yet implemented
  -- Floating-point numbers
  , ("addf", CAddf (), _arrowType _floatType (_arrowType _floatType _floatType))
  , ("subf", CSubf (), _arrowType _floatType (_arrowType _floatType _floatType))
  , ("mulf", CMulf (), _arrowType _floatType (_arrowType _floatType _floatType))
  , ("divf", CDivf (), _arrowType _floatType (_arrowType _floatType _floatType))
  , ("negf", CNegf (), _arrowType _floatType _floatType)
  , ("ltf", CLtf (), _arrowType _floatType (_arrowType _floatType _boolType))
  , ("leqf", CLeqf (), _arrowType _floatType (_arrowType _floatType _boolType))
  , ("gtf", CGtf (), _arrowType _floatType (_arrowType _floatType _boolType))
  , ("geqf", CGeqf (), _arrowType _floatType (_arrowType _floatType _boolType))
  , ("eqf", CEqf (), _arrowType _floatType (_arrowType _floatType _boolType))
  , ("neqf", CNeqf (), _arrowType _floatType (_arrowType _floatType _boolType))
  , ("floorfi", CFloorfi (), _arrowType _floatType _intType)
  , ("ceilfi", CCeilfi (), _arrowType _floatType _intType)
  , ("roundfi", CRoundfi (), _arrowType _floatType _intType)
  , ("int2float", CInt2float (), _arrowType _intType _floatType)
  , ("string2float", CString2float (), _arrowType _strType _floatType)
  -- Characters
  , ("eqc", CEqc (), _arrowType _charType (_arrowType _charType _boolType))
  , ("char2int", CChar2Int (), _arrowType _intType _charType)
  , ("int2char", CInt2Char (), _arrowType _charType _intType)
  -- Sequences
  , ("create", CCreate (),
      _arrowType
        _intType
        (_arrowType (_arrowType _intType _genericType)
                    _genericSeqType))
  , ("length", CLength (), _arrowType _genericSeqType _intType)
  , ("concat", CConcat (),
      _arrowType _genericSeqType
                 (_arrowType _genericSeqType _genericSeqType))
  , ("get", CGet (),
      _arrowType _genericSeqType
                 (_arrowType _intType _genericSeqType))
  , ("set", CSet (),
      _arrowType _genericSeqType
                 (_arrowType _intType (_arrowType _genericType _genericSeqType)))
  , ("cons", CCons (),
      _arrowType _genericType
                 (_arrowType _genericSeqType _genericSeqType))
  , ("snoc", CSnoc (),
      _arrowType _genericSeqType
                 (_arrowType _genericType _genericSeqType))
  , ("splitAt", CSplitAt (),
      _arrowType _genericSeqType
                 (_arrowType _intType
                             (_tupleType [_genericSeqType, _genericSeqType])))
  , ("reverse", CReverse (), _arrowType _genericSeqType _genericSeqType)
  , ("subsequence", CSubsequence (),
      _arrowType _genericSeqType
                 (_arrowType _intType
                             (_arrowType _intType _genericSeqType)))
  -- Random numbers
  , ("randIntU", CRandIntU (),
      _arrowType _intType (_arrowType _intType _intType))
  , ("randSetSeed", CRandSetSeed (), _arrowType _intType _unitType)
  -- MCore intrinsics: Time
  , ("wallTimeMs", CWallTimeMs (), _arrowType _unitType _floatType)
  , ("sleepMs", CSleepMs (), _arrowType _intType _unitType)
  -- MCore intrinsics: Debug and I/O
  , ("print", CPrint (), _arrowType _strType _unitType)
  , ("dprint", CDPrint (), _arrowType _strType _unitType)
  , ("readLine", CReadLine (), _arrowType _unitType _strType)
  , ("readBytesAsString", CReadBytesAsString (),
      _arrowType _intType (_tupleType [_strType, _strType]))
  , ("argv", CArgv (), _seqType _strType)
  , ("readFile", CFileRead (), _arrowType _strType _strType)
  , ("writeFile", CFileWrite (),
      _arrowType _strType (_arrowType _strType _unitType))
  , ("fileExists", CFileExists (), _arrowType _strType _boolType)
  , ("deleteFile", CFileDelete (), _arrowType _strType _unitType)
  , ("error", CError (), _arrowType _intType _unknownType)
  , ("exit", CExit (), _arrowType _intType _unknownType)
  -- Symbols
  , ("eqsym", CEqsym (), _arrowType _symType (_arrowType _symType _boolType))
  , ("gensym", CGensym (), _arrowType _unitType _symType)
  , ("sym2hash", CSym2hash (), _arrowType _symType _intType)
  -- References
  , ("ref", CRef (), _arrowType _genericType _refType)
  , ("deref", CDeRef (), _arrowType _refType _genericType)
  , ("modref", CModRef (), _arrowType _refType (_arrowType _genericType _unitType))
  -- Maps
  , ("mapEmpty", CMapEmpty (),
      _arrowType (_arrowType _genericType (_arrowType _genericType _intType)) _mapType)
  , ("mapSize", CMapSize (), _arrowType _mapType _intType)
  , ("mapGetCmpFun", CMapGetCmpFun (),
      _arrowType _mapType
                 (_arrowType _genericType (_arrowType _genericType _intType)))
  , ("mapInsert", CMapInsert (),
      _arrowType _genericType (_arrowType _genericType (_arrowType _mapType _mapType)))
  , ("mapRemove", CMapRemove (),
      _arrowType _genericType (_arrowType _genericType _mapType))
  , ("mapFindWithExn", CMapFindWithExn (),
      _arrowType _genericType (_arrowType _mapType _genericType))
  , ("mapFindOrElse", CMapFindOrElse (),
      _arrowType (_arrowType _unitType _genericType)
                 (_arrowType _genericType (_arrowType _mapType _mapType)))
  , ("mapFindApplyOrElse", CMapFindApplyOrElse (),
      _arrowType (_arrowType _genericType _genericType)
                 (_arrowType (_arrowType _unitType _genericType)
                             (_arrowType _genericType
                                         (_arrowType _mapType _genericType))))
  , ("mapAny", CMapAny (),
      _arrowType (_arrowType _genericType (_arrowType _genericType _boolType))
                 (_arrowType _mapType _boolType))
  , ("mapMem", CMapMem (),
     _arrowType _genericType (_arrowType _mapType _boolType))
  , ("mapMap", CMapMap (),
      _arrowType (_arrowType _genericType _genericType)
                 (_arrowType _mapType _mapType))
  , ("mapMapWithKey", CMapMapWithKey (),
      _arrowType (_arrowType _genericType (_arrowType _genericType _genericType))
                 (_arrowType _mapType _mapType))
  , ("mapFoldWithKey", CMapFoldWithKey (),
      _arrowType
        (_arrowType _genericType
                    (_arrowType _genericType
                                (_arrowType _genericType _genericType)))
        (_arrowType _genericType (_arrowType _mapType _mapType)))
  , ("mapBindings", CMapBindings (),
      _arrowType _mapType (_seqType (_tupleType [_genericType, _genericType])))
  , ("mapEq", CMapEq (),
      _arrowType (_arrowType _genericType (_arrowType _genericType _boolType))
                 (_arrowType _mapType (_arrowType _mapType _boolType)))
  , ("mapCmp", CMapCmp (),
      _arrowType (_arrowType _genericType (_arrowType _genericType _intType))
                 (_arrowType _mapType (_arrowType _mapType _intType)))
  -- Tensors
  , ("tensorCreate", CTensorCreate (),
      _arrowType (_seqType _intType)
                 (_arrowType (_seqType _intType) _tensorType))
  , ("tensorGetExn", CTensorGetExn (),
      _arrowType _tensorType
                 (_arrowType (_seqType _intType) _tensorType))
  , ("tensorSetExn", CTensorSetExn (),
      _arrowType _tensorType
                 (_arrowType (_seqType _intType)
                             (_arrowType _unknownType _unitType)))
  , ("tensorRank", CTensorRank (), _arrowType _tensorType _intType)
  , ("tensorShape", CTensorShape (), _arrowType _tensorType (_seqType _intType))
  , ("tensorReshapeExn", CTensorReshapeExn (),
      _arrowType _tensorType (_arrowType (_seqType _intType) _tensorType))
  , ("tensorCopyExn", CTensorCopyExn (),
      _arrowType _tensorType (_arrowType _tensorType _unknownType))
  , ("tensorSliceExn", CTensorSliceExn (),
      _arrowType _tensorType (_arrowType (_seqType _intType) _tensorType))
  , ("tensorSubExn", CTensorSubExn (),
      _arrowType _tensorType
                 (_arrowType _intType (_arrowType _intType _tensorType)))
  , ("tensorIteri", CTensorIteri (),
      _arrowType (_arrowType _intType (_arrowType _tensorType _unitType))
                 (_arrowType _tensorType _unitType))
  -- Boot parser
  , ("bootParserParseMExprString", CBootParserParseMExprString (),
      _arrowType _strType _parseTreeType)
  , ("bootParserParseMCoreFile", CBootParserParseMCoreFile (),
      _arrowType _strType _parseTreeType)
  , ("bootParserGetId", CBootParserGetId (),
      _arrowType _parseTreeType _intType)
  , ("bootParserGetTerm", CBootParserGetTerm (),
      _arrowType _parseTreeType _parseTreeType)
  , ("bootParserGetType", CBootParserGetType (),
      _arrowType _parseTreeType _parseTreeType)
  , ("bootParserGetString", CBootParserGetString (),
      _arrowType _parseTreeType _strType)
  , ("bootParserGetInt", CBootParserGetInt (),
      _arrowType _parseTreeType _intType)
  , ("bootParserGetFloat", CBootParserGetFloat (),
      _arrowType _parseTreeType _floatType)
  , ("bootParserGetListLength", CBootParserGetListLength (),
      _arrowType _parseTreeType _intType)
  , ("bootParserGetConst", CBootParserGetConst (),
      _arrowType _parseTreeType _parseTreeType)
  , ("bootParserGetPat", CBootParserGetPat (),
      _arrowType _parseTreeType _parseTreeType)
  , ("bootParserGetInfo", CBootParserGetInfo (),
      _arrowType _parseTreeType _parseTreeType)
  ]

let builtinStrNodeType = use MExprAst in
  map
    (lam x.
      match x with (s,c,ty) then
        ( nameSym s
        , TmConst {val = c, ty = TyUnknown (), info = NoInfo ()}
        , ty)
      else never)
    builtin

let builtinEnv = use MExprAst in
  map (lam x. (x.0, x.1)) builtinStrNodeType

let builtinNames : [Name] = map (lam intr. intr.0) builtinEnv

let builtinNameMap : Map String Name =
  mapFromList cmpString (map (lam x. (nameGetStr x.0, x.0)) builtinEnv)

let builtinIntrinsicName : String -> Name = lam str.
  match mapLookup str builtinNameMap with Some name then
    name
  else error (join ["Could not find intrinsic: ", str])

let builtinNameTypeMap : Map Name Type =
  mapFromList nameCmp (map (lam x. (x.0, x.2)) builtinStrNodeType)
