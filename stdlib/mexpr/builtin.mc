include "mexpr/ast.mc"
include "mexpr/const-types.mc"
include "map.mc"
include "stringid.mc"

let builtin = use MExprAst in
  [ ("addi", CAddi ())
  , ("subi", CSubi ())
  , ("muli", CMuli ())
  , ("divi", CDivi ())
  , ("modi", CModi ())
  , ("negi", CNegi ())
  , ("lti", CLti ())
  , ("leqi", CLeqi ())
  , ("gti", CGti ())
  , ("geqi", CGeqi ())
  , ("eqi", CEqi ())
  , ("neqi", CNeqi ())
  , ("slli", CSlli ())
  , ("srli", CSrli ())
  , ("srai", CSrai ())
  -- , ("arity", Carity ())   -- Arity is not yet implemented
  -- Floating-point numbers
  , ("addf", CAddf ())
  , ("subf", CSubf ())
  , ("mulf", CMulf ())
  , ("divf", CDivf ())
  , ("negf", CNegf ())
  , ("ltf", CLtf ())
  , ("leqf", CLeqf ())
  , ("gtf", CGtf ())
  , ("geqf", CGeqf ())
  , ("eqf", CEqf ())
  , ("neqf", CNeqf ())
  , ("floorfi", CFloorfi ())
  , ("ceilfi", CCeilfi ())
  , ("roundfi", CRoundfi ())
  , ("int2float", CInt2float ())
  , ("string2float", CString2float ())
  -- Characters
  , ("eqc", CEqc ())
  , ("char2int", CChar2Int ())
  , ("int2char", CInt2Char ())
  -- Sequences
  , ("create", CCreate ())
  , ("length", CLength ())
  , ("concat", CConcat ())
  , ("get", CGet ())
  , ("set", CSet ())
  , ("cons", CCons ())
  , ("snoc", CSnoc ())
  , ("splitAt", CSplitAt ())
  , ("reverse", CReverse ())
  , ("subsequence", CSubsequence ())
  -- Random numbers
  , ("randIntU", CRandIntU ())
  , ("randSetSeed", CRandSetSeed ())
  -- MCore intrinsics: Time
  , ("wallTimeMs", CWallTimeMs ())
  , ("sleepMs", CSleepMs ())
  -- MCore intrinsics: Debug and I/O
  , ("print", CPrint ())
  , ("dprint", CDPrint ())
  , ("readLine", CReadLine ())
  , ("readBytesAsString", CReadBytesAsString ())
  , ("argv", CArgv ())
  , ("readFile", CFileRead ())
  , ("writeFile", CFileWrite ())
  , ("fileExists", CFileExists ())
  , ("deleteFile", CFileDelete ())
  , ("error", CError ())
  , ("exit", CExit ())
  -- Symbols
  , ("eqsym", CEqsym ())
  , ("gensym", CGensym ())
  , ("sym2hash", CSym2hash ())
  -- References
  , ("ref", CRef ())
  , ("deref", CDeRef ())
  , ("modref", CModRef ())
  -- Maps
  , ("mapEmpty", CMapEmpty ())
  , ("mapSize", CMapSize ())
  , ("mapGetCmpFun", CMapGetCmpFun ())
  , ("mapInsert", CMapInsert ())
  , ("mapRemove", CMapRemove ())
  , ("mapFindWithExn", CMapFindWithExn ())
  , ("mapFindOrElse", CMapFindOrElse ())
  , ("mapFindApplyOrElse", CMapFindApplyOrElse ())
  , ("mapAny", CMapAny ())
  , ("mapMem", CMapMem ())
  , ("mapMap", CMapMap ())
  , ("mapMapWithKey", CMapMapWithKey ())
  , ("mapFoldWithKey", CMapFoldWithKey ())
  , ("mapBindings", CMapBindings ())
  , ("mapEq", CMapEq ())
  , ("mapCmp", CMapCmp ())
  -- Tensors
  , ("tensorCreate", CTensorCreate ())
  , ("tensorGetExn", CTensorGetExn ())
  , ("tensorSetExn", CTensorSetExn ())
  , ("tensorRank", CTensorRank ())
  , ("tensorShape", CTensorShape ())
  , ("tensorReshapeExn", CTensorReshapeExn ())
  , ("tensorCopyExn", CTensorCopyExn ())
  , ("tensorSliceExn", CTensorSliceExn ())
  , ("tensorSubExn", CTensorSubExn ())
  , ("tensorIteri", CTensorIteri ())
  -- Boot parser
  , ("bootParserParseMExprString", CBootParserParseMExprString ())
  , ("bootParserParseMCoreFile", CBootParserParseMCoreFile ())
  , ("bootParserGetId", CBootParserGetId ())
  , ("bootParserGetTerm", CBootParserGetTerm ())
  , ("bootParserGetType", CBootParserGetType ())
  , ("bootParserGetString", CBootParserGetString ())
  , ("bootParserGetInt", CBootParserGetInt ())
  , ("bootParserGetFloat", CBootParserGetFloat ())
  , ("bootParserGetListLength", CBootParserGetListLength ())
  , ("bootParserGetConst", CBootParserGetConst ())
  , ("bootParserGetPat", CBootParserGetPat ())
  , ("bootParserGetInfo", CBootParserGetInfo ())
  ]

let builtinEnv : Map Name Expr = use MExprAst in
  mapFromList
    nameCmp
    (map
      (lam x.
        match x with (s,c) then
          (nameSym s, TmConst {val = c, ty = TyUnknown (), info = NoInfo ()})
        else never)
      builtin)

let builtinNames : [Name] = mapKeys builtinEnv

let builtinNameMap : Map String Name =
  mapFromList cmpString (map (lam x. (nameGetStr x, x)) builtinNames)

let builtinNameTypeMap : Map Name Type =
  use ConstAst in
  use MExprConstType in
  mapMap
    (lam v.
      match v with TmConst {val = c} then
        tyConst c
      else never)
    builtinEnv

let builtinPprintNameMap =
  mapFromList nameCmp (map (lam n. (n, nameGetStr n)) builtinNames)

let builtinPprintCount =
  mapFromList cmpString (map (lam n. (nameGetStr n, 1)) builtinNames)

let builtinPprintStrings = mapMap (lam. 0) builtinPprintCount

let builtinPprintEnv =
  { nameMap = builtinPprintNameMap
  , count = builtinPprintCount
  , strings = builtinPprintStrings
  }
