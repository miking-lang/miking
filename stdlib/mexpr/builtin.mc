include "ast.mc"
include "ast-builder.mc"

let builtin = use MExprAst in
  [ ("addi", CAddi (), tyarrow_ tyint_ (tyarrow_ tyint_ tyint_))
  , ("subi", CSubi (), tyarrow_ tyint_ (tyarrow_ tyint_ tyint_))
  , ("muli", CMuli (), tyarrow_ tyint_ (tyarrow_ tyint_ tyint_))
  , ("divi", CDivi (), tyarrow_ tyint_ (tyarrow_ tyint_ tyint_))
  , ("modi", CModi (), tyarrow_ tyint_ (tyarrow_ tyint_ tyint_))
  , ("negi", CNegi (), tyarrow_ tyint_ tyint_)
  , ("lti", CLti (), tyarrow_ tyint_ (tyarrow_ tyint_ tybool_))
  , ("leqi", CLeqi (), tyarrow_ tyint_ (tyarrow_ tyint_ tybool_))
  , ("gti", CGti (), tyarrow_ tyint_ (tyarrow_ tyint_ tybool_))
  , ("geqi", CGeqi (), tyarrow_ tyint_ (tyarrow_ tyint_ tybool_))
  , ("eqi", CEqi (), tyarrow_ tyint_ (tyarrow_ tyint_ tybool_))
  , ("neqi", CNeqi (), tyarrow_ tyint_ (tyarrow_ tyint_ tybool_))
  , ("slli", CSlli (), tyarrow_ tyint_ (tyarrow_ tyint_ tyint_))
  , ("srli", CSrli (), tyarrow_ tyint_ (tyarrow_ tyint_ tyint_))
  , ("srai", CSrai (), tyarrow_ tyint_ (tyarrow_ tyint_ tyint_))
  -- , ("arity", Carity ())   -- Arity is not yet implemented
  -- Floating-point numbers
  , ("addf", CAddf (), tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_))
  , ("subf", CSubf (), tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_))
  , ("mulf", CMulf (), tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_))
  , ("divf", CDivf (), tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_))
  , ("negf", CNegf (), tyarrow_ tyfloat_ tyfloat_)
  , ("ltf", CLtf (), tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_))
  , ("leqf", CLeqf (), tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_))
  , ("gtf", CGtf (), tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_))
  , ("geqf", CGeqf (), tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_))
  , ("eqf", CEqf (), tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_))
  , ("neqf", CNeqf (), tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_))
  , ("floorfi", CFloorfi (), tyarrow_ tyfloat_ tyint_)
  , ("ceilfi", CCeilfi (), tyarrow_ tyfloat_ tyint_)
  , ("roundfi", CRoundfi (), tyarrow_ tyfloat_ tyint_)
  , ("int2float", CInt2float (), tyarrow_ tyint_ tyfloat_)
  , ("string2float", CString2float (), tyarrow_ tystr_ tyfloat_)
  -- Characters
  , ("eqc", CEqc (), tyarrow_ tychar_ (tyarrow_ tychar_ tybool_))
  , ("char2int", CChar2Int (), tyarrow_ tyint_ tychar_)
  , ("int2char", CInt2Char (), tyarrow_ tychar_ tyint_)
  -- Sequences
  , ("create", CCreate (),
     tyarrow_ tyint_ (tyarrow_ (tyarrow_ tyint_ tyunknown_) utyseq_))
  , ("length", CLength (), tyarrow_ utyseq_ tyint_)
  , ("concat", CConcat (), tyarrow_ utyseq_ (tyarrow_ utyseq_ utyseq_))
  , ("get", CGet (), tyarrow_ utyseq_ (tyarrow_ tyint_ utyseq_))
  , ("set", CSet (),
     tyarrow_ utyseq_ (tyarrow_ tyint_ (tyarrow_ tyunknown_ utyseq_)))
  , ("cons", CCons (), tyarrow_ tyunknown_ (tyarrow_ utyseq_ utyseq_))
  , ("snoc", CSnoc (), tyarrow_ utyseq_ (tyarrow_ tyunknown_ utyseq_))
  , ("splitAt", CSplitAt (),
     tyarrow_ utyseq_ (tyarrow_ tyint_ (tytuple_ [utyseq_, utyseq_])))
  , ("reverse", CReverse (), tyarrow_ utyseq_ utyseq_)
  , ("subsequence", CSubsequence (),
     tyarrow_ utyseq_ (tyarrow_ tyint_ (tyarrow_ tyint_ utyseq_)))
  -- Random numbers
  , ("randIntU", CRandIntU (), tyarrow_ tyint_ (tyarrow_ tyint_ tyint_))
  , ("randSetSeed", CRandSetSeed (), tyarrow_ tyint_ tyunit_)
  -- MCore intrinsics: Time
  , ("wallTimeMs", CWallTimeMs (), tyarrow_ tyunit_ tyfloat_)
  , ("sleepMs", CSleepMs (), tyarrow_ tyint_ tyunit_)
  -- MCore intrinsics: Debug and I/O
  , ("print", CPrint (), tyarrow_ tystr_ tyunit_)
  , ("dprint", CDPrint (), tyarrow_ tystr_ tyunit_)
  , ("readLine", CReadLine (), tyarrow_ tyunit_ tystr_)
  , ("readBytesAsString", CReadBytesAsString (),
     tyarrow_ tyint_ (tytuple_ [tystr_, tystr_]))
  , ("argv", CArgv (), tyseq_ tystr_)
  , ("readFile", CFileRead (), tyarrow_ tystr_ tystr_)
  , ("writeFile", CFileWrite (), tyarrow_ tystr_ (tyarrow_ tystr_ tyunit_))
  , ("fileExists", CFileExists (), tyarrow_ tystr_ tybool_)
  , ("deleteFile", CFileDelete (), tyarrow_ tystr_ tyunit_)
  , ("error", CError (), tyarrow_ tyint_ tyunknown_)
  , ("exit", CExit (), tyarrow_ tyint_ tyunknown_)
  -- Symbols
  , ("eqsym", CEqsym (), tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tybool_))
  , ("gensym", CGensym (), tyarrow_ tyunit_ tyunknown_)
  , ("sym2hash", CSym2hash (), tyarrow_ tyunknown_ tyint_)
  -- References
  , ("ref", CRef (), tyarrow_ tyunknown_ tyunknown_)
  , ("deref", CDeRef (), tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunit_))
  , ("modref", CModRef (), tyarrow_ tyunknown_ tyunknown_)
  -- Maps
  , ("mapEmpty", CMapEmpty (),
     tyarrow_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyint_)) tyunknown_)
  , ("mapSize", CMapSize (), tyarrow_ tyunknown_ tyint_)
  , ("mapGetCmpFun", CMapGetCmpFun (),
     tyarrow_ tyunknown_ (tyarrow_ tyunknown_
                         (tyarrow_ tyunknown_ tyint_)))
  , ("mapInsert", CMapInsert (),
     tyarrow_ tyunknown_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_)))
  , ("mapRemove", CMapRemove (),
     tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_))
  , ("mapFindWithExn", CMapFindWithExn (),
     tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_))
  , ("mapFindOrElse", CMapFindOrElse (),
     tyarrow_ (tyarrow_ tyunit_ tyunknown_)
              (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_)))
  , ("mapFindApplyOrElse", CMapFindApplyOrElse (),
     tyarrow_ (tyarrow_ tyunknown_ tyunknown_)
              (tyarrow_ (tyarrow_ tyunit_ tyunknown_)
                        (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_))))
  , ("mapAny", CMapAny (),
     tyarrow_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tybool_))
              (tyarrow_ tyunknown_ tybool_))
  , ("mapMem", CMapMem (),
     tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tybool_))
  , ("mapMap", CMapMap (),
     tyarrow_ (tyarrow_ tyunknown_ tyunknown_)
              (tyarrow_ tyunknown_ tyunknown_))
  , ("mapMapWithKey", CMapMapWithKey (),
     tyarrow_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_))
              (tyarrow_ tyunknown_ tyunknown_))
  , ("mapFoldWithKey", CMapFoldWithKey (),
     tyarrow_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_)))
              (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_)))
  , ("mapBindings", CMapBindings (),
     tyarrow_ tyunknown_ (tyseq_ (tytuple_ [tyunknown_, tyunknown_])))
  , ("mapEq", CMapEq (),
     tyarrow_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tybool_))
              (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tybool_)))
  , ("mapCmp", CMapCmp (),
     tyarrow_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyint_))
              (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyint_)))
  -- Tensors
  , ("tensorCreate", CTensorCreate (),
     tyarrow_ (tyseq_ tyint_)
              (tyarrow_ (tyseq_ tyint_) tyunknown_))
  , ("tensorGetExn", CTensorGetExn (),
     tyarrow_ tyunknown_
              (tyarrow_ (tyseq_ tyint_) tyunknown_))
  , ("tensorSetExn", CTensorSetExn (),
     tyarrow_ tyunknown_
              (tyarrow_ (tyseq_ tyint_)
                        (tyarrow_ tyunknown_ tyunit_)))
  , ("tensorRank", CTensorRank (), tyarrow_ tyunknown_ tyint_)
  , ("tensorShape", CTensorShape (), tyarrow_ tyunknown_ (tyseq_ tyint_))
  , ("tensorReshapeExn", CTensorReshapeExn (),
     tyarrow_ tyunknown_ (tyarrow_ (tyseq_ tyint_) tyunknown_))
  , ("tensorCopyExn", CTensorCopyExn (), tyarrow_ tyunknown_ tyunknown_)
  , ("tensorSliceExn", CTensorSliceExn (),
     tyarrow_ tyunknown_ (tyarrow_ (tyseq_ tyint_) tyunknown_))
  , ("tensorSubExn", CTensorSubExn (),
     tyarrow_ tyunknown_
              (tyarrow_ tyint_ (tyarrow_ tyint_ tyunknown_)))
  , ("tensorIteri", CTensorIteri (),
     tyarrow_ (tyarrow_ tyint_ (tyarrow_ tyunknown_ tyunit_))
              (tyarrow_ tyunknown_ tyunit_))
  -- Boot parser
  , ("bootParserParseMExprString", CBootParserParseMExprString (),
     tyarrow_ tystr_ tyunknown_)
  , ("bootParserParseMCoreFile", CBootParserParseMCoreFile (),
     tyarrow_ tystr_ tyunknown_)
  , ("bootParserGetId", CBootParserGetId (),
     tyarrow_ tyunknown_ tyint_)
  , ("bootParserGetTerm", CBootParserGetTerm (),
     tyarrow_ tyunknown_ tyunknown_)
  , ("bootParserGetType", CBootParserGetType (),
     tyarrow_ tyunknown_ tyunknown_)
  , ("bootParserGetString", CBootParserGetString (),
     tyarrow_ tyunknown_ tystr_)
  , ("bootParserGetInt", CBootParserGetInt (),
     tyarrow_ tyunknown_ tyint_)
  , ("bootParserGetFloat", CBootParserGetFloat (),
     tyarrow_ tyunknown_ tyfloat_)
  , ("bootParserGetListLength", CBootParserGetListLength (),
     tyarrow_ tyunknown_ tyint_)
  , ("bootParserGetConst", CBootParserGetConst (),
     tyarrow_ tyunknown_ tyunknown_)
  , ("bootParserGetPat", CBootParserGetPat (),
     tyarrow_ tyunknown_ tyunknown_)
  , ("bootParserGetInfo", CBootParserGetInfo (),
     tyarrow_ tyunknown_ tyunknown_)
  ]

let builtinEnv = map (lam x. match x with (s,c,ty) then (nameSym s, const_ c, ty) else never) builtin
