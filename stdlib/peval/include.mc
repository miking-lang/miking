include "stdlib.mc"
include "mexpr/utest-generate.mc"
include "mexpr/duplicate-code-elimination.mc"


let includesLoc = "/peval/peval-runtime.mc"

-- Mapping from pretty printed built-in const to its AST equivalent
-- TODO(adamssonj, 2023-03-17): True assumption? Built-ins are assumed always in AST
let builtinsMapping = mapFromSeq cmpString [
    -- These 5 are not builtin functions, but used to get name of AST node of constants
    -- Differs in that these take an argument when constructed
    ("float", "FloatAst_CFloat"),
    ("int", "IntAst_CInt"),
    ("bool", "BoolAst_CBool"),
    ("char", "CharAst_CChar"),
    ("symb", "SymbAst_CSymb"),
    -----------------------------------------------------
    ("unsafeCoerce", "UnsafeCoerceAst_CUnsafeCoerce"),
    ("addi", "ArithIntAst_CAddi"),
    ("subi", "ArithIntAst_CSubi"),
    ("muli", "ArithIntAst_CMuli"),
    ("divi", "ArithIntAst_CDivi"),
    ("modi", "ArithIntAst_CModi"),
    ("negi", "ArithIntAst_CNegi"),
    ("lti", "CmpIntAst_CLti"),
    ("leqi", "CmpIntAst_CLeqi"),
    ("gti", "CmpIntAst_CGti"),
    ("geqi", "CmpIntAst_CGeqi"),
    ("eqi", "CmpIntAst_CEqi"),
    ("neqi", "CmpIntAst_CNeqi"),
    ("slli", "ShiftIntAst_CSlli"),
    ("srli", "ShiftIntAst_CSrli"),
    ("srai", "ShiftIntAst_CSrai"),
    ("addf", "ArithFloatAst_CAddf"),
    ("subf", "ArithFloatAst_CSubf"),
    ("mulf", "ArithFloatAst_CMulf"),
    ("divf", "ArithFloatAst_CDivf"),
    ("negf", "ArithFloatAst_CNegf"),
    ("ltf", "CmpFloatAst_CLtf"),
    ("leqf", "CmpFloatAst_CLeqf"),
    ("gtf", "CmpFloatAst_CGtf"),
    ("geqf", "CmpFloatAst_CGeqf"),
    ("eqf", "CmpFloatAst_CEqf"),
    ("neqf", "CmpFloatAst_CNeqf"),
    ("floorfi", "FloatIntConversionAst_CFloorfi"),
    ("ceilfi", "FloatIntConversionAst_CCeilfi"),
    ("roundfi", "FloatIntConversionAst_CRoundfi"),
    ("int2float", "FloatIntConversionAst_CInt2float"),
    ("stringIsFloat", "FloatStringConversionAst_CStringIsFloat"),
    ("string2float", "FloatStringConversionAst_CString2float"),
    ("float2string", "FloatStringConversionAst_CFloat2string"),
    ("eqc", "CmpCharAst_CEqc"),
    ("char2int", "IntCharConversionAst_CChar2Int"),
    ("int2char", "IntCharConversionAst_CInt2Char"),
    ("create", "SeqOpAst_CCreate"),
    ("createList", "SeqOpAst_CCreateList"),
    ("createRope", "SeqOpAst_CCreateRope"),
    ("isList", "SeqOpAst_CIsList"),
    ("isRope", "SeqOpAst_CIsRope"),
    ("length", "SeqOpAst_CLength"),
    ("concat", "SeqOpAst_CConcat"),
    ("get", "SeqOpAst_CGet"),
    ("set", "SeqOpAst_CSet"),
    ("cons", "SeqOpAst_CCons"),
    ("snoc", "SeqOpAst_CSnoc"),
    ("splitAt", "SeqOpAst_CSplitAt"),
    ("reverse", "SeqOpAst_CReverse"),
    ("head", "SeqOpAst_CHead"),
    ("tail", "SeqOpAst_CTail"),
    ("null", "SeqOpAst_CNull"),
    ("map", "SeqOpAst_CMap"),
    ("mapi", "SeqOpAst_CMapi"),
    ("iter", "SeqOpAst_CIter"),
    ("iteri", "SeqOpAst_CIteri"),
    ("foldl", "SeqOpAst_CFoldl"),
    ("foldr", "SeqOpAst_CFoldr"),
    ("subsequence", "SeqOpAst_CSubsequence"),
    ("randIntU", "RandomNumberGeneratorAst_CRandIntU"),
    ("randSetSeed", "RandomNumberGeneratorAst_CRandSetSeed"),
    ("wallTimeMs", "TimeAst_CWallTimeMs"),
    ("sleepMs", "TimeAst_CSleepMs"),
    ("print", "IOAst_CPrint"),
    ("printError", "IOAst_CPrintError"),
    ("dprint", "IOAst_CDPrint"),
    ("flushStdout", "IOAst_CFlushStdout"),
    ("flushStderr", "IOAst_CFlushStderr"),
    ("readLine", "IOAst_CReadLine"),
    ("readBytesAsString", "IOAst_CReadBytesAsString"),
    ("argv", "SysAst_CArgv"),
    ("readFile", "FileOpAst_CFileRead"),
    ("writeFile", "FileOpAst_CFileWrite"),
    ("fileExists", "FileOpAst_CFileExists"),
    ("deleteFile", "FileOpAst_CFileDelete"),
    ("command", "SysAst_CCommand"),
    ("error", "SysAst_CError"),
    ("exit", "SysAst_CExit"),
    ("constructorTag", "ConTagAst_CConstructorTag"),
    ("eqsym", "CmpSymbAst_CEqsym"),
    ("gensym", "SymbAst_CGensym"),
    ("sym2hash", "SymbAst_CSym2hash"),
    ("ref", "RefOpAst_CRef"),
    ("deref", "RefOpAst_CDeRef"),
    ("modref", "RefOpAst_CModRef"),
    ("tensorCreateUninitInt", "TensorOpAst_CTensorCreateUninitInt"),
    ("tensorCreateUninitFloat", "TensorOpAst_CTensorCreateUninitFloat"),
    ("tensorCreateCArrayInt", "TensorOpAst_CTensorCreateInt"),
    ("tensorCreateCArrayFloat", "TensorOpAst_CTensorCreateFloat"),
    ("tensorCreateDense", "TensorOpAst_CTensorCreate"),
    ("tensorGetExn", "TensorOpAst_CTensorGetExn"),
    ("tensorSetExn", "TensorOpAst_CTensorSetExn"),
    ("tensorLinearGetExn", "TensorOpAst_CTensorLinearGetExn"),
    ("tensorLinearSetExn", "TensorOpAst_CTensorLinearSetExn"),
    ("tensorRank", "TensorOpAst_CTensorRank"),
    ("tensorShape", "TensorOpAst_CTensorShape"),
    ("tensorReshapeExn", "TensorOpAst_CTensorReshapeExn"),
    ("tensorCopy", "TensorOpAst_CTensorCopy"),
    ("tensorTransposeExn", "TensorOpAst_CTensorTransposeExn"),
    ("tensorSliceExn", "TensorOpAst_CTensorSliceExn"),
    ("tensorSubExn", "TensorOpAst_CTensorSubExn"),
    ("tensorIterSlice", "TensorOpAst_CTensorIterSlice"),
    ("tensorEq", "TensorOpAst_CTensorEq"),
    ("tensor2string", "TensorOpAst_CTensorToString"),
    ("bootParserParseMExprString", "BootParserAst_CBootParserParseMExprString"),
    ("bootParserParseMCoreFile", "BootParserAst_CBootParserParseMCoreFile"),
    ("bootParserGetId", "BootParserAst_CBootParserGetId"),
    ("bootParserGetTerm", "BootParserAst_CBootParserGetTerm"),
    ("bootParserGetType", "BootParserAst_CBootParserGetType"),
    ("bootParserGetString", "BootParserAst_CBootParserGetString"),
    ("bootParserGetInt", "BootParserAst_CBootParserGetInt"),
    ("bootParserGetFloat", "BootParserAst_CBootParserGetFloat"),
    ("bootParserGetListLength", "BootParserAst_CBootParserGetListLength"),
    ("bootParserGetConst", "BootParserAst_CBootParserGetConst"),
    ("bootParserGetPat", "BootParserAst_CBootParserGetPat"),
    ("bootParserGetInfo", "BootParserAst_CBootParserGetInfo")
]

let includeBuiltins = mapValues builtinsMapping

-- These use the constructors, as they are named, in the AST directly
-- Potentially could use e.g. "tmApp" here, but then tmApp just wraps "AppAst_TmApp"
-- At least the inclusion of 'tmApp' from cons-runtime ensures that the actual constructor
-- is in fact in the AST, but it may be subject to change (even if unlikely)
let includeConsNames = ["AppAst_TmApp", "LamAst_TmLam", "VarAst_TmVar", "RecordAst_TmRecord",
                        "SeqAst_TmSeq", "ClosAst_TmClos", "ConstAst_TmConst", "ClosAst_Lazy",
                        "MatchAst_TmMatch", "Cons", "Nil", "NoInfo", "Info", "_noSymbol",
                        "LetAst_TmLet", "RecLetsAst_TmRecLets",

                        --- Patterns
                        "IntPat_PatInt", "PName", "PWildcard", "NamedPat_PatNamed",
                        "BoolPat_PatBool"
                        ]


let includeTyConsNames = ["UnknownTypeAst_TyUnknown","BoolTypeAst_TyBool", "IntTypeAst_TyInt",
"FloatTypeAst_TyFloat","CharTypeAst_TyChar", "FunTypeAst_TyArrow", "SeqTypeAst_TySeq",
"TensorTypeAst_TyTensor", "RecordTypeAst_TyRecord", "VariantTypeAst_TyVariant",
"ConTypeAst_TyCon", "VarTypeAst_TyVar","VarSortAst_PolyVar","VarSortAst_MonoVar",
"VarSortAst_RecordVar","AllTypeAst_TyAll", "AppTypeAst_TyApp","AliasTypeAst_TyAlias"]

let includeOtherFuncs = ["mapFromSeq", "stringToSid", "mapMapWithKey", "toString"]

let includeSpecializeNames = ["pevalWithEnv"]

lang SpecializeInclude = MExprUtestGenerate

  sem includeSpecializeDeps : Expr -> Expr
  sem includeSpecializeDeps =
  | ast ->
    let ff = loadRuntime includesLoc in
    let ast = mergeWithUtestHeaderH (utestEnvEmpty ()) ast
              (ff) in
    resetStore ();
    eliminateDuplicateCode ast
end
