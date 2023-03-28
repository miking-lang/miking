-- In this file, a language fragment is defined for including the contents of
-- peval-runtime.mc in the given AST. The inclusion uses the same functionality as
-- mexpr/utest-generate.mc. Moreover, the strings of names that are needed in
-- the specialize transformation are defined. The actual names are then looked
-- up and used in e.g. lift.mc.
--
-- The idea is that this is a temporary solution until the full bootstrapping of
-- the compiler is in place.

include "stdlib.mc"
include "mexpr/load-runtime.mc"
include "mexpr/duplicate-code-elimination.mc"


let includesLoc = "/peval/peval-runtime.mc"

-- Mapping from pretty printed built-in const to its AST equivalent
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
    ("bootParserParseMLangString", "BootParserAst_CBootParserParseMLangString"),
    ("bootParserParseMLangFile", "BootParserAst_CBootParserParseMLangFile"),
    ("bootParserParseMCoreFile", "BootParserAst_CBootParserParseMCoreFile"),
    ("bootParserGetId", "BootParserAst_CBootParserGetId"),
    ("bootParserGetTerm", "BootParserAst_CBootParserGetTerm"),
    ("bootParserGetTop", "BootParserAst_CBootParserGetTop"),
    ("bootParserGetDecl", "BootParserAst_CBootParserGetDecl"),
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
let includeConsNames =
  ["AppAst_TmApp", "LamAst_TmLam", "VarAst_TmVar", "RecordAst_TmRecord",
   "SeqAst_TmSeq", "ClosAst_TmClos", "ConstAst_TmConst", "ClosAst_Lazy",
   "MatchAst_TmMatch", "LetAst_TmLet", "RecLetsAst_TmRecLets",
   "DataAst_TmConDef", "DataAst_TmConApp", "TypeAst_TmType", "NeverAst_TmNever",

   -- Others
   "Cons", "Nil", "NoInfo", "Info",

   -- Patterns
   "IntPat_PatInt", "PName", "PWildcard", "NamedPat_PatNamed",
   "BoolPat_PatBool", "CharPat_PatChar", "SeqTotPat_PatSeqTot",
   "SeqEdgePat_PatSeqEdge", "RecordPat_PatRecord", "DataPat_PatCon",
   "AndPat_PatAnd", "OrPat_PatOr", "NotPat_PatNot"]

let includeTyConsNames =
  ["UnknownTypeAst_TyUnknown","BoolTypeAst_TyBool", "IntTypeAst_TyInt",
   "FloatTypeAst_TyFloat","CharTypeAst_TyChar", "FunTypeAst_TyArrow",
   "SeqTypeAst_TySeq", "TensorTypeAst_TyTensor", "RecordTypeAst_TyRecord",
   "VariantTypeAst_TyVariant", "ConTypeAst_TyCon", "VarTypeAst_TyVar",
   "PolyKindAst_Poly", "MonoKindAst_Mono", "RecordKindAst_Record", "DataKindAst_Data",
   "AllTypeAst_TyAll", "AppTypeAst_TyApp","AliasTypeAst_TyAlias"]

let includeOtherFuncs =
  ["mapFromSeq", "stringToSid", "mapMapWithKey", "toString", "_noSymbol"]

let includeSpecializeNames = ["pevalWithEnv"]

lang SpecializeInclude = MExprLoadRuntime + MExprEliminateDuplicateCode

  sem includeSpecializeDeps : Expr -> Expr
  sem includeSpecializeDeps =
  | ast ->
    let includes = loadRuntime includesLoc in
    let ast = mergeWithHeader ast includes in
    eliminateDuplicateCode ast
end
