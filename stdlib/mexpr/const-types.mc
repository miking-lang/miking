-- Defines the types of MExpr constants. A semantic function `tyConst` is
-- provided.

include "ast.mc"
include "ast-builder.mc"

-- The types defined below are only used for documentation purposes, as these
-- cannot be properly represented using the existing types.
let tysym_ = tyunknown_
let tyref_ = tyunknown_
let tymap_ = tyunknown_
let tybootparsetree_ = tyunknown_
let tygeneric_ = lam id. tyunknown_
let tygenericseq_ = lam id. tyseq_ (tygeneric_ id)

lang LiteralTypeAst = IntAst + FloatAst + BoolAst + CharAst
  sem tyConst =
  | CInt _ -> tyint_
  | CFloat _ -> tyfloat_
  | CBool _ -> tybool_
  | CChar _ -> tychar_
end

lang ArithIntTypeAst = ArithIntAst
  sem tyConst =
  | CAddi _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CSubi _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CMuli _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CDivi _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CNegi _ -> tyarrow_ tyint_ tyint_
  | CModi _ -> tyarrows_ [tyint_, tyint_, tyint_]
end

lang ShiftIntTypeAst = ShiftIntAst
  sem tyConst =
  | CSlli _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CSrli _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CSrai _ -> tyarrows_ [tyint_, tyint_, tyint_]
end

lang ArithFloatTypeAst = ArithFloatAst
  sem tyConst =
  | CAddf _ -> tyarrows_ [tyfloat_, tyfloat_, tyfloat_]
  | CSubf _ -> tyarrows_ [tyfloat_, tyfloat_, tyfloat_]
  | CMulf _ -> tyarrows_ [tyfloat_, tyfloat_, tyfloat_]
  | CDivf _ -> tyarrows_ [tyfloat_, tyfloat_, tyfloat_]
  | CNegf _ -> tyarrow_ tyfloat_ tyfloat_
end

lang FloatIntConversionTypeAst = FloatIntConversionAst
  sem tyConst =
  | CFloorfi _ -> tyarrow_ tyfloat_ tyint_
  | CCeilfi _ -> tyarrow_ tyfloat_ tyint_
  | CRoundfi _ -> tyarrow_ tyfloat_ tyint_
  | CInt2float _ -> tyarrow_ tyint_ tyfloat_
end

lang CmpIntTypeAst = CmpIntAst
  sem tyConst =
  | CEqi _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CNeqi _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CLti _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CGti _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CLeqi _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CGeqi _ -> tyarrows_ [tyint_, tyint_, tybool_]
end

lang CmpFloatTypeAst = CmpFloatAst
  sem tyConst =
  | CEqf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CLtf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CLeqf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CGtf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CGeqf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CNeqf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
end

lang CmpCharTypeAst = CmpCharAst
  sem tyConst =
  | CEqc _ -> tyarrows_ [tychar_, tychar_, tybool_]
end

lang IntCharConversionTypeAst = IntCharConversionAst
  sem tyConst =
  | CInt2Char _ -> tyarrow_ tyint_ tychar_
  | CChar2Int _ -> tyarrow_ tychar_ tyint_
end

lang FloatStringConversionTypeAst = FloatStringConversionAst
  sem tyConst =
  | CString2float _ -> tyarrow_ tystr_ tyfloat_
  | CFloat2string _ -> tyarrow_ tyfloat_ tystr_
end

lang SymbTypeAst = SymbAst
  sem tyConst =
  | CSymb _ -> tysym_
  | CGensym _ -> tyarrow_ tyunit_ tysym_
  | CSym2hash _ -> tyarrow_ tysym_ tyint_
end

lang CmpSymbTypeAst = CmpSymbAst
  sem tyConst =
  | CEqsym _ -> tyarrows_ [tysym_, tysym_, tybool_]
end

lang SeqOpTypeAst = SeqOpAst
  sem tyConst =
  | CSet _ -> tyarrows_ [tygenericseq_ "a", tyint_,
                         tygeneric_ "a", tygenericseq_ "a"]
  | CGet _ -> tyarrows_ [tygenericseq_ "a", tyint_, tygeneric_ "a"]
  | CCons _ -> tyarrows_ [tygeneric_ "a", tygenericseq_ "a", tygenericseq_ "a"]
  | CSnoc _ -> tyarrows_ [tygenericseq_ "a", tygeneric_ "a", tygenericseq_ "a"]
  | CConcat _ -> tyarrows_ [tygenericseq_ "a", tygenericseq_ "a",
                            tygenericseq_ "a"]
  | CLength _ -> tyarrow_ (tygenericseq_ "a") tyint_
  | CReverse _ -> tyarrow_ (tygenericseq_ "a") (tygenericseq_ "a")
  | CHead _ -> tyarrow_ (tygenericseq_ "a") (tygeneric_ "a")
  | CTail _ -> tyarrow_ (tygenericseq_ "a") (tygenericseq_ "a")
  | CNull _ -> tyarrow_ (tygenericseq_ "a") tybool_
  | CMap _ ->
    tyarrows_ [ tyarrow_ (tygeneric_ "a") (tygeneric_ "a"),
                tygenericseq_ "a", tygenericseq_ "a" ]
  | CMapi _ ->
    tyarrows_ [ tyarrows_ [tyint_, tygeneric_ "a", tygeneric_ "a"],
                tygenericseq_ "a", tygenericseq_ "a" ]
  | CIter _ ->
    tyarrows_ [tyarrow_ (tygeneric_ "a") tyunit_, tygenericseq_ "a", tyunit_]
  | CIteri _ ->
    tyarrows_ [ tyarrows_ [tyint_, tygeneric_ "a", tyunit_],
                tygenericseq_ "a", tyunit_ ]
  | CFoldl _ ->
    tyarrows_ [ tyarrows_ [tygeneric_ "a", tygeneric_ "b", tygeneric_ "a"],
                tygeneric_ "a", tygenericseq_ "b", tygeneric_ "a" ]
  | CFoldr _ ->
    tyarrows_ [ tyarrows_ [tygeneric_ "b", tygeneric_ "a", tygeneric_ "a"],
                tygeneric_ "a", tygenericseq_ "b", tygeneric_ "a" ]
  | CCreate _ -> tyarrows_ [tyint_, tyarrow_ tyint_ (tygeneric_ "a"),
                            tygenericseq_ "a"]
  | CCreateList _ ->
    tyarrows_ [tyint_, tyarrow_ tyint_ (tygeneric_ "a"), tygenericseq_ "a"]
  | CCreateRope _ ->
    tyarrows_ [tyint_, tyarrow_ tyint_ (tygeneric_ "a"), tygenericseq_ "a"]
  | CSplitAt _ -> tyarrows_ [tygenericseq_ "a", tyint_,
                             tytuple_ [tygenericseq_ "a", tygenericseq_ "a"]]
  | CSubsequence _ -> tyarrows_ [tygenericseq_ "a", tyint_, tyint_,
                                 tygenericseq_ "a"]
end

lang FileOpTypeAst = FileOpAst
  sem tyConst =
  | CFileRead _ -> tyarrow_ tystr_ tystr_
  | CFileWrite _ -> tyarrows_ [tystr_, tystr_, tyunit_]
  | CFileExists _ -> tyarrow_ tystr_ tybool_
  | CFileDelete _ -> tyarrow_ tystr_ tyunit_
end

lang IOTypeAst = IOAst
  sem tyConst =
  | CPrint _ -> tyarrow_ tystr_ tyunit_
  | CDPrint _ -> tyarrow_ tystr_ tyunit_
  | CFlushStdout _ -> tyarrow_ tyunit_ tyunit_
  | CReadLine _ -> tyarrow_ tyunit_ tystr_
  | CReadBytesAsString _ -> tyarrow_ tyint_ (tytuple_ [tystr_, tystr_])
end

lang RandomNumberGeneratorTypeAst = RandomNumberGeneratorAst
  sem tyConst =
  | CRandIntU _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CRandSetSeed _ -> tyarrow_ tyint_ tyunit_
end

lang SysTypeAst = SysAst
  sem tyConst =
  | CExit _ -> tyarrow_ tyint_ tyunknown_
  | CError _ -> tyarrow_ tystr_ tyunknown_
  | CArgv _ -> tyseq_ tystr_
  | CCommand _ -> tyarrow_ tystr_ tyint_
end

lang TimeTypeAst = TimeAst
  sem tyConst =
  | CWallTimeMs _ -> tyarrow_ tyunit_ tyfloat_
  | CSleepMs _ -> tyarrow_ tyint_ tyunit_
end

lang RefOpTypeAst = RefOpAst
  sem tyConst =
  | CRef _ -> tyarrow_ (tygeneric_ "a") tyref_
  | CModRef _ -> tyarrows_ [tyref_, tygeneric_ "a", tyunit_]
  | CDeRef _ -> tyarrow_ tyref_ (tygeneric_ "a")
end

lang ConTagTypeAst = ConTagAst
  sem tyConst =
  | CConstructorTag _ -> tyarrow_ (tygeneric_ "a") tyint_
end

lang MapTypeAst = MapAst
  sem tyConst =
  | CMapEmpty _ -> tyarrow_ (tyarrows_ [tygeneric_ "a", tygeneric_ "a", tyint_])
                            tymap_
  | CMapInsert _ -> tyarrows_ [tygeneric_ "a", tygeneric_ "b", tymap_, tymap_]
  | CMapRemove _ -> tyarrows_ [tygeneric_ "a", tymap_, tymap_]
  | CMapFindWithExn _ -> tyarrows_ [tygeneric_ "a", tymap_, tygeneric_ "b"]
  | CMapFindOrElse _ -> tyarrows_ [tyarrow_ tyunit_ (tygeneric_ "b"),
                                   tygeneric_ "a", tymap_, tygeneric_ "b"]
  | CMapFindApplyOrElse _ ->
    tyarrows_ [tyarrow_ (tygeneric_ "b") (tygeneric_ "c"),
               tyarrow_ tyunit_ (tygeneric_ "c"), tygeneric_ "a",
               tymap_, tygeneric_ "c"]
  | CMapBindings _ -> tyarrow_ tymap_
                               (tyseq_ (tytuple_ [tygeneric_ "a", tygeneric_ "b"]))
  | CMapSize _ -> tyarrow_ tymap_ tyint_
  | CMapMem _ -> tyarrows_ [tygeneric_ "a", tymap_, tybool_]
  | CMapAny _ -> tyarrows_ [tyarrows_ [tygeneric_ "a", tygeneric_ "b", tybool_],
                            tymap_, tybool_]
  | CMapMap _ -> tyarrows_ [tyarrow_ (tygeneric_ "b") (tygeneric_ "c"),
                            tymap_, tymap_]
  | CMapMapWithKey _ ->
    tyarrows_ [tyarrows_ [tygeneric_ "a", tygeneric_ "b", tygeneric_ "c"],
               tymap_, tymap_]
  | CMapFoldWithKey _ ->
    tyarrows_ [tyarrows_ [tygeneric_ "a", tygeneric_ "b",
                          tygeneric_ "c", tygeneric_ "c"],
               tygeneric_ "c", tymap_, tygeneric_ "c"]
  | CMapEq _ -> tyarrows_ [tyarrows_ [tygeneric_ "b", tygeneric_ "b", tybool_],
                           tymap_, tymap_, tybool_]
  | CMapCmp _ -> tyarrows_ [tyarrows_ [tygeneric_ "b", tygeneric_ "b", tyint_],
                            tymap_, tymap_, tyint_]
  | CMapGetCmpFun _ -> tyarrows_ [tymap_, tygeneric_ "a", tygeneric_ "a", tyint_]
end

lang TensorOpTypeAst = TensorOpAst
  sem tyConst =
  | CTensorCreateInt _ -> tytensorcreateint_
  | CTensorCreateFloat _ -> tytensorcreatefloat_
  | CTensorCreate _ -> tytensorcreate_ (tygeneric_ "a")
  | CTensorGetExn _ -> tytensorgetexn_ (tygeneric_ "a")
  | CTensorSetExn _ -> tytensorsetexn_ (tygeneric_ "a")
  | CTensorRank _ -> tytensorrank_ (tygeneric_ "a")
  | CTensorShape _ -> tytensorshape_ (tygeneric_ "a")
  | CTensorReshapeExn _ -> tytensorreshapeexn_ (tygeneric_ "a")
  | CTensorCopy _ -> tytensorcopy_ (tygeneric_ "a")
  | CTensorTransposeExn _ -> tytensortransposeexn_ (tygeneric_ "a")
  | CTensorSliceExn _ -> tytensorsliceexn_ (tygeneric_ "a")
  | CTensorSubExn _ -> tytensorsubexn_ (tygeneric_ "a")
  | CTensorIterSlice _ -> tytensoriteri_ (tygeneric_ "a")
  | CTensorEq _ -> tytensoreq_ (tygeneric_ "a") (tygeneric_ "a")
  | CTensorToString _ -> tytensortostring_ (tygeneric_ "a")
end

lang BootParserTypeAst = BootParserAst
  sem tyConst =
  | CBootParserParseMExprString _ -> tyarrow_ tystr_ tybootparsetree_
  | CBootParserParseMCoreFile _ -> tyarrow_ tystr_ tybootparsetree_
  | CBootParserGetId _ -> tyarrows_ [tybootparsetree_, tyint_, tyint_]
  | CBootParserGetTerm _ -> tyarrows_ [tybootparsetree_, tyint_, tybootparsetree_]
  | CBootParserGetType _ -> tyarrows_ [tybootparsetree_, tyint_, tybootparsetree_]
  | CBootParserGetString _ -> tyarrows_ [tybootparsetree_, tyint_, tystr_]
  | CBootParserGetInt _ -> tyarrows_ [tybootparsetree_, tyint_, tyint_]
  | CBootParserGetFloat _ -> tyarrows_ [tybootparsetree_, tyint_, tyfloat_]
  | CBootParserGetListLength _ -> tyarrows_ [tybootparsetree_, tyint_, tyint_]
  | CBootParserGetConst _ -> tyarrows_ [tybootparsetree_, tyint_, tybootparsetree_]
  | CBootParserGetPat _ -> tyarrows_ [tybootparsetree_, tyint_, tybootparsetree_]
  | CBootParserGetInfo _ -> tyarrows_ [tybootparsetree_, tyint_, tybootparsetree_]
end

lang MExprConstType =
  LiteralTypeAst + ArithIntTypeAst + ShiftIntTypeAst + ArithFloatTypeAst +
  CmpIntTypeAst + IntCharConversionTypeAst + CmpFloatTypeAst + CmpCharTypeAst +
  SymbTypeAst + CmpSymbTypeAst + SeqOpTypeAst + FileOpTypeAst + IOTypeAst +
  RandomNumberGeneratorTypeAst + SysTypeAst + FloatIntConversionTypeAst +
  FloatStringConversionTypeAst + TimeTypeAst + RefOpTypeAst + ConTagTypeAst +
  MapTypeAst + TensorOpTypeAst + BootParserTypeAst
end
