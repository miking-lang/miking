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

let tyvarseq_ = lam id. tyseq_ (tyvar_ id)

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
  | CStringIsFloat _ -> tyarrow_ tystr_ tybool_
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
  | CSet _ ->
    tyall_ "a" (tyarrows_ [ tyvarseq_ "a", tyint_, tyvar_ "a", tyvarseq_ "a"])
  | CGet _ -> tyall_ "a" (tyarrows_ [tyvarseq_ "a", tyint_, tyvar_ "a"])
  | CCons _ -> tyall_ "a" (tyarrows_ [tyvar_ "a", tyvarseq_ "a", tyvarseq_ "a"])
  | CSnoc _ -> tyall_ "a" (tyarrows_ [tyvarseq_ "a", tyvar_ "a", tyvarseq_ "a"])
  | CConcat _ -> tyall_ "a" (tyarrows_ [tyvarseq_ "a", tyvarseq_ "a", tyvarseq_ "a"])
  | CLength _ -> tyall_ "a" (tyarrow_ (tyvarseq_ "a") tyint_)
  | CReverse _ -> tyall_ "a" (tyarrow_ (tyvarseq_ "a") (tyvarseq_ "a"))
  | CHead _ -> tyall_ "a" (tyarrow_ (tyvarseq_ "a") (tyvar_ "a"))
  | CTail _ -> tyall_ "a" (tyarrow_ (tyvarseq_ "a") (tyvarseq_ "a"))
  | CNull _ -> tyall_ "a" (tyarrow_ (tyvarseq_ "a") tybool_)
  | CMap _ ->
    tyalls_ ["a", "b"] (tyarrows_ [ tyarrow_ (tyvar_ "a") (tyvar_ "b"),
                                    tyvarseq_ "a", tyvarseq_ "b" ])
  | CMapi _ ->
    tyalls_ ["a", "b"] (tyarrows_ [ tyarrows_ [tyint_, tyvar_ "a", tyvar_ "b"],
                                               tyvarseq_ "a", tyvarseq_ "b" ])
  | CIter _ ->
    tyall_ "a" (tyarrows_ [tyarrow_ (tyvar_ "a") tyunit_, tyvarseq_ "a", tyunit_])
  | CIteri _ ->
    tyall_ "a" (tyarrows_ [ tyarrows_ [tyint_, tyvar_ "a", tyunit_],
                            tyvarseq_ "a", tyunit_ ])
  | CFoldl _ ->
    tyalls_ ["a", "b"]
            (tyarrows_ [ tyarrows_ [tyvar_ "a", tyvar_ "b", tyvar_ "a"],
                         tyvar_ "a", tyvarseq_ "b", tyvar_ "a" ])
  | CFoldr _ ->
    tyalls_ ["a", "b"]
            (tyarrows_ [ tyarrows_ [tyvar_ "b", tyvar_ "a", tyvar_ "a"],
                         tyvar_ "a", tyvarseq_ "b", tyvar_ "a" ])
  | CCreate _ ->
    tyall_ "a" (tyarrows_ [tyint_, tyarrow_ tyint_ (tyvar_ "a"), tyvarseq_ "a"])
  | CCreateList _ ->
    tyall_ "a" (tyarrows_ [tyint_, tyarrow_ tyint_ (tyvar_ "a"), tyvarseq_ "a"])
  | CCreateRope _ ->
    tyall_ "a" (tyarrows_ [tyint_, tyarrow_ tyint_ (tyvar_ "a"), tyvarseq_ "a"])
  | CIsList _ -> tyall_ "a" (tyarrow_ (tyvarseq_ "a") tybool_)
  | CIsRope _ -> tyall_ "a" (tyarrow_ (tyvarseq_ "a") tybool_)
  | CSplitAt _ ->
    tyall_ "a" (tyarrows_ [ tyvarseq_ "a", tyint_,
                            tytuple_ [tyvarseq_ "a", tyvarseq_ "a"]])
  | CSubsequence _ ->
    tyall_ "a" (tyarrows_ [ tyvarseq_ "a", tyint_, tyint_, tyvarseq_ "a"])
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
  | CPrintError _ -> tyarrow_ tystr_ tyunit_
  | CDPrint _ -> tyarrow_ tystr_ tyunit_
  | CFlushStdout _ -> tyarrow_ tyunit_ tyunit_
  | CFlushStderr _ -> tyarrow_ tyunit_ tyunit_
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
  | CRef _ -> tyall_ "a" (tyarrow_ (tyvar_ "a") tyref_)
  | CModRef _ -> tyall_ "a" (tyarrows_ [tyref_, tyvar_ "a", tyunit_])
  | CDeRef _ -> tyall_ "a" (tyarrow_ tyref_ (tyvar_ "a"))
end

lang ConTagTypeAst = ConTagAst
  sem tyConst =
  | CConstructorTag _ -> tyall_ "a" (tyarrow_ (tyvar_ "a") tyint_)
end

lang MapTypeAst = MapAst
  sem tyConst =
  | CMapEmpty _ ->
    tyall_ "a" (tyarrow_ (tyarrows_ [tyvar_ "a", tyvar_ "a", tyint_]) tymap_)
  | CMapInsert _ ->
    tyalls_ ["a", "b"] (tyarrows_ [tyvar_ "a", tyvar_ "b", tymap_, tymap_])
  | CMapRemove _ -> tyall_ "a" (tyarrows_ [tyvar_ "a", tymap_, tymap_])
  | CMapFindExn _ ->
    tyalls_ ["a", "b"] (tyarrows_ [tyvar_ "a", tymap_, tyvar_ "b"])
  | CMapFindOrElse _ ->
    tyalls_ ["a", "b"]
            (tyarrows_ [tyarrow_ tyunit_ (tyvar_ "b"),
                        tyvar_ "a", tymap_, tyvar_ "b"])
  | CMapFindApplyOrElse _ ->
    tyalls_ ["a", "b", "c"]
            (tyarrows_ [tyarrow_ (tyvar_ "b") (tyvar_ "c"),
                        tyarrow_ tyunit_ (tyvar_ "c"), tyvar_ "a",
                        tymap_, tyvar_ "c"])
  | CMapBindings _ ->
    tyalls_ ["a", "b"]
            (tyarrow_ tymap_ (tyseq_ (tytuple_ [tyvar_ "a", tyvar_ "b"])))
  | CMapChooseExn _ ->
    tyalls_ ["a", "b"]
            (tyarrows_ [tymap_, (tytuple_ [tyvar_ "a", tyvar_ "b"])])
  | CMapChooseOrElse _ ->
    tyalls_ ["a", "b"]
            (tyarrows_ [tyarrow_ tyunit_ (tytuple_ [tyvar_ "a", tyvar_ "b"]),
                        tymap_, (tytuple_ [tyvar_ "a", tyvar_ "b"])])
  | CMapSize _ -> tyarrow_ tymap_ tyint_
  | CMapMem _ -> tyall_ "a" (tyarrows_ [tyvar_ "a", tymap_, tybool_])
  | CMapAny _ ->
    tyalls_ ["a", "b"]
            (tyarrows_ [tyarrows_ [tyvar_ "a", tyvar_ "b", tybool_], tymap_, tybool_])
  | CMapMap _ ->
    tyalls_ ["b", "c"]
            (tyarrows_ [tyarrow_ (tyvar_ "b") (tyvar_ "c"), tymap_, tymap_])
  | CMapMapWithKey _ ->
    tyalls_ ["a", "b", "c"]
            (tyarrows_ [tyarrows_ [tyvar_ "a", tyvar_ "b", tyvar_ "c"],
                        tymap_, tymap_])
  | CMapFoldWithKey _ ->
    tyalls_ ["a", "b", "c"]
            (tyarrows_ [tyarrows_ [tyvar_ "a", tyvar_ "b", tyvar_ "c", tyvar_ "c"],
                        tyvar_ "c", tymap_, tyvar_ "c"])
  | CMapEq _ ->
    tyall_ "b" (tyarrows_ [tyarrows_ [tyvar_ "b", tyvar_ "b", tybool_],
                           tymap_, tymap_, tybool_])
  | CMapCmp _ ->
    tyall_ "b" (tyarrows_ [tyarrows_ [tyvar_ "b", tyvar_ "b", tyint_],
                           tymap_, tymap_, tyint_])
  | CMapGetCmpFun _ -> tyall_ "a" (tyarrows_ [tymap_, tyvar_ "a", tyvar_ "a", tyint_])
end

lang TensorOpTypeAst = TensorOpAst
  sem tyConst =
  | CTensorCreateInt _ -> tytensorcreateint_
  | CTensorCreateFloat _ -> tytensorcreatefloat_
  | CTensorCreate _ -> tyall_ "a" (tytensorcreate_ (tyvar_ "a"))
  | CTensorGetExn _ -> tyall_ "a" (tytensorgetexn_ (tyvar_ "a"))
  | CTensorSetExn _ -> tyall_ "a" (tytensorsetexn_ (tyvar_ "a"))
  | CTensorLinearGetExn _ -> tyall_ "a" (tytensorlineargetexn_ (tyvar_ "a"))
  | CTensorLinearSetExn _ -> tyall_ "a" (tytensorlinearsetexn_ (tyvar_ "a"))
  | CTensorRank _ -> tyall_ "a" (tytensorrank_ (tyvar_ "a"))
  | CTensorShape _ -> tyall_ "a" (tytensorshape_ (tyvar_ "a"))
  | CTensorReshapeExn _ -> tyall_ "a" (tytensorreshapeexn_ (tyvar_ "a"))
  | CTensorCopy _ -> tyall_ "a" (tytensorcopy_ (tyvar_ "a"))
  | CTensorTransposeExn _ -> tyall_ "a" (tytensortransposeexn_ (tyvar_ "a"))
  | CTensorSliceExn _ -> tyall_ "a" (tytensorsliceexn_ (tyvar_ "a"))
  | CTensorSubExn _ -> tyall_ "a" (tytensorsubexn_ (tyvar_ "a"))
  | CTensorIterSlice _ -> tyall_ "a" (tytensoriteri_ (tyvar_ "a"))
  | CTensorEq _ -> tyall_ "a" (tytensoreq_ (tyvar_ "a") (tyvar_ "a"))
  | CTensorToString _ -> tyall_ "a" (tytensortostring_ (tyvar_ "a"))
end

lang BootParserTypeAst = BootParserAst
  sem tyConst =
  | CBootParserParseMExprString _ -> tyarrow_ tystr_ tybootparsetree_
  | CBootParserParseMCoreFile _ -> tyarrows_ [
      tytuple_ [tybool_, tybool_ ,tyseq_ tystr_],
      tyseq_ tystr_,
      tystr_,
      tybootparsetree_
    ]
  | CBootParserGetId _ -> tyarrow_ tybootparsetree_ tyint_
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
