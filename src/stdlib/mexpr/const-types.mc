-- Defines the types of MExpr constants. A semantic function `tyConst` is
-- provided.

include "ast.mc"
include "ast-builder.mc"

let mktyall_ = lam s. lam f. tyall_ s (f (tyvar_ s))
let mkstyall_ = lam s. lam k. lam f. styall_ s k (f (tyvar_ s))

let mktybuiltin_ = lam s. lam d. lam disable. lam f.
  let ident = nameNoSym s in
  if disable then f (nsitycon_ ident tyunknown_ (NoInfo ()))
  else
    mkstyall_ d
      (kidata_ [(ident,
                 {lower = setEmpty nameCmp,
                  upper = Some (setEmpty nameCmp)})])
      (lam x. f (nsitycon_ ident x (NoInfo ())))


let mktysym_ = mktybuiltin_ "Symbol" "d"
let mktyref_ = mktybuiltin_ "Ref" "d"
let mktybootparsetree_ = mktybuiltin_ "BootParseTree" "d"

lang TyConst = ConstAst
  sem tyConst : Const -> Type
  sem tyConst =
  | c -> tyConstBase false c

  -- tyConstBase takes a parameter deciding whether to disable constructor sets
  -- for builtin types (Symbol, Ref, BootParseTree)
  sem tyConstBase : Bool -> Const -> Type

  sem mkConst : Info -> Const -> Expr
  sem mkConst info = | c -> TmConst
  { info = info
  , val = c
  , ty = tyConst c
  }
end

lang UnsafeCoerceTypeAst = TyConst + UnsafeCoerceAst
  sem tyConstBase d =
  | CUnsafeCoerce _ -> mktyall_ "a" (lam a. mktyall_ "b" (lam b. tyarrow_ a b))
end

lang LiteralTypeAst = TyConst + IntAst + FloatAst + BoolAst + CharAst
  sem tyConstBase d =
  | CInt _ -> tyint_
  | CFloat _ -> tyfloat_
  | CBool _ -> tybool_
  | CChar _ -> tychar_
end

lang ArithIntTypeAst = TyConst + ArithIntAst
  sem tyConstBase d =
  | CAddi _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CSubi _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CMuli _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CDivi _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CNegi _ -> tyarrow_ tyint_ tyint_
  | CModi _ -> tyarrows_ [tyint_, tyint_, tyint_]
end

lang ShiftIntTypeAst = TyConst + ShiftIntAst
  sem tyConstBase d =
  | CSlli _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CSrli _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CSrai _ -> tyarrows_ [tyint_, tyint_, tyint_]
end

lang ArithFloatTypeAst = TyConst + ArithFloatAst
  sem tyConstBase d =
  | CAddf _ -> tyarrows_ [tyfloat_, tyfloat_, tyfloat_]
  | CSubf _ -> tyarrows_ [tyfloat_, tyfloat_, tyfloat_]
  | CMulf _ -> tyarrows_ [tyfloat_, tyfloat_, tyfloat_]
  | CDivf _ -> tyarrows_ [tyfloat_, tyfloat_, tyfloat_]
  | CNegf _ -> tyarrow_ tyfloat_ tyfloat_
end

lang FloatIntConversionTypeAst = TyConst + FloatIntConversionAst
  sem tyConstBase d =
  | CFloorfi _ -> tyarrow_ tyfloat_ tyint_
  | CCeilfi _ -> tyarrow_ tyfloat_ tyint_
  | CRoundfi _ -> tyarrow_ tyfloat_ tyint_
  | CInt2float _ -> tyarrow_ tyint_ tyfloat_
end

lang CmpIntTypeAst = TyConst + CmpIntAst
  sem tyConstBase d =
  | CEqi _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CNeqi _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CLti _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CGti _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CLeqi _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CGeqi _ -> tyarrows_ [tyint_, tyint_, tybool_]
end

lang CmpFloatTypeAst = TyConst + CmpFloatAst
  sem tyConstBase d =
  | CEqf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CLtf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CLeqf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CGtf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CGeqf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CNeqf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
end

lang CmpCharTypeAst = TyConst + CmpCharAst
  sem tyConstBase d =
  | CEqc _ -> tyarrows_ [tychar_, tychar_, tybool_]
end

lang IntCharConversionTypeAst = TyConst + IntCharConversionAst
  sem tyConstBase d =
  | CInt2Char _ -> tyarrow_ tyint_ tychar_
  | CChar2Int _ -> tyarrow_ tychar_ tyint_
end

lang FloatStringConversionTypeAst = TyConst + FloatStringConversionAst
  sem tyConstBase d =
  | CStringIsFloat _ -> tyarrow_ tystr_ tybool_
  | CString2float _ -> tyarrow_ tystr_ tyfloat_
  | CFloat2string _ -> tyarrow_ tyfloat_ tystr_
end

lang SymbTypeAst = TyConst + SymbAst
  sem tyConstBase d =
  | CSymb _ -> mktysym_ d (lam s. s)
  | CGensym _ -> mktysym_ d (lam s. tyarrow_ tyunit_ s)
  | CSym2hash _ -> mktysym_ d (lam s. tyarrow_ s tyint_)
end

lang CmpSymbTypeAst = TyConst + CmpSymbAst
  sem tyConstBase d =
  | CEqsym _ -> mktysym_ d (lam s. tyarrows_ [s, s, tybool_])
end

lang SeqOpTypeAst = TyConst + SeqOpAst
  sem tyConstBase d =
  | CSet _ -> mktyall_ "a" (lam a. tyarrows_ [tyseq_ a, tyint_, a, tyseq_ a])
  | CGet _ -> mktyall_ "a" (lam a. tyarrows_ [tyseq_ a, tyint_, a])
  | CCons _ -> mktyall_ "a" (lam a. tyarrows_ [a, tyseq_ a, tyseq_ a])
  | CSnoc _ -> mktyall_ "a" (lam a. tyarrows_ [tyseq_ a, a, tyseq_ a])
  | CConcat _ -> mktyall_ "a" (lam a. tyarrows_ [tyseq_ a, tyseq_ a, tyseq_ a])
  | CLength _ -> mktyall_ "a" (lam a. tyarrow_ (tyseq_ a) tyint_)
  | CReverse _ -> mktyall_ "a" (lam a. tyarrow_ (tyseq_ a) (tyseq_ a))
  | CHead _ -> mktyall_ "a" (lam a. tyarrow_ (tyseq_ a) a)
  | CTail _ -> mktyall_ "a" (lam a. tyarrow_ (tyseq_ a) (tyseq_ a))
  | CNull _ -> mktyall_ "a" (lam a. tyarrow_ (tyseq_ a) tybool_)
  | CMap _ ->
    mktyall_ "a" (lam a. mktyall_ "b" (lam b.
      tyarrows_ [ tyarrow_ a b, tyseq_ a, tyseq_ b ]))
  | CMapi _ ->
    mktyall_ "a" (lam a. mktyall_ "b" (lam b.
      tyarrows_ [ tyarrows_ [tyint_, a, b], tyseq_ a, tyseq_ b ]))
  | CIter _ ->
    mktyall_ "a" (lam a. tyarrows_ [tyarrow_ a tyunit_, tyseq_ a, tyunit_])
  | CIteri _ ->
    mktyall_ "a" (lam a. tyarrows_ [ tyarrows_ [tyint_, a, tyunit_],
                                     tyseq_ a, tyunit_ ])
  | CFoldl _ ->
    mktyall_ "a" (lam a. mktyall_ "b" (lam b.
      tyarrows_ [tyarrows_ [a, b, a], a, tyseq_ b, a ]))
  | CFoldr _ ->
    mktyall_ "a" (lam a. mktyall_ "b" (lam b.
      tyarrows_ [tyarrows_ [b, a, a], a, tyseq_ b, a ]))
  | CCreate _ ->
    mktyall_ "a" (lam a. tyarrows_ [tyint_, tyarrow_ tyint_ a, tyseq_ a])
  | CCreateList _ ->
    mktyall_ "a" (lam a. tyarrows_ [tyint_, tyarrow_ tyint_ a, tyseq_ a])
  | CCreateRope _ ->
    mktyall_ "a" (lam a. tyarrows_ [tyint_, tyarrow_ tyint_ a, tyseq_ a])
  | CIsList _ -> mktyall_ "a" (lam a. tyarrow_ (tyseq_ a) tybool_)
  | CIsRope _ -> mktyall_ "a" (lam a. tyarrow_ (tyseq_ a) tybool_)
  | CSplitAt _ ->
    mktyall_ "a" (lam a. tyarrows_ [ tyseq_ a, tyint_,
                                     tytuple_ [tyseq_ a, tyseq_ a]])
  | CSubsequence _ ->
    mktyall_ "a" (lam a. tyarrows_ [ tyseq_ a, tyint_, tyint_, tyseq_ a])
end

lang FileOpTypeAst = TyConst + FileOpAst
  sem tyConstBase d =
  | CFileRead _ -> tyarrow_ tystr_ tystr_
  | CFileWrite _ -> tyarrows_ [tystr_, tystr_, tyunit_]
  | CFileExists _ -> tyarrow_ tystr_ tybool_
  | CFileDelete _ -> tyarrow_ tystr_ tyunit_
end

lang IOTypeAst = TyConst + IOAst
  sem tyConstBase d =
  | CPrint _ -> tyarrow_ tystr_ tyunit_
  | CPrintError _ -> tyarrow_ tystr_ tyunit_
  | CDPrint _ -> mktyall_ "a" (lam a. tyarrow_ a tyunit_)
  | CFlushStdout _ -> tyarrow_ tyunit_ tyunit_
  | CFlushStderr _ -> tyarrow_ tyunit_ tyunit_
  | CReadLine _ -> tyarrow_ tyunit_ tystr_
  | CReadBytesAsString _ -> tyarrow_ tyint_ (tytuple_ [tystr_, tystr_])
end

lang RandomNumberGeneratorTypeAst = TyConst + RandomNumberGeneratorAst
  sem tyConstBase d =
  | CRandIntU _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CRandSetSeed _ -> tyarrow_ tyint_ tyunit_
end

lang SysTypeAst = TyConst + SysAst
  sem tyConstBase d =
  | CExit _ -> mktyall_ "a" (lam a. tyarrow_ tyint_ a)
  | CError _ -> mktyall_ "a" (lam a. tyarrow_ tystr_ a)
  | CArgv _ -> tyseq_ tystr_
  | CCommand _ -> tyarrow_ tystr_ tyint_
end

lang TimeTypeAst = TyConst + TimeAst
  sem tyConstBase d =
  | CWallTimeMs _ -> tyarrow_ tyunit_ tyfloat_
  | CSleepMs _ -> tyarrow_ tyint_ tyunit_
end

lang RefOpTypeAst = TyConst + RefOpAst
  sem tyConstBase d =
  | CRef _ -> mktyall_ "a" (lam a. mktyref_ d (lam r. tyarrow_ a (tyapp_ r a)))
  | CModRef _ -> mktyall_ "a" (lam a. mktyref_ d (lam r. tyarrows_ [tyapp_ r a, a, tyunit_]))
  | CDeRef _ -> mktyall_ "a" (lam a. mktyref_ d (lam r. tyarrow_ (tyapp_ r a) a))
end

lang ConTagTypeAst = TyConst + ConTagAst
  sem tyConstBase d =
  | CConstructorTag _ -> mktyall_ "a" (lam a. tyarrow_ a tyint_)
end

lang TensorOpTypeAst = TyConst + TensorOpAst
  sem tyConstBase d =
  | CTensorCreateUninitInt _ -> tytensorcreateuninitint_
  | CTensorCreateUninitFloat _ -> tytensorcreateuninitfloat_
  | CTensorCreateInt _ -> tytensorcreateint_
  | CTensorCreateFloat _ -> tytensorcreatefloat_
  | CTensorCreate _ -> mktyall_ "a" (lam a. tytensorcreate_ a)
  | CTensorGetExn _ -> mktyall_ "a" (lam a. tytensorgetexn_ a)
  | CTensorSetExn _ -> mktyall_ "a" (lam a. tytensorsetexn_ a)
  | CTensorLinearGetExn _ -> mktyall_ "a" (lam a. tytensorlineargetexn_ a)
  | CTensorLinearSetExn _ -> mktyall_ "a" (lam a. tytensorlinearsetexn_ a)
  | CTensorRank _ -> mktyall_ "a" (lam a. tytensorrank_ a)
  | CTensorShape _ -> mktyall_ "a" (lam a. tytensorshape_ a)
  | CTensorReshapeExn _ -> mktyall_ "a" (lam a. tytensorreshapeexn_ a)
  | CTensorCopy _ -> mktyall_ "a" (lam a. tytensorcopy_ a)
  | CTensorTransposeExn _ -> mktyall_ "a" (lam a. tytensortransposeexn_ a)
  | CTensorSliceExn _ -> mktyall_ "a" (lam a. tytensorsliceexn_ a)
  | CTensorSubExn _ -> mktyall_ "a" (lam a. tytensorsubexn_ a)
  | CTensorIterSlice _ -> mktyall_ "a" (lam a. tytensoriteri_ a)
  | CTensorEq _ -> mktyall_ "a" (lam a. mktyall_ "b" (lam b. tytensoreq_ a b))
  | CTensorToString _ -> mktyall_ "a" (lam a. tytensortostring_ a)
end

lang BootParserTypeAst = TyConst + BootParserAst
  sem tyConstBase d =
  | CBootParserParseMExprString _ ->
    mktybootparsetree_ d (lam b.
      tyarrows_ [
        tytuple_ [tybool_],
        tyseq_ tystr_,
        tystr_,
        b
      ])
  | CBootParserParseMLangString _ ->
    mktybootparsetree_ d (lam b.
      tyarrows_ [
        tystr_,
        b
      ])
  | CBootParserParseMLangFile _ ->
    mktybootparsetree_ d (lam b.
      tyarrows_ [
        tystr_,
        b
      ])
  | CBootParserParseMCoreFile _ ->
    mktybootparsetree_ d (lam b.
      tyarrows_ [
        tytuple_ [tybool_, tybool_ ,tyseq_ tystr_, tybool_, tybool_, tybool_],
        tyseq_ tystr_,
        tystr_,
        b
      ])
  | CBootParserGetId _ -> mktybootparsetree_ d (lam b. tyarrow_ b tyint_)
  | CBootParserGetTerm _ -> mktybootparsetree_ d (lam b. tyarrows_ [b, tyint_, b])
  | CBootParserGetTop _ -> mktybootparsetree_ d (lam b. tyarrows_ [b, tyint_, b])
  | CBootParserGetDecl _ -> mktybootparsetree_ d (lam b. tyarrows_ [b, tyint_, b])
  | CBootParserGetType _ -> mktybootparsetree_ d (lam b. tyarrows_ [b, tyint_, b])
  | CBootParserGetString _ -> mktybootparsetree_ d (lam b. tyarrows_ [b, tyint_, tystr_])
  | CBootParserGetInt _ -> mktybootparsetree_ d (lam b. tyarrows_ [b, tyint_, tyint_])
  | CBootParserGetFloat _ -> mktybootparsetree_ d (lam b. tyarrows_ [b, tyint_, tyfloat_])
  | CBootParserGetListLength _ -> mktybootparsetree_ d (lam b. tyarrows_ [b, tyint_, tyint_])
  | CBootParserGetConst _ -> mktybootparsetree_ d (lam b. tyarrows_ [b, tyint_, b])
  | CBootParserGetPat _ -> mktybootparsetree_ d (lam b. tyarrows_ [b, tyint_, b])
  | CBootParserGetInfo _ -> mktybootparsetree_ d (lam b. tyarrows_ [b, tyint_, b])
end

lang MExprConstType =
  LiteralTypeAst + ArithIntTypeAst + ShiftIntTypeAst + ArithFloatTypeAst +
  CmpIntTypeAst + IntCharConversionTypeAst + CmpFloatTypeAst + CmpCharTypeAst +
  SymbTypeAst + CmpSymbTypeAst + SeqOpTypeAst + FileOpTypeAst + IOTypeAst +
  RandomNumberGeneratorTypeAst + SysTypeAst + FloatIntConversionTypeAst +
  FloatStringConversionTypeAst + TimeTypeAst + RefOpTypeAst + ConTagTypeAst +
  TensorOpTypeAst + BootParserTypeAst + UnsafeCoerceTypeAst
end
