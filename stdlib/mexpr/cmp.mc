-- Comparison functions for MExpr. Much of this file should probably be generated automatically at some point.

include "ast.mc"
include "ast-builder.mc"

-------------------
-- BASE FRAGMENT --
-------------------

lang Cmp = Ast

  sem cmpExpr (lhs: Expr) =
  | rhs /- : Expr -/ -> cmpExprH (lhs, rhs)

  sem cmpExprH =
  -- Default case when expressions are not the same
  | (lhs, rhs) /- (Expr, Expr) -/ ->
    let res = subi (exprIndex lhs) (exprIndex rhs) in
    if eqi res 0 then
      error "Missing case in cmpExprH for expressions with equal indices."
    else res

  sem exprIndex =
  | t /- : Expr -/ -> constructorTag t

  sem cmpConst (lhs: Const) =
  | rhs /- : Const -/ -> cmpConstH (lhs, rhs)

  sem cmpConstH =
  -- Default case when constants are not the same
  | (lhs, rhs) /- (Const, Const) -/ ->
    let res = subi (constIndex lhs) (constIndex rhs) in
    if eqi res 0 then
      error "Missing case in cmpConstH for constants with equal indices."
    else res

  sem constIndex =
  | c /- : Const -/ -> constructorTag c

  sem cmpPat (lhs: Pat) =
  | rhs /- : Pat -/ -> cmpPatH (lhs, rhs)

  sem cmpPatH =
  -- Default case when patterns are not the same
  | (lhs, rhs) /- (Pat, Pat) -/ ->
    let res = subi (patIndex lhs) (patIndex rhs) in
    if eqi res 0 then
      error "Missing case in cmpPatH for patterns with equal indices."
    else res

  sem patIndex =
  | p /- : Pat -/ -> constructorTag p

  sem cmpType (lhs: Type) =
  | rhs /- : Type -/ -> cmpTypeH (lhs, rhs)

  sem cmpTypeH =
  -- Default case when types are not the same
  | (lhs, rhs) /- (Type, Type) -/ ->
    let res = subi (typeIndex lhs) (typeIndex rhs) in
    if eqi res 0 then
      error "Missing case in cmpTypeH for types with equal indices."
    else res

  sem typeIndex =
  | ty /- : Type -/ -> constructorTag ty

end

-----------
-- TERMS --
-----------

lang VarCmp = Cmp + VarAst
  sem cmpExprH =
  | (TmVar l, TmVar r) ->
    nameCmp l.ident r.ident
end

lang AppCmp = Cmp + AppAst
  sem cmpExprH =
  | (TmApp l, TmApp r) ->
    let lhsDiff = cmpExpr l.lhs r.lhs in
    if eqi lhsDiff 0 then cmpExpr l.rhs r.rhs
    else lhsDiff
end

lang LamCmp = Cmp + LamAst
  sem cmpExprH =
  | (TmLam l, TmLam r) ->
    let identDiff = nameCmp l.ident r.ident in
    if eqi identDiff 0 then cmpExpr l.body r.body
    else identDiff
end

lang LetCmp = Cmp + LetAst
  sem cmpExprH =
  | (TmLet l, TmLet r) ->
    let identDiff = nameCmp l.ident r.ident in
    if eqi identDiff 0 then
      let bodyDiff = cmpExpr l.body r.body in
      if eqi bodyDiff 0 then cmpExpr l.inexpr r.inexpr
      else bodyDiff
    else identDiff
end

lang RecLetBindingCmp = Cmp
  sem cmpRecLetBinding (lhs : RecLetBinding) =
  | rhs ->
    let rhs : RecLetBinding = rhs in
    let identDiff = nameCmp lhs.ident rhs.ident in
    if eqi identDiff 0 then
      cmpExpr lhs.body rhs.body
    else identDiff
end

lang RecLetsCmp = Cmp + RecLetsAst + RecLetBindingCmp
  sem cmpExprH =
  | (TmRecLets l, TmRecLets r) ->
    let bindingsDiff = seqCmp cmpRecLetBinding l.bindings r.bindings in
    if eqi bindingsDiff 0 then
      cmpExpr l.inexpr r.inexpr
    else bindingsDiff
end

lang ConstCmp = Cmp + ConstAst
  sem cmpExprH =
  | (TmConst l, TmConst r) -> cmpConst l.val r.val
end

lang SeqCmp = Cmp + SeqAst
  sem cmpExprH =
  | (TmSeq l, TmSeq r) -> seqCmp cmpExpr l.tms r.tms
end

lang RecordCmp = Cmp + RecordAst
  sem cmpExprH =
  | (TmRecord l, TmRecord r) -> mapCmp cmpExpr l.bindings r.bindings
  | (TmRecordUpdate l, TmRecordUpdate r) ->
    let recDiff = cmpExpr l.rec r.rec in
    if eqi recDiff 0 then
      let keyDiff = cmpSID l.key r.key in
      if eqi keyDiff 0 then cmpExpr l.value r.value
      else keyDiff
    else recDiff
end

lang TypeCmp = Cmp + TypeAst
  sem cmpExprH =
  | (TmType l, TmType r) ->
    let identDiff = nameCmp l.ident r.ident in
    if eqi identDiff 0 then
      let tyIdentDiff = cmpType l.tyIdent r.tyIdent in
      if eqi tyIdentDiff 0 then cmpExpr l.inexpr r.inexpr
      else tyIdentDiff
    else identDiff
end

lang DataCmp = Cmp + DataAst
  sem cmpExprH =
  | (TmConDef l, TmConDef r) ->
    let identDiff = nameCmp l.ident r.ident in
    if eqi identDiff 0 then
      let tyIdentDiff = cmpType l.tyIdent r.tyIdent in
      if eqi tyIdentDiff 0 then cmpExpr l.inexpr r.inexpr
      else tyIdentDiff
    else identDiff
  | (TmConApp l, TmConApp r) ->
    let identDiff = nameCmp l.ident r.ident in
    if eqi identDiff 0 then cmpExpr l.body r.body
    else identDiff
end

lang MatchCmp = Cmp + MatchAst
  sem cmpExprH =
  | (TmMatch l, TmMatch r) ->
    let targetDiff = cmpExpr l.target r.target in
    if eqi targetDiff 0 then
      let patDiff = cmpPat l.pat r.pat in
      if eqi patDiff 0 then
        let thnDiff = cmpExpr l.thn r.thn in
        if eqi thnDiff 0 then cmpExpr l.els r.els
        else thnDiff
      else patDiff
    else targetDiff
end

lang UtestCmp = Cmp + UtestAst
  sem cmpExprH =
  | (TmUtest l, TmUtest r) ->
    let testDiff = cmpExpr l.test r.test in
    if eqi testDiff 0 then
      let expectedDiff = cmpExpr l.expected r.expected in
      if eqi expectedDiff 0 then
        let nextDiff = cmpExpr l.next r.next in
        if eqi nextDiff 0 then
          let t = (l.tusing, r.tusing) in
          match t with (Some a, Some b) then
            cmpExpr a b
          else match t with (Some _, None _) then
            1
          else match t with (None _, Some _) then
            negi 1
          else 0
        else nextDiff
      else expectedDiff
    else testDiff
end

lang NeverCmp = Cmp + NeverAst
  sem cmpExprH =
  | (TmNever _, TmNever _) -> 0
end

lang ExtCmp = Cmp + ExtAst
  sem cmpExprH =
  | (TmExt l, TmExt r) ->
    let identDiff = nameCmp l.ident r.ident in
    if eqi identDiff 0 then
      let tyIdentDiff = cmpType l.tyIdent r.tyIdent in
      if eqi tyIdentDiff 0 then
        let leffect = if l.effect then 1 else 0 in
        let reffect = if r.effect then 1 else 0 in
        let effectDiff = subi leffect reffect in
        if eqi effectDiff 0 then cmpExpr l.inexpr r.inexpr
        else effectDiff
      else tyIdentDiff
    else identDiff
end

---------------
-- CONSTANTS --
---------------

lang IntCmp = Cmp + IntAst
  sem cmpConstH =
  | (CInt l, CInt r) -> subi l.val r.val
end

lang ArithIntCmp = Cmp + ArithIntAst
  sem cmpConstH =
  | (CAddi _, CAddi _) -> 0
  | (CSubi _, CSubi _) -> 0
  | (CMuli _, CMuli _) -> 0
  | (CDivi _, CDivi _) -> 0
  | (CNegi _, CNegi _) -> 0
  | (CModi _, CModi _) -> 0
end

lang ShiftIntCmp = Cmp + ShiftIntAst
  sem cmpConstH =
  | (CSlli _, CSlli _) -> 0
  | (CSrli _, CSrli _) -> 0
  | (CSrai _, CSrai _) -> 0
end

lang FloatCmp = Cmp + FloatAst
  sem cmpConstH =
  | (CFloat l, CFloat r) ->
    let x = subf l.val r.val in
    if gtf x 0.0 then 1
    else if ltf x 0.0 then negi 1
    else 0
end

lang ArithFloatCmp = Cmp + ArithFloatAst
  sem cmpConstH =
  | (CAddf _, CAddf _) -> 0
  | (CSubf _, CSubf _) -> 0
  | (CMulf _, CMulf _) -> 0
  | (CDivf _, CDivf _) -> 0
  | (CNegf _, CNegf _) -> 0
end

lang FloatIntConversionCmp = Cmp + FloatIntConversionAst
  sem cmpConstH =
  | (CFloorfi _, CFloorfi _) -> 0
  | (CCeilfi _, CCeilfi _) -> 0
  | (CRoundfi _, CRoundfi _) -> 0
  | (CInt2float _, CInt2float _) -> 0
end

lang BoolCmp = Cmp + BoolAst
  sem cmpConstH =
  | (CBool l, CBool r) ->
    let lval = if l.val then 1 else 0 in
    let rval = if r.val then 1 else 0 in
    subi lval rval
end

lang CmpIntCmp = Cmp + CmpIntAst
  sem cmpConstH =
  | (CEqi _, CEqi _) -> 0
  | (CNeqi _, CNeqi _) -> 0
  | (CLti _, CLti _) -> 0
  | (CGti _, CGti _) -> 0
  | (CLeqi _, CLeqi _) -> 0
  | (CGeqi _, CGeqi _) -> 0
end

lang CmpFloatCmp = Cmp + CmpFloatAst
  sem cmpConstH =
  | (CEqf _, CEqf _) -> 0
  | (CLtf _, CLtf _) -> 0
  | (CLeqf _, CLeqf _) -> 0
  | (CGtf _, CGtf _) -> 0
  | (CGeqf _, CGeqf _) -> 0
  | (CNeqf _, CNeqf _) -> 0
end

lang CharCmp = Cmp + CharAst
  sem cmpConstH =
  | (CChar l, CChar r) -> subi (char2int l.val) (char2int r.val)
end

lang CmpCharCmp = Cmp + CmpCharAst
  sem cmpConstH =
  | (CEqc _, CEqc _) -> 0
end

lang IntCharConversionCmp = Cmp + IntCharConversionAst
  sem cmpConstH =
  | (CInt2Char _, CInt2Char _) -> 0
  | (CChar2Int _, CChar2Int _) -> 0
end

lang FloatStringConversionCmp = Cmp + FloatStringConversionAst
  sem cmpConstH =
  | (CString2float _, CString2float _) -> 0
  | (CFloat2string _, CFloat2string _) -> 0
end

lang SymbCmp = Cmp + SymbAst
  sem cmpConstH =
  | (CSymb l, CSymb r) -> subi (sym2hash l.val) (sym2hash r.val)
  | (CGensym _, CGensym _) -> 0
  | (CSym2hash _, CSym2hash _) -> 0
end

lang CmpSymbCmp = Cmp + CmpSymbAst
  sem cmpConstH =
  | (CEqsym _, CEqsym _) -> 0
end

lang SeqOpCmp = Cmp + SeqOpAst
  sem cmpConstH =
  | (CSet _, CSet _) -> 0
  | (CGet _, CGet _) -> 0
  | (CCons _, CCons _) -> 0
  | (CSnoc _, CSnoc _) -> 0
  | (CConcat _, CConcat _) -> 0
  | (CLength _, CLength _) -> 0
  | (CReverse _, CReverse _) -> 0
  | (CHead _, CHead _) -> 0
  | (CTail _, CTail _) -> 0
  | (CNull _, CNull _) -> 0
  | (CMap _, CMap _) -> 0
  | (CMapi _, CMapi _) -> 0
  | (CIter _, CIter _) -> 0
  | (CIteri _, CIteri _) -> 0
  | (CFoldl _, CFoldl _) -> 0
  | (CFoldr _, CFoldr _) -> 0
  | (CCreate _, CCreate _) -> 0
  | (CCreateFingerTree _, CCreateFingerTree _) -> 0
  | (CCreateList _, CCreateList _) -> 0
  | (CCreateRope _, CCreateRope _) -> 0
  | (CSplitAt _, CSplitAt _) -> 0
  | (CSubsequence _, CSubsequence _) -> 0
end

lang FileOpCmp = Cmp + FileOpAst
  sem cmpConstH =
  | (CFileRead _, CFileRead _) -> 0
  | (CFileWrite _, CFileWrite _) -> 0
  | (CFileExists _, CFileExists _) -> 0
  | (CFileDelete _, CFileDelete _) -> 0
end

lang IOCmp = Cmp + IOAst
  sem cmpConstH =
  | (CPrint _, CPrint _) -> 0
  | (CDPrint _, CDPrint _) -> 0
  | (CFlushStdout _, CFlushStdout _) -> 0
  | (CReadLine _, CReadLine _) -> 0
  | (CReadBytesAsString _, CReadBytesAsString _) -> 0
end

lang RandomNumberGeneratorCmp = Cmp + RandomNumberGeneratorAst
  sem cmpConstH =
  | (CRandIntU _, CRandIntU _) -> 0
  | (CRandSetSeed _, CRandSetSeed _) -> 0
end

lang SysCmp = Cmp + SysAst
  sem cmpConstH =
  | (CExit _, CExit _) -> 0
  | (CError _, CError _) -> 0
  | (CArgv _, CArgv _) -> 0
  | (CCommand _, CCommand _) -> 0
end

lang TimeCmp = Cmp + TimeAst
  sem cmpConstH =
  | (CWallTimeMs _, CWallTimeMs _) -> 0
  | (CSleepMs _, CSleepMs _) -> 0
end

lang RefOpCmp = Cmp + RefOpAst
  sem cmpConstH =
  | (CRef _, CRef _) -> 0
  | (CModRef _, CModRef _) -> 0
  | (CDeRef _, CDeRef _) -> 0
end

lang MapCmp = Cmp + MapAst
  sem cmpConstH =
  | (CMapEmpty _, CMapEmpty _) -> 0
  | (CMapInsert _, CMapInsert _) -> 0
  | (CMapRemove _, CMapRemove _) -> 0
  | (CMapFindWithExn _, CMapFindWithExn _) -> 0
  | (CMapFindOrElse _, CMapFindOrElse _) -> 0
  | (CMapFindApplyOrElse _, CMapFindApplyOrElse _) -> 0
  | (CMapBindings _, CMapBindings _) -> 0
  | (CMapSize _, CMapSize _) -> 0
  | (CMapMem _, CMapMem _) -> 0
  | (CMapAny _, CMapAny _) -> 0
  | (CMapMap _, CMapMap _) -> 0
  | (CMapMapWithKey _, CMapMapWithKey _) -> 0
  | (CMapFoldWithKey _, CMapFoldWithKey _) -> 0
  | (CMapEq _, CMapEq _) -> 0
  | (CMapCmp _, CMapCmp _) -> 0
  | (CMapGetCmpFun _, CMapGetCmpFun _) -> 0
end

lang TensorOpCmp = Cmp + TensorOpAst
  sem cmpConstH =
  | (CTensorCreateInt _, CTensorCreateInt _) -> 0
  | (CTensorCreateFloat _, CTensorCreateFloat _) -> 0
  | (CTensorCreate _, CTensorCreate _) -> 0
  | (CTensorGetExn _, CTensorGetExn _) -> 0
  | (CTensorSetExn _, CTensorSetExn _) -> 0
  | (CTensorRank _, CTensorRank _) -> 0
  | (CTensorShape _, CTensorShape _) -> 0
  | (CTensorReshapeExn _, CTensorReshapeExn _) -> 0
  | (CTensorCopyExn _, CTensorCopyExn _) -> 0
  | (CTensorSliceExn _, CTensorSliceExn _) -> 0
  | (CTensorSubExn _, CTensorSubExn _) -> 0
  | (CTensorIterSlice _, CTensorIterSlice _) -> 0
end

lang BootParserCmp = Cmp + BootParserAst
  sem cmpConstH =
  | (CBootParserParseMExprString _, CBootParserParseMExprString _) -> 0
  | (CBootParserParseMCoreFile _, CBootParserParseMCoreFile _) -> 0
  | (CBootParserGetId _, CBootParserGetId _) -> 0
  | (CBootParserGetTerm _, CBootParserGetTerm _) -> 0
  | (CBootParserGetType _, CBootParserGetType _) -> 0
  | (CBootParserGetString _, CBootParserGetString _) -> 0
  | (CBootParserGetInt _, CBootParserGetInt _) -> 0
  | (CBootParserGetFloat _, CBootParserGetFloat _) -> 0
  | (CBootParserGetListLength _, CBootParserGetListLength _) -> 0
  | (CBootParserGetConst _, CBootParserGetConst _) -> 0
  | (CBootParserGetPat _, CBootParserGetPat _) -> 0
  | (CBootParserGetInfo _, CBootParserGetInfo _) -> 0
end

--------------
-- PATTERNS --
--------------

lang PatNameCmp = Cmp
  sem cmpPatName =
  | (PName l, PName r) -> nameCmp l r
  | (PName _, PWildcard _) -> 1
  | (PWildcard _, PName _) -> negi 1
  | _ -> 0
end

lang NamedPatCmp = Cmp + NamedPat + PatNameCmp
  sem cmpPatH =
  | (PatNamed l, PatNamed r) -> cmpPatName (l.ident, r.ident)
end

lang SeqTotPatCmp = Cmp + SeqTotPat
  sem cmpPatH =
  | (PatSeqTot l, PatSeqTot r) -> seqCmp cmpPat l.pats r.pats
end

lang SeqEdgePatCmp = Cmp + SeqEdgePat + PatNameCmp
  sem cmpPatH =
  | (PatSeqEdge l, PatSeqEdge r) ->
    let prefixDiff = seqCmp cmpPat l.prefix r.prefix in
    if eqi prefixDiff 0 then
      let middleDiff = cmpPatName (l.middle, r.middle) in
      if eqi middleDiff 0 then
        seqCmp cmpPat l.postfix r.postfix
      else middleDiff
    else prefixDiff
end

lang RecordPatCmp = Cmp + RecordPat
  sem cmpPatH =
  | (PatRecord l, PatRecord r) -> mapCmp cmpPat l.bindings r.bindings
end

lang DataPatCmp = Cmp + DataPat
  sem cmpPatH =
  | (PatCon l, PatCon r) ->
    let identDiff = nameCmp l.ident r.ident in
    if eqi identDiff 0 then
      cmpPat l.subpat r.subpat
    else identDiff
end

lang IntPatCmp = Cmp + IntPat
  sem cmpPatH =
  | (PatInt l, PatInt r) -> subi l.val r.val
end

lang CharPatCmp = Cmp + CharPat
  sem cmpPatH =
  | (PatChar l, PatChar r) -> subi (char2int l.val) (char2int r.val)
end

lang BoolPatCmp = Cmp + BoolPat
  sem cmpPatH =
  | (PatBool l, PatBool r) ->
    let lval = if l.val then 1 else 0 in
    let rval = if r.val then 1 else 0 in
    subi lval rval
end

lang AndPatCmp = Cmp + AndPat
  sem cmpPatH =
  | (PatAnd l, PatAnd r) ->
    let lpatDiff = cmpPat l.lpat r.lpat in
    if eqi lpatDiff 0 then cmpPat l.rpat r.rpat
    else lpatDiff
end

lang OrPatCmp = Cmp + OrPat
  sem cmpPatH =
  | (PatOr l, PatOr r) ->
    let lpatDiff = cmpPat l.lpat r.lpat in
    if eqi lpatDiff 0 then cmpPat l.rpat r.rpat
    else lpatDiff
end

lang NotPatCmp = Cmp + NotPat
  sem cmpPatH =
  | (PatNot l, PatNot r) -> cmpPat l.subpat r.subpat
end

-----------
-- TYPES --
-----------

lang UnknownTypeCmp = Cmp + UnknownTypeAst
  sem cmpTypeH =
  | (TyUnknown _, TyUnknown _) -> 0
end

lang BoolTypeCmp = Cmp + BoolTypeAst
  sem cmpTypeH =
  | (TyBool _, TyBool _) -> 0
end

lang IntTypeCmp = Cmp + IntTypeAst
  sem cmpTypeH =
  | (TyInt _, TyInt _) -> 0
end

lang FloatTypeCmp = Cmp + FloatTypeAst
  sem cmpTypeH =
  | (TyFloat _, TyFloat _) -> 0
end

lang CharTypeCmp = Cmp + CharTypeAst
  sem cmpTypeH =
  | (TyChar _, TyChar _) -> 0
end

lang FunTypeCmp = Cmp + FunTypeAst
  sem cmpTypeH =
  | (TyArrow t1, TyArrow t2) ->
    let fromDiff = cmpType t1.from t2.from in
    if eqi fromDiff 0 then cmpType t1.to t2.to
    else fromDiff
end

lang SeqTypeCmp = Cmp + SeqTypeAst
  sem cmpTypeH =
  | (TySeq { ty = t1 }, TySeq { ty = t2 }) -> cmpType t1 t2
end

lang TensorTypeCmp = Cmp + TensorTypeAst
  sem cmpTypeH =
  | (TyTensor { ty = t1 }, TyTensor { ty = t2 }) -> cmpType t1 t2
end

lang RecordTypeCmp = Cmp + RecordTypeAst
  sem cmpTypeH =
  | (TyRecord t1, TyRecord t2) -> mapCmp cmpType t1.fields t2.fields
end

lang VariantTypeCmp = Cmp + VariantTypeAst
  sem cmpTypeH =
  | (TyVariant t1, TyVariant t2) -> mapCmp cmpType t1.constrs t2.constrs
end

lang VarTypeCmp = Cmp + VarTypeAst
  sem cmpTypeH =
  | (TyVar t1, TyVar t2) -> nameCmp t1.ident t2.ident
end

lang AppTypeCmp = Cmp + AppTypeAst
  sem cmpTypeH =
  | (TyApp t1, TyApp t2) ->
    let lhsDiff = cmpType t1.lhs t2.lhs in
    if eqi lhsDiff 0 then cmpType t1.rhs t2.rhs
    else lhsDiff
end

--------------------
-- MEXPR FRAGMENT --
--------------------

lang MExprCmp =

  -- Terms
  VarCmp + AppCmp + LamCmp + RecordCmp + LetCmp + TypeCmp + RecLetsCmp +
  ConstCmp + DataCmp + MatchCmp + UtestCmp + SeqCmp + NeverCmp + ExtCmp +

  -- Constants
  IntCmp + ArithIntCmp + ShiftIntCmp + FloatCmp + ArithFloatCmp + BoolCmp +
  CmpIntCmp + IntCharConversionCmp + CmpFloatCmp + CharCmp + CmpCharCmp +
  SymbCmp + CmpSymbCmp + SeqOpCmp + FileOpCmp + IOCmp +
  RandomNumberGeneratorCmp + SysCmp + FloatIntConversionCmp +
  FloatStringConversionCmp + TimeCmp + RefOpCmp + MapCmp + TensorOpCmp +
  BootParserCmp +

  -- Patterns
  NamedPatCmp + SeqTotPatCmp + SeqEdgePatCmp + RecordPatCmp + DataPatCmp +
  IntPatCmp + CharPatCmp + BoolPatCmp + AndPatCmp + OrPatCmp + NotPatCmp +

  -- Types
  UnknownTypeCmp + BoolTypeCmp + IntTypeCmp + FloatTypeCmp + CharTypeCmp +
  FunTypeCmp + SeqTypeCmp + TensorTypeCmp + RecordTypeCmp + VariantTypeCmp +
  VarTypeCmp + AppTypeCmp

-----------
-- TESTS --
-----------

mexpr

use MExprCmp in

-- Expressions
utest cmpExpr (var_ "a") (var_ "a") with 0 in
utest cmpExpr (var_ "b") (var_ "a") with 0 using neqi in

utest cmpExpr (app_ (var_ "a") (var_ "b"))
              (app_ (var_ "a") (var_ "b")) with 0 in
utest cmpExpr (app_ (var_ "a") (var_ "a"))
              (app_ (var_ "a") (var_ "b")) with 0 using neqi in

utest cmpExpr (ulam_ "a" (var_ "a")) (ulam_ "a" (var_ "a")) with 0 in
utest cmpExpr (ulam_ "b" (var_ "a")) (ulam_ "a" (var_ "a")) with 0 using neqi in
utest cmpExpr (ulam_ "a" (var_ "b")) (ulam_ "a" (var_ "a")) with 0 using neqi in

utest cmpExpr (bind_ (ulet_ "b" (var_ "a")) (var_ "b"))
              (bind_ (ulet_ "b" (var_ "a")) (var_ "b")) with 0 in
utest cmpExpr (bind_ (ulet_ "b" (var_ "a")) (var_ "b"))
              (bind_ (ulet_ "a" (var_ "a")) (var_ "b")) with 0 using neqi in
utest cmpExpr (bind_ (ulet_ "a" (var_ "b")) (var_ "b"))
              (bind_ (ulet_ "a" (var_ "a")) (var_ "b")) with 0 using neqi in
utest cmpExpr (bind_ (ulet_ "a" (var_ "a")) (var_ "b"))
              (bind_ (ulet_ "a" (var_ "a")) (var_ "a")) with 0 using neqi in

utest cmpExpr (ureclets_ []) (ureclets_ []) with 0 in
utest cmpExpr (ureclets_ [("a", ulam_ "b" (var_ "a"))])
              (ureclets_ [("a", ulam_ "a" (var_ "a"))]) with 0 using neqi in

utest cmpExpr (int_ 0) (int_ 0) with 0 in
utest cmpExpr (int_ 1) (int_ 0) with 0 using neqi in

utest cmpExpr (seq_ []) (seq_ []) with 0 in
utest cmpExpr (seq_ [int_ 1, int_ 2]) (seq_ [int_ 1]) with 0 using neqi in
utest cmpExpr (seq_ [int_ 1, int_ 2]) (seq_ [int_ 2]) with 0 using neqi in
utest cmpExpr (seq_ [int_ 1, int_ 2]) (seq_ [int_ 1, int_ 2]) with 0 in

utest cmpExpr unit_ unit_ with 0 in
utest cmpExpr (urecord_ [("a", int_ 0)])
              (urecord_ [("a", int_ 0)]) with 0 in
utest cmpExpr (urecord_ [("a", int_ 0), ("b", var_ "a")])
              (urecord_ [("a", int_ 0)]) with 0 using neqi in
utest cmpExpr (urecord_ [("a", int_ 0), ("b", var_ "a")])
              (urecord_ [("a", int_ 0), ("b", int_ 0)]) with 0 using neqi in

let r = urecord_ [("a", int_ 0), ("b", char_ 'c')] in
utest cmpExpr (recordupdate_ r "a" (int_ 1))
              (recordupdate_ r "a" (int_ 1)) with 0 in
utest cmpExpr (recordupdate_ r "a" (int_ 0))
              (recordupdate_ r "a" (int_ 1)) with 0 using neqi in
utest cmpExpr (recordupdate_ r "b" (int_ 0))
              (recordupdate_ r "a" (int_ 1)) with 0 using neqi in

utest cmpExpr (type_ "a" tyint_) (type_ "a" tyint_) with 0 in
utest cmpExpr (type_ "b" tyint_) (type_ "a" tyint_) with 0 using neqi in
utest cmpExpr (type_ "a" tyfloat_) (type_ "a" tyint_) with 0 using neqi in

utest cmpExpr (condef_ "a" tyint_) (condef_ "a" tyint_) with 0 in
utest cmpExpr (condef_ "b" tyint_) (condef_ "a" tyint_) with 0 using neqi in
utest cmpExpr (condef_ "a" tyfloat_) (condef_ "a" tyint_) with 0 using neqi in
utest cmpExpr (conapp_ "a" (var_ "b")) (conapp_ "a" (var_ "b")) with 0 in
utest cmpExpr (conapp_ "b" (var_ "b")) (conapp_ "a" (var_ "b")) with 0
using neqi in
utest cmpExpr (conapp_ "a" (int_ 0)) (conapp_ "a" (var_ "a")) with 0
using neqi in

utest cmpExpr (match_ (var_ "a") pvarw_ (int_ 0) (int_ 1))
              (match_ (var_ "a") (pvar_ "x") (int_ 0) (int_ 1)) with 0
using neqi in
utest cmpExpr (if_ (var_ "a") (int_ 0) (int_ 1))
              (if_ (var_ "a") (int_ 0) (int_ 1)) with 0 in
utest cmpExpr (if_ (var_ "b") (int_ 0) (int_ 1))
              (if_ (var_ "a") (int_ 0) (int_ 1)) with 0 using neqi in
utest cmpExpr (if_ (var_ "a") (int_ 1) (int_ 1))
              (if_ (var_ "a") (int_ 0) (int_ 1)) with 0 using neqi in
utest cmpExpr (if_ (var_ "a") (int_ 0) (int_ 2))
              (if_ (var_ "a") (int_ 0) (int_ 1)) with 0 using neqi in

utest cmpExpr (utest_ (var_ "a") (var_ "a") unit_)
              (utest_ (var_ "a") (var_ "a") unit_) with 0 in
utest cmpExpr (utest_ (var_ "b") (var_ "a") unit_)
              (utest_ (var_ "a") (var_ "a") unit_) with 0 using neqi in
utest cmpExpr (utest_ (var_ "a") (var_ "b") unit_)
              (utest_ (var_ "a") (var_ "a") unit_) with 0 using neqi in
utest cmpExpr (utestu_ (var_ "a") (var_ "a") unit_ (var_ "cmp"))
              (utest_ (var_ "a") (var_ "a") unit_) with 0 using neqi in

utest cmpExpr never_ never_ with 0 in

utest cmpExpr (ext_ "a" false tyint_) (ext_ "a" false tyint_) with 0 in
utest cmpExpr (ext_ "a" false tyint_) (ext_ "b" false tyint_) with 0
using neqi in
utest cmpExpr (ext_ "a" true tyint_) (ext_ "a" false tyint_) with 0
using neqi in
utest cmpExpr (ext_ "a" true tyunknown_) (ext_ "a" false tyint_) with 0
using neqi in

-- Constants
utest cmpConst (CInt {val = 0}) (CInt {val = 0}) with 0 in
utest cmpConst (CInt {val = 7}) (CInt {val = 0}) with 0 using neqi in
utest cmpConst (CInt {val = negi 2}) (CInt {val = 0}) with 0 using neqi in

utest cmpConst (CAddi {}) (CAddi {}) with 0 in
utest cmpConst (CSubi {}) (CSubi {}) with 0 in
utest cmpConst (CMuli {}) (CMuli {}) with 0 in
utest cmpConst (CDivi {}) (CDivi {}) with 0 in
utest cmpConst (CNegi {}) (CNegi {}) with 0 in
utest cmpConst (CModi {}) (CModi {}) with 0 in
utest cmpConst (CMuli {}) (CSubi {}) with 0 using neqi in
utest cmpConst (CAddi {}) (CDivi {}) with 0 using neqi in

utest cmpConst (CSlli {}) (CSlli {}) with 0 in
utest cmpConst (CSrli {}) (CSrli {}) with 0 in
utest cmpConst (CSrai {}) (CSrai {}) with 0 in
utest cmpConst (CSrli {}) (CSlli {}) with 0 using neqi in

utest cmpConst (CFloat {val = 0.0}) (CFloat {val = 0.0}) with 0 in
utest cmpConst (CFloat {val = 2.718}) (CFloat {val = 3.14}) with 0
using neqi in
utest cmpConst (CFloat {val = 0.001}) (CFloat {val = 0.0}) with 0 using neqi in

utest cmpConst (CAddf {}) (CAddf {}) with 0 in
utest cmpConst (CSubf {}) (CSubf {}) with 0 in
utest cmpConst (CMulf {}) (CMulf {}) with 0 in
utest cmpConst (CDivf {}) (CDivf {}) with 0 in
utest cmpConst (CNegf {}) (CNegf {}) with 0 in
utest cmpConst (CMulf {}) (CSubf {}) with 0 using neqi in
utest cmpConst (CAddf {}) (CDivf {}) with 0 using neqi in

utest cmpConst (CFloorfi {}) (CFloorfi {}) with 0 in
utest cmpConst (CCeilfi {}) (CCeilfi {}) with 0 in
utest cmpConst (CRoundfi {}) (CRoundfi {}) with 0 in
utest cmpConst (CInt2float {}) (CInt2float {}) with 0 in

utest cmpConst (CBool {val = true}) (CBool {val = true}) with 0 in
utest cmpConst (CBool {val = true}) (CBool {val = false}) with 0 using neqi in
utest cmpConst (CBool {val = false}) (CBool {val = true}) with 0 using neqi in
utest cmpConst (CBool {val = false}) (CBool {val = false}) with 0 in
utest cmpConst (CBool {val = true}) (CInt {val = 1}) with 0 using neqi in

utest cmpConst (CEqi {}) (CEqi {}) with 0 in
utest cmpConst (CNeqi {}) (CNeqi {}) with 0 in
utest cmpConst (CLti {}) (CLti {}) with 0 in
utest cmpConst (CGti {}) (CGti {}) with 0 in
utest cmpConst (CLeqi {}) (CLeqi {}) with 0 in
utest cmpConst (CGeqi {}) (CGeqi {}) with 0 in
utest cmpConst (CGti {}) (CEqi {}) with 0 using neqi in
utest cmpConst (CLeqi {}) (CGeqi {}) with 0 using neqi in

utest cmpConst (CEqf {}) (CEqf {}) with 0 in
utest cmpConst (CLtf {}) (CLtf {}) with 0 in
utest cmpConst (CLeqf {}) (CLeqf {}) with 0 in
utest cmpConst (CGtf {}) (CGtf {}) with 0 in
utest cmpConst (CGeqf {}) (CGeqf {}) with 0 in
utest cmpConst (CNeqf {}) (CNeqf {}) with 0 in
utest cmpConst (CGtf {}) (CLeqf {}) with 0 using neqi in
utest cmpConst (CEqf {}) (CNeqf {}) with 0 using neqi in

utest cmpConst (CChar {val = 'a'}) (CChar {val = 'a'}) with 0 in
utest cmpConst (CChar {val = 'z'}) (CChar {val = 'a'}) with 0 using neqi in
utest cmpConst (CChar {val = 'a'}) (CChar {val = 'b'}) with 0 using neqi in
utest cmpConst (CChar {val = 'a'}) (CInt {val = 97}) with 0 using neqi in

utest cmpConst (CEqc {}) (CEqc {}) with 0 in

utest cmpConst (CInt2Char {}) (CInt2Char {}) with 0 in
utest cmpConst (CChar2Int {}) (CChar2Int {}) with 0 in

utest cmpConst (CString2float {}) (CString2float {}) with 0 in
utest cmpConst (CFloat2string {}) (CFloat2string {}) with 0 in

let s1 = gensym () in
let s2 = gensym () in
utest cmpConst (CSymb {val = s1}) (CSymb {val = s1}) with 0 in
utest cmpConst (CSymb {val = s2}) (CSymb {val = s2}) with 0 in
utest cmpConst (CSymb {val = s1}) (CSymb {val = s2}) with 0 using neqi in
utest cmpConst (CSymb {val = s1}) (CInt {val = sym2hash s1}) with 0
using neqi in
utest cmpConst (CGensym {}) (CGensym {}) with 0 in
utest cmpConst (CSym2hash {}) (CSym2hash {}) with 0 in

utest cmpConst (CEqsym {}) (CEqsym {}) with 0 in

utest cmpConst (CSet {}) (CSet {}) with 0 in
utest cmpConst (CGet {}) (CGet {}) with 0 in
utest cmpConst (CCons {}) (CCons {}) with 0 in
utest cmpConst (CSnoc {}) (CSnoc {}) with 0 in
utest cmpConst (CConcat {}) (CConcat {}) with 0 in
utest cmpConst (CLength {}) (CLength {}) with 0 in
utest cmpConst (CReverse {}) (CReverse {}) with 0 in
utest cmpConst (CHead {}) (CHead {}) with 0 in
utest cmpConst (CTail {}) (CTail {}) with 0 in
utest cmpConst (CNull {}) (CNull {}) with 0 in
utest cmpConst (CMap {}) (CMap {}) with 0 in
utest cmpConst (CMapi {}) (CMapi {}) with 0 in
utest cmpConst (CIter {}) (CIter {}) with 0 in
utest cmpConst (CIteri {}) (CIteri {}) with 0 in
utest cmpConst (CFoldl {}) (CFoldl {}) with 0 in
utest cmpConst (CFoldr {}) (CFoldr {}) with 0 in
utest cmpConst (CCreate {}) (CCreate {}) with 0 in
utest cmpConst (CCreateFingerTree {}) (CCreateFingerTree {}) with 0 in
utest cmpConst (CCreateList {}) (CCreateList {}) with 0 in
utest cmpConst (CCreateRope {}) (CCreateRope {}) with 0 in
utest cmpConst (CSplitAt {}) (CSplitAt {}) with 0 in
utest cmpConst (CSubsequence {}) (CSubsequence {}) with 0 in

utest cmpConst (CFileRead {}) (CFileRead {}) with 0 in
utest cmpConst (CFileWrite {}) (CFileWrite {}) with 0 in
utest cmpConst (CFileExists {}) (CFileExists {}) with 0 in
utest cmpConst (CFileDelete {}) (CFileDelete {}) with 0 in

utest cmpConst (CPrint {}) (CPrint {}) with 0 in
utest cmpConst (CDPrint {}) (CDPrint {}) with 0 in
utest cmpConst (CFlushStdout {}) (CFlushStdout {}) with 0 in
utest cmpConst (CReadLine {}) (CReadLine {}) with 0 in
utest cmpConst (CReadBytesAsString {}) (CReadBytesAsString {}) with 0 in

utest cmpConst (CRandIntU {}) (CRandIntU {}) with 0 in
utest cmpConst (CRandSetSeed {}) (CRandSetSeed {}) with 0 in

utest cmpConst (CExit {}) (CExit {}) with 0 in
utest cmpConst (CError {}) (CError {}) with 0 in
utest cmpConst (CArgv {}) (CArgv {}) with 0 in
utest cmpConst (CCommand {}) (CCommand {}) with 0 in

utest cmpConst (CWallTimeMs {}) (CWallTimeMs {}) with 0 in
utest cmpConst (CSleepMs {}) (CSleepMs {}) with 0 in

utest cmpConst (CRef {}) (CRef {}) with 0 in
utest cmpConst (CModRef {}) (CModRef {}) with 0 in
utest cmpConst (CDeRef {}) (CDeRef {}) with 0 in

utest cmpConst (CMapEmpty {}) (CMapEmpty {}) with 0 in
utest cmpConst (CMapInsert {}) (CMapInsert {}) with 0 in
utest cmpConst (CMapRemove {}) (CMapRemove {}) with 0 in
utest cmpConst (CMapFindWithExn {}) (CMapFindWithExn {}) with 0 in
utest cmpConst (CMapFindOrElse {}) (CMapFindOrElse {}) with 0 in
utest cmpConst (CMapFindApplyOrElse {}) (CMapFindApplyOrElse {}) with 0 in
utest cmpConst (CMapBindings {}) (CMapBindings {}) with 0 in
utest cmpConst (CMapSize {}) (CMapSize {}) with 0 in
utest cmpConst (CMapMem {}) (CMapMem {}) with 0 in
utest cmpConst (CMapAny {}) (CMapAny {}) with 0 in
utest cmpConst (CMapMap {}) (CMapMap {}) with 0 in
utest cmpConst (CMapMapWithKey {}) (CMapMapWithKey {}) with 0 in
utest cmpConst (CMapFoldWithKey {}) (CMapFoldWithKey {}) with 0 in
utest cmpConst (CMapEq {}) (CMapEq {}) with 0 in
utest cmpConst (CMapCmp {}) (CMapCmp {}) with 0 in
utest cmpConst (CMapGetCmpFun {}) (CMapGetCmpFun {}) with 0 in

utest cmpConst (CTensorCreateInt {}) (CTensorCreateInt {}) with 0 in
utest cmpConst (CTensorCreateFloat {}) (CTensorCreateFloat {}) with 0 in
utest cmpConst (CTensorCreate {}) (CTensorCreate {}) with 0 in
utest cmpConst (CTensorGetExn {}) (CTensorGetExn {}) with 0 in
utest cmpConst (CTensorSetExn {}) (CTensorSetExn {}) with 0 in
utest cmpConst (CTensorRank {}) (CTensorRank {}) with 0 in
utest cmpConst (CTensorShape {}) (CTensorShape {}) with 0 in
utest cmpConst (CTensorReshapeExn {}) (CTensorReshapeExn {}) with 0 in
utest cmpConst (CTensorCopyExn {}) (CTensorCopyExn {}) with 0 in
utest cmpConst (CTensorSliceExn {}) (CTensorSliceExn {}) with 0 in
utest cmpConst (CTensorSubExn {}) (CTensorSubExn {}) with 0 in
utest cmpConst (CTensorIterSlice {}) (CTensorIterSlice {}) with 0 in

utest cmpConst (CBootParserParseMExprString {})
               (CBootParserParseMExprString {}) with 0 in
utest cmpConst (CBootParserParseMCoreFile {})
               (CBootParserParseMCoreFile {}) with 0 in
utest cmpConst (CBootParserGetId {}) (CBootParserGetId {}) with 0 in
utest cmpConst (CBootParserGetTerm {}) (CBootParserGetTerm {}) with 0 in
utest cmpConst (CBootParserGetType {}) (CBootParserGetType {}) with 0 in
utest cmpConst (CBootParserGetString {}) (CBootParserGetString {}) with 0 in
utest cmpConst (CBootParserGetInt {}) (CBootParserGetInt {}) with 0 in
utest cmpConst (CBootParserGetFloat {}) (CBootParserGetFloat {}) with 0 in
utest cmpConst (CBootParserGetListLength {})
               (CBootParserGetListLength {}) with 0 in
utest cmpConst (CBootParserGetConst {}) (CBootParserGetConst {}) with 0 in
utest cmpConst (CBootParserGetPat {}) (CBootParserGetPat {}) with 0 in
utest cmpConst (CBootParserGetInfo {}) (CBootParserGetInfo {}) with 0 in

-- Patterns
utest cmpPat (pvar_ "a") (pvar_ "a") with 0 in
utest cmpPat (pvar_ "a") pvarw_ with 0 using neqi in
utest cmpPat pvarw_ (pvar_ "a") with 0 using neqi in

utest cmpPat (pseqtot_ [pvar_ "a"]) (pseqtot_ []) with 0 using neqi in
utest cmpPat (pseqtot_ [pvar_ "b"]) (pseqtot_ [pvar_ "a"]) with 0 using neqi in
utest cmpPat (pseqtot_ [pvar_ "a"]) (pseqtot_ [pvar_ "a"]) with 0 in

utest cmpPat (pseqedgew_ [] []) (pseqedgew_ [] []) with 0 in
utest cmpPat (pseqedge_ [] "a" []) (pseqedgew_ [] []) with 0 using neqi in
utest cmpPat (pseqedge_ [] "a" []) (pseqedge_ [] "b" []) with 0 using neqi in
utest cmpPat (pseqedge_ [] "a" []) (pseqedge_ [] "a" []) with 0 in

utest cmpPat punit_ punit_ with 0 in
utest cmpPat (prec_ [("a", pvar_ "a")]) (prec_ []) with 0 using neqi in
utest cmpPat (prec_ [("a", pvar_ "a")]) (prec_ [("a", pvar_ "a")]) with 0 in
utest cmpPat (prec_ [("a", pvar_ "b")]) (prec_ [("a", pvar_ "a")]) with 0
using neqi in

utest cmpPat (pcon_ "x" pvarw_) (pcon_ "x" pvarw_) with 0 in
utest cmpPat (pcon_ "x" (pvar_ "a")) (pcon_ "x" pvarw_) with 0 using neqi in

utest cmpPat (pint_ 0) (pint_ 0) with 0 in
utest cmpPat (pint_ 1) (pint_ 0) with 0 using neqi in
utest cmpPat (pint_ 0) (pint_ 1) with 0 using neqi in

utest cmpPat (pchar_ 'a') (pchar_ 'a') with 0 in
utest cmpPat (pchar_ 'b') (pchar_ 'a') with 0 using neqi in

utest cmpPat ptrue_ ptrue_ with 0 in
utest cmpPat ptrue_ pfalse_ with 0 using neqi in
utest cmpPat pfalse_ ptrue_ with 0 using neqi in
utest cmpPat pfalse_ pfalse_ with 0 in

utest cmpPat (pand_ (pvar_ "a") (pvar_ "a"))
             (pand_ (pvar_ "a") (pvar_ "a")) with 0 in
utest cmpPat (pand_ (pvar_ "a") (pvar_ "b"))
             (pand_ (pvar_ "a") (pvar_ "a")) with 0 using neqi in
utest cmpPat (pand_ (pvar_ "a") (pvar_ "b"))
             (pand_ (pvar_ "b") (pvar_ "a")) with 0 using neqi in

utest cmpPat (por_ (pvar_ "a") (pvar_ "a"))
             (por_ (pvar_ "a") (pvar_ "a")) with 0 in
utest cmpPat (por_ (pvar_ "b") (pvar_ "a"))
             (por_ (pvar_ "a") (pvar_ "b")) with 0 using neqi in

utest cmpPat (pnot_ (pvar_ "b")) (pnot_ (pvar_ "a")) with 0 using neqi in
utest cmpPat (pnot_ (pvar_ "a")) (pnot_ (pvar_ "a")) with 0 in

-- Types
utest cmpType tyunknown_ tyunknown_ with 0 in
utest cmpType tybool_ tybool_ with 0 in
utest cmpType tyint_ tyint_ with 0 in
utest cmpType tyfloat_ tyfloat_ with 0 in
utest cmpType tychar_ tychar_ with 0 in

utest cmpType (tyarrow_ tybool_ tybool_) (tyarrow_ tybool_ tybool_) with 0 in
utest cmpType (tyarrow_ tybool_ tyint_) (tyarrow_ tybool_ tybool_) with 0
using neqi in

utest cmpType (tyseq_ tybool_) (tyseq_ tybool_) with 0 in
utest cmpType (tyseq_ tybool_) (tyseq_ tyfloat_) with 0 using neqi in

utest cmpType (tyrecord_ [("a", tybool_)]) (tyrecord_ [("a", tybool_)]) with 0 in
utest cmpType (tyrecord_ [("b", tybool_)]) (tyrecord_ [("a", tybool_)]) with 0
using neqi in

utest cmpType (tyvariant_ []) (tyvariant_ []) with 0 in

utest cmpType (tyvar_ "t") (tyvar_ "t") with 0 in
utest cmpType (tyvar_ "a") (tyvar_ "b") with 0 using neqi in

utest cmpType (tyapp_ tybool_ tybool_) (tyapp_ tybool_ tybool_) with 0 in
utest cmpType (tyapp_ tybool_ tybool_) (tyapp_ tyfloat_ tybool_) with 0
using neqi in

utest cmpType (tytensor_ tybool_) (tytensor_ tybool_) with 0 in
utest cmpType (tytensor_ tybool_) (tytensor_ tyint_) with 0 using neqi in

()
