-- Comparison functions for MExpr. Currently only consists of a simple comparison function for types. Much of this file should probably be generated automatically at some point.

include "ast.mc"
include "ast-builder.mc"

-------------------
-- BASE FRAGMENT --
-------------------

lang Cmp = Ast

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
  -- | ty: Type
  -- Intentionally left blank

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
  UnknownTypeCmp + BoolTypeCmp + IntTypeCmp + FloatTypeCmp + CharTypeCmp +
  FunTypeCmp + SeqTypeCmp + TensorTypeCmp + RecordTypeCmp + VariantTypeCmp +
  VarTypeCmp + AppTypeCmp

lang MExprCmpTypeIndex = MExprAst

  -- NOTE(dlunde,2021-05-11): This function cannot be defined in isolation for
  -- each component fragment (as with cmpTypeH). Optimally, this would be
  -- automatically generated.
  sem typeIndex =
  | TyUnknown _ -> 0
  | TyBool _ -> 1
  | TyInt _ -> 2
  | TyFloat _ -> 3
  | TyChar _ -> 4
  | TyArrow _ -> 5
  | TySeq _ -> 6
  | TyRecord _ -> 7
  | TyVariant _ -> 8
  | TyVar _ -> 9
  | TyApp _ -> 10
  | TyTensor _ -> 11

end

lang MExprCmpClosed = MExprCmp + MExprCmpTypeIndex

-----------
-- TESTS --
-----------

mexpr

use MExprCmpClosed in

utest cmpType tyunknown_ tyunknown_ with 0 in
utest cmpType tybool_ tybool_ with 0 in
utest cmpType tyint_ tyint_ with 0 in
utest cmpType tyfloat_ tyfloat_ with 0 in
utest cmpType tychar_ tychar_ with 0 in

utest cmpType (tyarrow_ tybool_ tybool_) (tyarrow_ tybool_ tybool_) with 0 in
utest cmpType (tyarrow_ tybool_ tyint_) (tyarrow_ tybool_ tybool_) with 1 in

utest cmpType (tyseq_ tybool_) (tyseq_ tybool_) with 0 in
utest cmpType (tyseq_ tybool_) (tyseq_ tyfloat_) with negi 2 in

utest cmpType (tyrecord_ [("a", tybool_)]) (tyrecord_ [("a", tybool_)]) with 0 in
utest cmpType (tyrecord_ [("b", tybool_)]) (tyrecord_ [("a", tybool_)]) with 1 in

utest cmpType (tyvariant_ []) (tyvariant_ []) with 0 in

utest cmpType (tyvar_ "t") (tyvar_ "t") with 0 in
utest cmpType (tyvar_ "a") (tyvar_ "b") with negi 1 in

utest cmpType (tyapp_ tybool_ tybool_) (tyapp_ tybool_ tybool_) with 0 in
utest cmpType (tyapp_ tybool_ tybool_) (tyapp_ tyfloat_ tybool_) with negi 2 in

utest cmpType (tytensor_ tybool_) (tytensor_ tybool_) with 0 in
utest cmpType (tytensor_ tybool_) (tytensor_ tyint_) with negi 1 in

()
