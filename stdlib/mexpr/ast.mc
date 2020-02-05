include "string.mc"

lang VarAst
  syn Expr =
  | TmVar String
end

lang VarPat
  syn Pat =
  | PVar String
end


lang AppAst
  syn Expr =
  | TmApp (Expr, Expr)
end


lang FunAst = VarAst + AppAst
  syn Type =
  | TyArrow (Type, Type)
  syn Expr =
  | TmLam (String, Option, Expr) -- Option Type
end


lang LetAst = VarAst
  syn Expr =
  | TmLet (String, Option, Expr, Expr) -- Option Type
end


lang RecLetsAst = VarAst
  syn Type =
  syn Expr =
  | TmRecLets ([(String, Option, Expr)], Expr) -- Option Type
end


lang ConstAst
  syn Const =

  syn Expr =
  | TmConst (Const)
end


lang UnitAst = ConstAst
  syn Const =
  | CUnit ()
end

lang UnitPat = UnitAst
  syn Pat =
  | PUnit ()
end


lang IntAst = ConstAst
  syn Const =
  | CInt Int
end

lang IntPat = IntAst
  syn Pat =
  | PInt Int
end


lang ArithIntAst = ConstAst + IntAst
  syn Const =
  | CAddi ()
  | CSubi ()
  | CMuli ()
end


lang BoolAst
  syn Const =
  | CNot ()
  | CAnd ()
  | COr ()

  syn Expr =
  | TmIf (Expr, Expr, Expr)
end

lang BoolPat = BoolAst
  syn Pat =
  | PBool Bool
end


lang CmpAst = IntAst + BoolAst
  syn Const =
  | CEqi ()
  | CLti ()
end


lang CharAst = ConstAst
  syn Const =
  | CChar Char
end


lang SeqAst = IntAst
  syn Const =
  | CSeq [Expr]
  | CNth ()

  syn Expr =
  | TmSeq [Expr]
end


lang TupleAst
  syn Expr =
  | TmTuple [Expr]
  | TmProj (Expr, Int)
end

lang TuplePat = TupleAst
  syn Pat =
  | PTuple [Pat]
end


lang DataAst
  -- TODO: Constructors have no generated symbols
  syn Expr =
  | TmConDef (String, Expr)
  | TmConFun (String)
end

lang DataPat = DataAst
  syn Pat =
  | PCon (String, Pat)
end


lang MatchAst
  syn Expr =
  | TmMatch (Expr, Pat, Expr, Expr)

  syn Pat =
end

lang UtestAst
  syn Expr =
  | TmUtest (Expr, Expr, Expr)
end


lang DynTypeAst
  syn Type =
  | TyDyn
end

lang UnitTypeAst
  syn Type =
  | TyUnit
end

lang SeqTypeAst
  syn Type =
  | TySeq Type
end

lang TupleTypeAst
  syn Type =
  | TyProd [Type]
end

lang DataTypeAst
  syn Type =
  | TyCon String
end

lang ArithTypeAst
  syn Type =
  | TyInt
end

lang BoolTypeAst
  syn Type =
  | TyBool
end

lang AppTypeAst
  syn Type =
  | TyApp (Type, Type)
end


lang MExprAst =
  VarAst + AppAst + FunAst + LetAst + RecLetsAst + ConstAst +
  UnitAst + UnitPat + IntAst + IntPat +
  ArithIntAst + BoolAst + BoolPat + CmpAst + CharAst + SeqAst +
  TupleAst + TuplePat + DataAst + DataPat + MatchAst + VarPat + UtestAst
