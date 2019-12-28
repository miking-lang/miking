include "string.mc"

lang VarAst
  syn Expr =
  | TmVar String
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

  sem tryMatch (t : Expr) =
  | PUnit _ ->
    match t with TmConst CUnit _ then Some [] else None ()
end



lang IntAst = ConstAst
  syn Const =
  | CInt Int
end

lang IntPat = IntAst
  syn Pat =
  | PInt Int

  sem tryMatch (t : Expr) =
  | PInt i -> match t with TmConst CInt i2 then
    if eqi i i2 then Some [] else None ()
    else None ()
end



lang ArithIntAst = ConstAst + IntAst
  syn Const =
  | CAddi ()
  | CAddi2 Int
  | CSubi ()
  | CSubi2 Int
  | CMuli
  | CMuli2 Int
end


lang BoolAst
  syn Const =
  | CBool Bool
  | CNot ()
  | CAnd ()
  | CAnd2 Bool
  | COr ()
  | COr2 Bool

  syn Expr =
  | TmIf (Expr, Expr, Expr)
end

lang BoolPat = BoolAst
  syn Pat =
  | PBool Bool

  sem tryMatch (t : Expr) =
  | PBool b ->
    match t with TmConst CBool b2 then
      if or (and b b2) (and (not b) (not b2)) then Some [] else None () -- TODO: is there a nicer way to do equality on bools? 'eqb' is unbound
    else None ()
end



lang CmpAst = IntAst + BoolAst
  syn Const =
  | CEqi ()
  | CEqi2 Int
  | CLti ()
  | CLti2 Int
end


lang CharAst = ConstAst
  syn Const =
  | CChar Char
end


lang SeqAst = IntAst
  syn Const =
  | CSeq [Expr]
  | CNth ()
  | CNth2 [Expr]

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

  sem tryMatch (t : Expr) =
  | PTuple pats ->
    match t with TmTuple tms then
      if eqi (length pats) (length tms) then
        let results = zipWith tryMatch tms pats in
        let go = lam left. lam right.
          match (left, right) with (Some l, Some r)
          then Some (concat l r)
          else None () in
        foldl go (Some []) results
      else None ()
    else None ()
end

lang DataAst
  -- TODO: Constructors have no generated symbols
  syn Expr =
  | TmConDef (String, Expr)
end



lang DataPat = DataAst
  syn Pat =
  | PCon (String, Pat)

  sem tryMatch (t : Expr) =
  | PCon x -> -- INCONSISTENCY: this won't follow renames in the constructor, but the ml interpreter will
    let constructor = x.0 in
    let subpat = x.1 in
    match t with TmCon (constructor2, subexpr) then
      if eqstr constructor constructor2
        then tryMatch subexpr subpat
        else None ()
    else None ()
end

lang MatchAst
  syn Expr =
  | TmMatch (Expr, Pat, Expr, Expr)

  syn Pat =
end



lang VarPat
  syn Pat =
  | PVar String

  sem tryMatch (t : Expr) =
  | PVar ident -> Some [(ident, t)]
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
