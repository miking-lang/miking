include "string.mc"

lang Var
  syn Expr =
  | TmVar String
end


lang App
  syn Expr =
  | TmApp (Expr, Expr)
end


lang Fun = Var + App
  syn Type =
  | TyArrow (Type, Type)
  syn Expr =
  | TmLam (String, Option, Expr) -- Option Type
end


lang Let = Var
  syn Expr =
  | TmLet (String, Option, Expr, Expr) -- Option Type
end


lang RecLets = Var
  syn Type =
  syn Expr =
  | TmRecLets ([(String, Option, Expr)], Expr) -- Option Type
end



lang Const
  syn Const =

  syn Expr =
  | TmConst (Const)
end


lang Unit = Const
  syn Const =
  | CUnit ()
end

lang UnitPat = Unit
  syn Pat =
  | UnitPat ()

  sem tryMatch (t : Expr) =
  | UnitPat _ ->
    match t with TmConst CUnit _ then Some [] else None ()
end



lang Int = Const
  syn Const =
  | CInt Int
end

lang IntPat = Int
  syn Pat =
  | IntPat Int

  sem tryMatch (t : Expr) =
  | IntPat i -> match t with TmConst CInt i2 then
    if eqi i i2 then Some [] else None ()
    else None ()
end



lang Arith = Const + Int
  syn Const =
  | CAddi ()
  | CAddi2 Int
  | CSubi ()
  | CSubi2 Int
  | CMuli
  | CMuli2 Int
  -- TODO: Add more operations
  -- TODO: Add floating point numbers (maybe in its own fragment)
end


lang Bool
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

lang BoolPat = Bool
  syn Pat =
  | BoolPat Bool

  sem tryMatch (t : Expr) =
  | BoolPat b ->
    match t with TmConst CBool b2 then
      if or (and b b2) (and (not b) (not b2)) then Some [] else None () -- TODO: is there a nicer way to do equality on bools? 'eqb' is unbound
    else None ()
end



lang Cmp = Int + Bool
  syn Const =
  | CEqi ()
  | CEqi2 Int
  | CLti ()
  | CLti2 Int
end


lang Char = Const
  syn Const =
  | CChar Char
end


lang Seq = Int
  syn Const =
  | CSeq [Expr]
  | CNth ()
  | CNth2 [Expr]

  syn Expr =
  | TmSeq [Expr]
end


lang Tuple
  syn Expr =
  | TmTuple [Expr]
  | TmProj (Expr, Int)
end


lang TuplePat = Tuple
  syn Pat =
  | TuplePat [Pat]

  sem tryMatch (t : Expr) =
  | TuplePat pats ->
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

lang Data
  -- TODO: Constructors have no generated symbols
  syn Expr =
  | TmConDef (String, Expr)
end



lang DataPat = Data
  syn Pat =
  | ConPat (String, Pat)

  sem tryMatch (t : Expr) =
  | ConPat x -> -- INCONSISTENCY: this won't follow renames in the constructor, but the ml interpreter will
    let constructor = x.0 in
    let subpat = x.1 in
    match t with TmCon (constructor2, subexpr) then
      if eqstr constructor constructor2
        then tryMatch subexpr subpat
        else None ()
    else None ()
end

lang Match
  syn Expr =
  | TmMatch (Expr, Pat, Expr, Expr)

  syn Pat =
end



lang VarPat
  syn Pat =
  | VarPat String

  sem tryMatch (t : Expr) =
  | VarPat ident -> Some [(ident, t)]
end

lang Utest
  syn Expr =
  | TmUtest (Expr, Expr, Expr)
end


lang DynType
  syn Type =
  | TyDyn
end

lang UnitType
  syn Type =
  | TyUnit
end

lang SeqType
  syn Type =
  | TySeq Type
end

lang TupleType
  syn Type =
  | TyProd [Type]
end

lang DataType
  syn Type =
  | TyCon String
end

lang ArithType
  syn Type =
  | TyInt
end

lang BoolType
  syn Type =
  | TyBool
end

lang AppType
  syn Type =
  | TyApp (Type, Type)
end


lang MExprAst =
  Var + App + Fun + Let + RecLets + Const + Unit + UnitPat + Int + IntPat +
  Arith + Bool + BoolPat + Cmp + Char + Seq + Tuple + TuplePat + Data +
  DataPat + Match + VarPat + Utest
