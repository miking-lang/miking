include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

lang OCamlTypeDeclAst
  syn Expr =
  | OTmVariantTypeDecl { ident : Name, constrs : [(Name, Type)], inexpr : Expr }

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmVariantTypeDecl t ->
    OTmVariantTypeDecl {t with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmVariantTypeDecl t ->
    sfold_Expr_Expr f acc t.inexpr
end

lang OCamlRecord
  syn Expr =
  | OTmRecord {bindings : [(String, Expr)]}

  syn Pat =
  | OPatRecord {bindings : AssocMap String Pat}

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmRecord t -> OTmRecord {t with bindings = map (lam b. (b.0, f b.1)) t.bindings}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmRecord t -> foldl (lam acc. lam b. f acc b.1) acc t.bindings
end

lang OCamlMatch
  syn Expr =
  | OTmMatch
    { target : Expr
    , arms : [(Pat, Expr)]
    }

  syn Pat =

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmMatch t -> OTmMatch {{t with target = f t.target}
                               with arms = map (lam a. (a.0, f a.1)) t.arms}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmMatch t -> foldl (lam acc. lam a. f acc a.1) (f acc t.target) t.arms
end

lang OCamlTuple
  syn Expr =
  | OTmTuple { values : [Expr] }

  syn Pat =
  | OPatTuple { pats : [Pat] }

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmTuple t -> OTmTuple {t with values = map f t.values}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmTuple t -> foldl f acc t.values
end

lang OCamlData
  syn Expr =
  | OTmConApp { ident : Name, args : [Expr] }

  syn Pat =
  | OPatCon { ident : Name, args : [Pat] }

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmConApp t -> OTmConApp {t with args = map f t.args}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmConApp t -> foldl f acc t.args
end

lang OCamlAst = LamAst + LetAst + RecLetsAst + ArithIntAst + ShiftIntAst
                + ArithFloatAst + BoolAst + CmpIntAst + CmpFloatAst
                + CharAst + OCamlMatch + NamedPat + IntPat + CharPat
                + BoolPat + OCamlTuple + OCamlData + OCamlRecord
                + CharAst + FloatIntConversionAst + OCamlTypeDeclAst
end

mexpr
()
