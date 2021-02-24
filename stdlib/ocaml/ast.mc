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
end

lang OCamlTuple
  syn Expr =
  | OTmTuple { values : [Expr] }

  syn Pat =
  | OPTuple { pats : [Pat] }
end

lang OCamlData
  syn Expr =
  | OTmConApp { ident : Name, args : [Expr] }

  syn Pat =
  | OPCon { ident : Name, args : [Pat] }

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
