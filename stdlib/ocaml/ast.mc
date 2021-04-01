include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

lang OCamlTypeDeclAst
  syn Expr =
  | OTmVariantTypeDecl { ident : Name, constrs : Map Name Type, inexpr : Expr }

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmVariantTypeDecl t ->
    OTmVariantTypeDecl {t with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmVariantTypeDecl t ->
    sfold_Expr_Expr f acc t.inexpr
end

lang OCamlRecord
  syn Pat =
  | OPatRecord {bindings : Map SID Pat}
end

lang OCamlMatch
  syn Expr =
  | OTmMatch
    { target : Expr
    , arms : [(Pat, Expr)]
    }

  syn Pat =

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmMatch t ->
    OTmMatch {{t with target = f t.target}
                 with arms = map (lam p. (p.0, f p.1)) t.arms}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmMatch t -> foldl (lam acc. lam a. f acc a.1) (f acc t.target) t.arms
end

lang OCamlArray
  syn Expr =
  | OTmArray {tms : [Expr]}

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmArray t -> OTmArray {t with tms = map f t.tms}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmArray t -> foldl f acc t.tms
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

lang OCamlString
  syn Expr =
  | OTmString { text : String }

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmString t -> OTmString t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmString t -> acc
end

-- This fragment is a hack used to enable inserting the preamble after variant
-- type declarations, but before the rest of the program.
lang OCamlPreambleHack
  syn Expr =
  | OTmPreambleText { text : String, inexpr : Expr }

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmPreambleText t -> OTmPreambleText {t with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmPreambleText t -> f acc t.inexpr
end

-- This fragment contains variants of other ocaml constructs where the
-- names should appear exactly as specified, intended to be used to
-- refer to externally defined names, e.g., in the ocaml standard
-- library. Note that these names will not affect other names in any
-- way, meaning that these names should be chosen so that they
-- *cannot* overlap with other names. An easy way to do that is to
-- always use fully qualified names, since normal names cannot contain
-- dots.
lang OCamlExternal
  syn Expr =
  | OTmVarExt { ident : String }
  | OTmConAppExt { ident : String, args : [Expr] }

  syn Pat =
  | OPatConExt { ident : String, args : [Pat] }

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmVarExt t -> acc
  | OTmConAppExt t -> foldl f acc t.args

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmVarExt t -> OTmVarExt t
  | OTmConAppExt t -> OTmConAppExt {t with args = map f t.args}
end

lang OCamlTryWith
  syn Expr =
  | OTmTryWith { body : Expr,  arms : [(Pat, Expr)] }
end

lang OCamlAst = LamAst + LetAst + RecLetsAst + RecordAst + ArithIntAst
                + ShiftIntAst + ArithFloatAst + BoolAst + CmpIntAst
                + CmpFloatAst + CharAst + CmpCharAst  + NamedPat
                + IntPat + CharPat + BoolPat  + FloatIntConversionAst
                + IntCharConversionAst + RefOpAst

                + OCamlTuple + OCamlArray + OCamlMatch + OCamlData
                + OCamlExternal + OCamlTryWith + OCamlPreambleHack
                + OCamlTypeDeclAst + OCamlRecord + OCamlString

end

mexpr
()
