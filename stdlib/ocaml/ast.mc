include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

lang OCamlTypeDeclAst
  syn Expr =
  | OTmVariantTypeDecl { ident : Name, constrs : Map Name Type, inexpr : Expr }

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmVariantTypeDecl t ->
    OTmVariantTypeDecl {t with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmVariantTypeDecl t -> f acc t.inexpr
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
                 with arms = map (lam p : (Pat, Expr). (p.0, f p.1)) t.arms}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmMatch t -> foldl (lam acc. lam a : (Pat, Expr). f acc a.1) (f acc t.target) t.arms
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

lang OCamlArgLabels
  syn Expr =
  | OTmArgLabel { label : String, arg : Expr }

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmArgLabel t -> f acc t.arg

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmArgLabel t -> OTmArgLabel { t with arg = f t.arg }
end

lang OCamlTypeAst =
  BoolTypeAst + IntTypeAst + FloatTypeAst + CharTypeAst + RecordTypeAst + FunTypeAst

  syn Type =
  | OTyList {info : Info, ty : Type}
  | OTyArray {info : Info, ty : Type}
  | OTyTuple {info : Info, tys : [Type]}
  | OTyBigArrayGenArray {info : Info, tys : [Type]}
  | OTyBigArrayFloat64Elt {info : Info}
  | OTyBigArrayIntElt {info : Info}
  | OTyBigArrayClayout {info : Info}
  | OTyLabel {info : Info, label : String, ty : Type}
  | OTyVarExt {info : Info, ident : String, args : [Type]}
  | OTyParam {info : Info, ident : String}

  sem infoTy =
  | OTyList r -> r.info
  | OTyArray r -> r.info
  | OTyTuple r -> r.info
  | OTyBigArrayGenArray r -> r.info
  | OTyBigArrayFloat64Elt r -> r.info
  | OTyBigArrayIntElt r -> r.info
  | OTyBigArrayClayout r -> r.info
  | OTyLabel r -> r.info
  | OTyVarExt r -> r.info
  | OTyParam r -> r.info
end

lang OCamlAst =
  -- Terms
  LamAst + LetAst + RecLetsAst + RecordAst + OCamlMatch + OCamlTuple +
  OCamlArray + OCamlData + OCamlTypeDeclAst + OCamlRecord + OCamlArgLabels +

  -- Constants
  ArithIntAst + ShiftIntAst + ArithFloatAst + BoolAst + FloatIntConversionAst +
  IntCharConversionAst + OCamlString + RefOpAst +

  -- Patterns
  NamedPat + IntPat + CharPat + BoolPat +

  -- Compares
  CmpIntAst + CmpFloatAst + CharAst + CmpCharAst +

  -- Other
  OCamlExternal +

  -- Types
  OCamlTypeAst
end

let otylist_ = use OCamlAst in
  lam ty. OTyList {info = NoInfo (), ty = ty}

let otyarray_ = use OCamlAst in
  lam ty. OTyArray {info = NoInfo (), ty = ty}

let otygenarray_ = use OCamlAst in
  lam tys. OTyBigArrayGenArray {info = NoInfo (), tys = tys}

let oclayout_ = use OCamlAst in
  OTyBigArrayClayout {info = NoInfo ()}

let otygenarrayclayoutint_ = use OCamlAst in
  otygenarray_ [tyint_, OTyBigArrayIntElt {info = NoInfo ()}, oclayout_]

let otygenarrayclayoutfloat_ = use OCamlAst in
  otygenarray_ [tyfloat_, OTyBigArrayFloat64Elt {info = NoInfo ()}, oclayout_]

let otytuple_ = use OCamlAst in
  lam tys. OTyTuple {info = NoInfo (), tys = tys}

let otyunit_ = otytuple_ []

let otyvarext_ = use OCamlAst in
  lam ident. lam args. OTyVarExt { info = NoInfo (), ident = ident, args = args}

let otyparam_ = use OCamlAst in
  lam ident. OTyParam {info = NoInfo (), ident = ident}

mexpr
()
