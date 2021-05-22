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
  syn Expr =
  | OTmRecord {bindings : [(String, Expr)]}
  | OTmProject {field : String, tm : Expr}

  syn Pat =
  | OPatRecord {bindings : Map SID Pat}

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmRecord t -> OTmRecord {t with bindings = mapMap f t.bindings}
  | OTmProject t -> OTmProject {t with tm = f t.tm}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmRecord t ->
    foldl (lam acc. lam a : (String, Expr). f acc a.1) acc t.bindings
  | OTmProject t -> f acc t.tm
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

lang OCamlLabel
  syn Expr =
  | OTmLabel { label : String, arg : Expr }

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | OTmLabel t -> f acc t.arg

  sem smap_Expr_Expr (f : Expr -> a) =
  | OTmLabel t -> OTmLabel { t with arg = f t.arg }
end

lang OCamlTypeAst =
  BoolTypeAst + IntTypeAst + FloatTypeAst + CharTypeAst + RecordTypeAst +
  FunTypeAst + OCamlLabel

  syn Type =
  | OTyList {info : Info, ty : Type}
  | OTyArray {info : Info, ty : Type}
  | OTyTuple {info : Info, tys : [Type]}
  | OTyBigarrayGenarray {info : Info, tys : [Type]}
  | OTyBigarrayArray {info : Info, rank : Int, tys : [Type]}
  | OTyBigarrayFloat64Elt {info : Info}
  | OTyBigarrayIntElt {info : Info}
  | OTyBigarrayClayout {info : Info}
  | OTyLabel {info : Info, label : String, ty : Type}
  | OTyVarExt {info : Info, ident : String, args : [Type]}
  | OTyParam {info : Info, ident : String}
  | OTyRecord {info : Info, fields : [(String, Type)]}

  sem infoTy =
  | OTyList r -> r.info
  | OTyArray r -> r.info
  | OTyTuple r -> r.info
  | OTyBigarrayGenarray r -> r.info
  | OTyBigarrayArray r -> r.info
  | OTyBigarrayFloat64Elt r -> r.info
  | OTyBigarrayIntElt r -> r.info
  | OTyBigarrayClayout r -> r.info
  | OTyLabel r -> r.info
  | OTyVarExt r -> r.info
  | OTyParam r -> r.info
  | OTyRecord r -> r.info
end

lang OCamlAst =
  -- Terms
  LamAst + LetAst + RecLetsAst + RecordAst + OCamlMatch + OCamlTuple +
  OCamlArray + OCamlData + OCamlTypeDeclAst + OCamlRecord + OCamlLabel +

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
  lam tys. OTyBigarrayGenarray {info = NoInfo (), tys = tys}

let otybaarray_ = use OCamlAst in
  lam rank. lam tys.
    OTyBigarrayArray {info = NoInfo (), rank = rank, tys = tys}

let oclayout_ = use OCamlAst in
  OTyBigarrayClayout {info = NoInfo ()}

let otygenarrayclayoutint_ = use OCamlAst in
  otygenarray_ [tyint_, OTyBigarrayIntElt {info = NoInfo ()}, oclayout_]

let otygenarrayclayoutfloat_ = use OCamlAst in
  otygenarray_ [tyfloat_, OTyBigarrayFloat64Elt {info = NoInfo ()}, oclayout_]

let otybaarrayclayoutint_ = use OCamlAst in
  lam rank.
    otybaarray_ rank [tyint_, OTyBigarrayIntElt {info = NoInfo ()}, oclayout_]

let otybaarrayclayoutfloat_ = use OCamlAst in
  lam rank.
    otybaarray_
      rank [tyfloat_, OTyBigarrayFloat64Elt {info = NoInfo ()}, oclayout_]

let otytuple_ = use OCamlAst in
  lam tys. OTyTuple {info = NoInfo (), tys = tys}

let otyunit_ = otytuple_ []

let otyvarext_ = use OCamlAst in
  lam ident. lam args. OTyVarExt {info = NoInfo (), ident = ident, args = args}

let otyparam_ = use OCamlAst in
  lam ident. OTyParam {info = NoInfo (), ident = ident}

let otylabel_ = use OCamlAst in
  lam label. lam ty. OTyLabel {info = NoInfo (), label = label, ty = ty}

mexpr
()
