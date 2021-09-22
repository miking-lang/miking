include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

type OCamlTopBinding =
  { ident : Name
    , tyBody : Type
    , body : Expr
  }

lang OCamlTopAst
  syn Top =
  | OTopVariantTypeDecl { ident : Name, constrs : Map Name Type }
  | OTopCExternalDecl { ident : Name, ty : Type, bytecodeIdent : Name,
                        nativeIdent : Name }
  | OTopLet { ident : Name, tyBody: Type, body : Expr }
  | OTopRecLets { bindings : [OCamlTopBinding] }
  | OTopExpr { expr : Expr }
end

lang OCamlRecord
  syn Expr =
  | OTmRecord {bindings : [(String, Expr)], tyident : Type}
  | OTmProject {field : String, tm : Expr}

  syn Pat =
  | OPatRecord {bindings : Map SID Pat}

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | OTmRecord t ->
    let bindFunc = lam acc. lam bind : (String, Expr).
      match f acc bind.1 with (acc, expr) then
        (acc, (bind.0, expr))
      else never in
    match mapAccumL bindFunc acc t.bindings with (acc, bindings) then
      (acc, OTmRecord {t with bindings = bindings})
    else never
  | OTmProject t ->
    match f acc t.tm with (acc, tm) then
      (acc, OTmProject {t with tm = tm})
    else never
end

lang OCamlMatch
  syn Expr =
  | OTmMatch
    { target : Expr
    , arms : [(Pat, Expr)]
    }

  syn Pat =

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | OTmMatch t ->
    let armsFunc = lam acc. lam arm : (Pat, Expr).
      match f acc arm.1 with (acc, expr) then
        (acc, (arm.0, expr))
      else never in
    match f acc t.target with (acc, target) then
      match mapAccumL armsFunc acc t.arms with (acc, arms) then
        (acc, OTmMatch {{t with target = target}
                           with arms = arms})
      else never
    else never
end

lang OCamlArray
  syn Expr =
  | OTmArray {tms : [Expr]}

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | OTmArray t ->
    match mapAccumL f acc t.tms with (acc, tms) then
      (acc, OTmArray {t with tms = tms})
    else never
end

lang OCamlTuple
  syn Expr =
  | OTmTuple { values : [Expr] }

  syn Pat =
  | OPatTuple { pats : [Pat] }

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | OTmTuple t ->
    match mapAccumL f acc t.values with (acc, values) then
      (acc, OTmTuple {t with values = values})
    else never
end

lang OCamlData
  syn Expr =
  | OTmConApp { ident : Name, args : [Expr] }

  syn Pat =
  | OPatCon { ident : Name, args : [Pat] }

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | OTmConApp t ->
    match mapAccumL f acc t.args with (acc, args) then
      (acc, OTmConApp {t with args = args})
    else never
end

lang OCamlString
  syn Expr =
  | OTmString { text : String }
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

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | OTmConAppExt t ->
    match mapAccumL f acc t.args with (acc, args) then
      (acc, OTmConAppExt {t with args = args})
    else never
end

lang OCamlLabel
  syn Expr =
  | OTmLabel { label : String, arg : Expr }

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | OTmLabel t ->
    match f acc t.arg with (acc, arg) then
      (acc, OTmLabel {t with arg = arg})
    else never
end

lang OCamlLam
  syn Expr =
  | OTmLam {label : Option String, ident : Name, body : Expr}

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | OTmLam t ->
    match f acc t.body with (acc, body) then
      (acc, OTmLam {t with body = body})
    else never
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
  | OTyRecord {info : Info, fields : [(String, Type)], tyident : Type}
  | OTyString {info: Info}

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
  | OTyString r -> r.info
end

lang OCamlAst =
  -- Tops
  OCamlTopAst +

  -- Terms
  LamAst + LetAst + RecLetsAst + RecordAst + OCamlMatch + OCamlTuple +
  OCamlArray + OCamlData + OCamlRecord + OCamlLabel + OCamlLam +

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

let otyrecord_ = use OCamlAst in
  lam tyident. lam fields.
    OTyRecord {info = NoInfo (), tyident = tyident, fields = fields}

let otystring_ = use OCamlAst in
  OTyString {info = NoInfo ()}

let otyopaque_ = otyvarext_ "opaque" []

mexpr
()
