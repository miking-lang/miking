include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"

type TypeEnv = AssocMap Name Type

let _tyEnvInsert = assocInsert {eq = nameEqSym}
let _tyEnvLookup = assocLookup {eq = nameEqSym}

let _isTypeAscription = use MExprAst in
  lam letTerm.
  match letTerm.inexpr with TmVar {ident = id} then
    nameEq letTerm.ident id
  else false

lang TypeAnnot = UnknownTypeAst
  sem typeExpr (env : TypeEnv) =

  sem typeAnnotExpr (env : TypeEnv) =

  sem typeAnnot =
  | expr -> typeAnnotExpr assocEmpty expr
end

lang VarTypeAnnot = TypeAnnot + VarAst
  sem typeExpr (env : TypeEnv) =
  | TmVar t ->
    match t.ty with TyUnknown {} then
      match _tyEnvLookup t.ident env with Some ty then
        ty
      else t.ty
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | var & TmVar t ->
    TmVar {t with ty = typeExpr env var}
end

lang AppTypeAnnot = TypeAnnot + AppAst + FunTypeAst + MExprEq
  sem typeExpr (env : TypeEnv) =
  | TmApp t ->
    match t.ty with TyUnknown {} then
      match typeExpr env t.lhs with TyArrow {from = from, to = to} then
        let ty = typeExpr env t.rhs in
        if eqType from ty then
          to
        else
          error "Unexpected type of right-hand side of application"
      else
        error "Unexpected type of left-hand side of application"
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | TmApp t ->
    let t = {{t with lhs = typeAnnotExpr env t.lhs}
                with rhs = typeAnnotExpr env t.rhs} in
    TmApp {t with ty = typeExpr env (TmApp t)}
end

lang FunTypeAnnot = TypeAnnot + FunAst + FunTypeAst
  sem typeExpr (env : TypeEnv) =
  | TmLam t ->
    match t.ty with TyUnknown {} then
      TyArrow {from = t.ty, to = typeExpr env t.body}
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | TmLam t ->
    let env = _tyEnvInsert t.ident t.ty env in
    let t = {t with body = typeAnnotExpr env t.body} in
    TmLam {t with ty = typeExpr env (TmLam t)}
end

lang RecordTypeAnnot = TypeAnnot + RecordAst + RecordTypeAst
  sem typeExpr (env : TypeEnv) =
  | TmRecord t ->
    let f = lam acc. lam k. lam v.
      assocInsert {eq=eqString} k (typeExpr env v) acc
    in
    TyRecord {fields = assocFold {eq=eqString} f assocEmpty t.bindings}
  | TmRecordUpdate t -> typeExpr env t.rec
end

lang LetTypeAnnot = TypeAnnot + LetAst
  sem typeExpr (env : TypeEnv) =
  | TmLet t ->
    match t.ty with TyUnknown {} then
      typeExpr env t.body
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | l & TmLet t ->
    if _isTypeAscription t then
      let ty = typeExpr env l in
      withType ty t.body
    else
      let t = {t with body = typeAnnotExpr env t.body} in
      let ty = typeExpr env (TmLet t) in
      let env = _tyEnvInsert t.ident ty env in
      TmLet {{t with ty = ty}
                with inexpr = typeAnnotExpr env t.inexpr}
end

lang ConstTypeAnnot = TypeAnnot + ConstAst
  sem typeConst =

  sem typeExpr (env : TypeEnv) =
  | TmConst {val = v} -> typeConst v
end

lang MatchTypeAnnot = TypeAnnot + MatchAst
  sem typeExpr (env : TypeEnv) =
  | TmMatch t ->
    match t.ty with TyUnknown {} then
      typeExpr env t.thn
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | TmMatch t ->
    let t = {{{t with target = typeAnnotExpr env t.target}
                 with thn = typeAnnotExpr env t.thn}
                 with els = typeAnnotExpr env t.els} in
    TmMatch {t with ty = typeExpr env (TmMatch t)}
end

lang SeqTypeAnnot = TypeAnnot + SeqAst + MExprEq
  sem typeExpr (env : TypeEnv) =
  | TmSeq t ->
    match t.ty with TyUnknown {} then
      let tpes = map (typeExpr env) t.tms in
      let fst = get tpes 0 in
      if all (lam t. eqType t fst) tpes then
        tyseq_ fst
      else
        error "Sequence contains elements of different types"
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | TmSeq t ->
    let t = {t with tms = map (typeAnnotExpr env) t.tms} in
    TmSeq {t with ty = typeExpr env (TmSeq t)}
end

lang IntTypeAnnot = ConstTypeAnnot + IntAst
  sem typeConst =
  | CInt _ -> tyint_
end

lang ArithIntTypeAnnot = ConstTypeAnnot + ArithIntAst
  sem typeConst =
  | CAddi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CSubi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CMuli _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CDivi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CNegi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CModi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
end

lang ShiftIntTypeAnnot = ConstTypeAnnot + ShiftIntAst
  sem typeConst =
  | CSlli _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CSrli _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CSrai _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
end

lang FloatTypeAnnot = ConstTypeAnnot + FloatAst
  sem typeConst =
  | CFloat _ -> tyfloat_
end

lang ArithFloatTypeAnnot = ConstTypeAnnot + ArithFloatAst
  sem typeConst =
  | CAddf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)
  | CSubf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)
  | CMulf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)
  | CDivf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)
  | CNegf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)
end

lang FloatIntConversionTypeAnnot = ConstTypeAnnot + FloatIntConversionAst
  sem typeConst =
  | CFloorfi _ -> tyarrow_ tyfloat_ tyint_
  | CCeilfi _ -> tyarrow_ tyfloat_ tyint_
  | CRoundfi _ -> tyarrow_ tyfloat_ tyint_
  | CInt2float _ -> tyarrow_ tyint_ tyfloat_
end

lang BoolTypeAnnot = ConstTypeAnnot + BoolAst
  sem typeConst =
  | CBool _ -> tybool_
end

lang CmpIntTypeAnnot = ConstTypeAnnot + CmpIntAst
  sem typeConst =
  | CEqi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tybool_)
  | CNeqi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tybool_)
  | CLti _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tybool_)
  | CGti _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tybool_)
  | CLeqi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tybool_)
  | CGeqi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tybool_)
end

lang CmpFloatTypeAnnot = ConstTypeAnnot + CmpFloatAst
  sem typeConst =
  | CEqf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_)
  | CNeqf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_)
  | CLtf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_)
  | CGtf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_)
  | CLeqf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_)
  | CGeqf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_)
end

lang CharTypeAnnot = ConstTypeAnnot + CharAst
  sem typeConst =
  | CChar _ -> tychar_
end

lang CmpCharTypeAnnot = ConstTypeAnnot + CmpCharAst
  sem typeConst =
  | CEqc _ -> tyarrow_ tychar_ (tyarrow_ tychar_ tybool_)
end

lang IntCharConversionTypeAnnot = ConstTypeAnnot + IntCharConversionAst
  sem typeConst =
  | CInt2Char _ -> tyarrow_ tyint_ tychar_
  | CChar2Int _ -> tyarrow_ tychar_ tyint_
end

lang FloatStringConversionTypeAnnot = ConstTypeAnnot + FloatStringConversionAst
  sem typeConst =
  | CString2float _ -> tyarrow_ tystr_ tyfloat_
end

lang MExprTypeAnnot =

  -- Terms
  VarTypeAnnot + AppTypeAnnot + FunTypeAnnot + RecordTypeAnnot + LetTypeAnnot +
  ConstTypeAnnot + MatchTypeAnnot + SeqTypeAnnot +

  -- Constants
  IntTypeAnnot + ArithIntTypeAnnot + ShiftIntTypeAnnot + FloatTypeAnnot +
  ArithFloatTypeAnnot + FloatIntConversionTypeAnnot + BoolTypeAnnot +
  CmpIntTypeAnnot + CmpFloatTypeAnnot + CharTypeAnnot + CmpCharTypeAnnot +
  IntCharConversionTypeAnnot + FloatStringConversionTypeAnnot

  sem typeExpr (env : TypeEnv) =
  | t -> TyUnknown {}

  sem typeAnnotExpr (env : TypeEnv) =
  | t -> smap_Expr_Expr (typeAnnotExpr env) t
end

lang TestLang = MExprTypeAnnot + MExprPrettyPrint + MExprEq

mexpr

use TestLang in

let x = nameSym "x" in
let y = nameSym "y" in
let z = nameSym "z" in
let n = nameSym "n" in


-- Type annotation of terms

let ascription = lam body.
  bind_ (nlet_ x tyunknown_ body) (nvar_ x)
in

let appBody = addi_ (int_ 5) (int_ 2) in
utest typeAnnot (ascription appBody)
with  withType tyint_ appBody
using eqExpr in

let lamBody = nulam_ y (float_ 2.718) in
utest typeAnnot (ascription lamBody)
with  withType (tyarrow_ tyunknown_ tyfloat_) lamBody
using eqExpr in

let recordBody = record_ [("a", int_ 2), ("b", float_ 2.0), ("c", false_)] in
let recordType = tyrecord_ [
  ("a", tyint_), ("b", tyfloat_), ("c", tybool_)
] in
utest typeAnnot (ascription recordBody)
with  withType recordType recordBody
using eqExpr in

let constBody = const_ (int_ 0) in
utest typeAnnot (ascription constBody)
with  withType tyint_ constBody
using eqExpr in

let matchBody = if_ true_ (int_ 2) (int_ 3) in
utest typeAnnot (ascription matchBody)
with  withType tyint_ matchBody
using eqExpr in

let seqBody = seq_ [int_ 2, int_ 3, int_ 4] in
utest typeAnnot (ascription seqBody)
with  withType (tyseq_ tyint_) seqBody
using eqExpr in

-- Type annotation of constant terms

let constlet = lam body. lam ty.
  bind_ (nlet_ x ty body) unit_ in

let intLiteralLet = constlet (int_ 4) in
utest typeAnnot (intLiteralLet tyunknown_)
with  intLiteralLet tyint_
using eqExpr in

let addiLet = constlet (const_ (CAddi ())) in
utest typeAnnot (addiLet tyunknown_)
with  addiLet (tyarrow_ tyint_ (tyarrow_ tyint_ tyint_))
using eqExpr in

let floatLiteralLet = constlet (float_ 4.0) in
utest typeAnnot (floatLiteralLet tyunknown_)
with  floatLiteralLet tyfloat_
using eqExpr in

let boolLiteralLet = constlet true_ in
utest typeAnnot (boolLiteralLet tyunknown_)
with  boolLiteralLet tybool_
using eqExpr in

let charLiteralLet = constlet (char_ 'a') in
utest typeAnnot (charLiteralLet tyunknown_)
with  charLiteralLet tychar_
using eqExpr in

let partialApp = lam ty1. lam ty2.
  bind_
    (nlet_ x ty1 (withType ty1 (app_ (const_ (CLtf ())) (float_ 3.14))))
    (withType ty2 (app_ (withType ty1 (nvar_ x)) (float_ 2.718)))
in
utest typeAnnot (partialApp tyunknown_ tyunknown_)
with  partialApp (tyarrow_ tyfloat_ tybool_) tybool_
using eqExpr in

()

