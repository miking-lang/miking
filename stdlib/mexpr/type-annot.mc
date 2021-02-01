include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"

type TypeEnv = AssocMap Name Type

let _tyEnvInsert = assocInsert {eq = nameEqSym}
let _tyEnvLookup = assocLookup {eq = nameEqSym}

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

lang AppTypeAnnot = TypeAnnot + AppAst + FunTypeAst
  sem typeExpr (env : TypeEnv) =
  | TmApp t ->
    match t.ty with TyUnknown {} then
      TyArrow {from = typeExpr env t.lhs, to = typeExpr env t.rhs}
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | app & TmApp t ->
    TmApp {{{t with ty = typeExpr env app}
               with lhs = typeAnnotExpr env t.lhs}
               with rhs = typeAnnotExpr env t.rhs}
end

lang FunTypeAnnot = TypeAnnot + FunAst + FunTypeAst
  sem typeExpr (env : TypeEnv) =
  | TmLam t ->
    TyArrow {from = t.ty, to = typeExpr env t.body}

  sem typeAnnotExpr (env : TypeEnv) =
  | TmLam t ->
    let env = _tyEnvInsert t.ident t.ty env in
    TmLam {t with body = typeAnnotExpr env t.body}
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
    let ty = typeExpr env l in
    let env2 = _tyEnvInsert t.ident ty env in
    TmLet {{{t with ty = ty}
               with body = typeAnnotExpr env t.body}
               with inexpr = typeAnnotExpr env2 t.inexpr}
end

lang DataTypeAnnot = TypeAnnot + DataAst
  sem typeExpr (env : TypeEnv) =
  | TmConApp t ->
    match t.ty with TyUnknown {} then
      match _tyEnvLookup t.ident env with Some ty then
        ty
      else t.ty
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | c & TmConDef t ->
    let env = _tyEnvInsert t.ident t.ty env in
    TmConDef {t with inexpr = typeAnnotExpr env t.inexpr}
  | c & TmConApp t ->
    TmConApp {{t with ty = typeExpr env c}
                 with body = typeAnnotExpr env t.body}
end

lang MatchTypeAnnot = TypeAnnot + MatchAst
  sem typeExpr (env : TypeEnv) =
  | TmMatch t ->
    match t.ty with TyUnknown {} then
      typeExpr env t.thn
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | m & TmMatch t ->
    TmMatch {{{{t with ty = typeExpr env m}
                  with target = typeAnnotExpr env t.target}
                  with thn = typeAnnotExpr env t.thn}
                  with els = typeAnnotExpr env t.els}
end

lang SeqTypeAnnot = TypeAnnot + SeqAst
  sem typeExpr (env : TypeEnv) =
  | TmSeq t ->
    match t.ty with TyUnknown {} then
      typeExpr env (get t.tms 0)
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | s & TmSeq t ->
    TmSeq {{t with ty = typeExpr env s}
              with tms = map (typeAnnotExpr env) t.tms}
end

lang MExprTypeAnnot = VarTypeAnnot + AppTypeAnnot + FunTypeAnnot + RecordTypeAnnot + LetTypeAnnot
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

let base = nulam_ x (nvar_ x) in
utest typeAnnot base with base using eqExpr in

let letexp = lam ty.
  bind_
    (nlet_ x ty (record_ [
      ("a", int_ 5),
      ("b", float_ 2.718)
    ]))
    unit_ in
utest typeAnnot (letexp tyunknown_)
with  letexp (tyrecord_ [("a", tyunknown_), ("b", tyunknown_)])
using eqExpr in

let nestedRec = lam ty1. lam ty2.
  bindall_ [
    nlet_ x ty1 (record_ [
      ("a", int_ 5),
      ("b", record_ [("c", float_ 2.718), ("d", float_ 3.14)]),
      ("e", float_ 1.2)
    ]),
    nlet_ y ty2 (record_ [
      ("a", record_ [("b", int_ 0), ("c", record_ [])]),
      ("d", TmVar {ident = x, ty = ty1}),
      ("e", int_ 5)
    ]),
    nlet_ z ty2 (recordupdate_ (TmVar {ident = y, ty = ty2}) "e" (int_ 4)),
    unit_
  ]
in
let xType = tyrecord_ [
  ("a", tyunknown_),
  ("b", tyrecord_ [
    ("c", tyunknown_), ("d", tyunknown_)
  ]),
  ("e", tyunknown_)
] in
let yType = tyrecord_ [
  ("a", tyrecord_ [
    ("b", tyunknown_), ("c", tyrecord_ [])
  ]),
  ("d", xType),
  ("e", tyunknown_)
] in
utest typeAnnot (nestedRec tyunknown_ tyunknown_)
with  nestedRec xType yType
using eqExpr in

let nestedTuple = lam ty.
  bind_
    (nlet_ x ty (tuple_ [int_ 0, float_ 2.5, tuple_ [int_ 0, int_ 1]]))
    unit_
in
let tupleType = tytuple_ [
  tyunknown_, tyunknown_, tytuple_ [tyunknown_, tyunknown_]
] in
utest typeAnnot (nestedTuple tyunknown_)
with  nestedTuple tupleType
using eqExpr in

let recordInLambda = lam ty.
  bindall_ [
    nulam_ n (
      bind_ (nlet_ y ty (record_ [("value", nvar_ n)])) unit_
    )
  ]
in
utest typeAnnot (recordInLambda tyunknown_)
with  recordInLambda (tyrecord_ [("value", tyunknown_)])
using eqExpr in

()
