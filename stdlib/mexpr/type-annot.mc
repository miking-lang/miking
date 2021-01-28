include "mexpr/ast.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"

type TypeEnv = AssocMap Name Type

let _tyEnvInsert = assocInsert {eq = nameEqSym}
let _tyEnvLookup = assocLookup {eq = nameEqSym}

lang TypeAnnot = UnknownTypeAst
  sem typeExpr (env : TypeEnv) =
  | t -> TyUnknown {}

  sem typeAnnotExpr (env : TypeEnv) =

  sem typeAnnot =
  | expr -> typeAnnotExpr assocEmpty expr
end

lang VarTypeAnnot = TypeAnnot + VarAst
  sem typeExpr (env : TypeEnv) =
  | TmVar t ->
    match _tyEnvLookup t.ident env with Some ty then
      ty
    else
      TyUnknown {}
end

lang FunTypeAnnot = TypeAnnot + FunAst
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
    let sortBindingsByKey = lam bindings.
      let cmpKey = lam l. lam r.
        match ltString l.0 r.0 with true then (negi 1) else
        match gtString l.0 r.0 with true then 1 else 0
      in
      let traits = {eq=eqString} in
      seq2assoc traits (sort cmpKey (assoc2seq traits bindings))
    in
    let bindings = sortBindingsByKey t.bindings in
    TyRecord {fields = assocFold {eq=eqString} f assocEmpty bindings}
end

lang LetTypeAnnot = TypeAnnot + LetAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmLet t ->
    let ty =
      match t.ty with TyUnknown {} then
        typeExpr env t.body
      else t.ty
    in
    let env2 = _tyEnvInsert t.ident ty env in
    TmLet {{{t with ty = ty}
               with body = typeAnnotExpr env t.body}
               with inexpr = typeAnnotExpr env2 t.inexpr}
end

lang MExprTypeAnnot = VarTypeAnnot + FunTypeAnnot + RecordTypeAnnot + LetTypeAnnot
  sem typeAnnotExpr (env : TypeEnv) =
  | t -> smap_Expr_Expr (typeAnnotExpr env) t
end

lang TestLang = MExprTypeAnnot + MExprPrettyPrint

mexpr

use TestLang in

let x = nameSym "x" in
let y = nameSym "y" in
let z = nameSym "z" in
let n = nameSym "n" in

let base = nulam_ x (nulam_ y (app_ (nvar_ x) (var_ y))) in
utest typeAnnot base with base in

let letexp = lam ty.
  bind_
    (nlet_ x ty (record_ [
      ("a", int_ 5),
      ("b", float_ 2.718)
    ]))
    (nvar_ x) in
utest typeAnnot (letexp tyunknown_)
with  letexp (tyrecord_ [("a", tyunknown_), ("b", tyunknown_)]) in

let nestedRec = lam ty1. lam ty2.
  bindall_ [
    nlet_ x ty1 (record_ [
      ("a", int_ 5),
      ("b", record_ [("c", float_ 2.718), ("d", float_ 3.14)]),
      ("e", float_ 1.2)
    ]),
    nlet_ y ty2 (record_ [
      ("a", record_ [("b", int_ 0), ("c", int_ 1), ("d", record_ [])]),
      ("e", nvar_ x)
    ]),
    nlet_ z ty2 (nvar_ y),
    nvar_ z
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
    ("b", tyunknown_), ("c", tyunknown_), ("d", tyrecord_ [])
  ]),
  ("e", xType)
] in
utest typeAnnot (nestedRec tyunknown_ tyunknown_)
with  nestedRec xType yType in

let nestedTuple = lam ty.
  bind_
    (nlet_ x ty (tuple_ [int_ 0, float_ 2.5, tuple_ [int_ 0, int_ 1]]))
    (nvar_ x)
in
let tupleType = tytuple_ [
  tyunknown_, tyunknown_, tytuple_ [tyunknown_, tyunknown_]
] in
utest typeAnnot (nestedTuple tyunknown_)
with  nestedTuple tupleType in

let recordInLambda = lam ty.
  bindall_ [
    nulet_ x (
      nulam_ n (
        bind_ (nlet_ y ty (record_ [("value", nvar_ n)])) (nvar_ y)
    )),
    app_ (nvar_ x) (int_ 5)
  ]
in
utest typeAnnot (recordInLambda tyunknown_)
with  recordInLambda (tyrecord_ [("value", tyunknown_)]) in

()
