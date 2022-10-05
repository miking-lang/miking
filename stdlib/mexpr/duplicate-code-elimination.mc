-- Language fragment which performs elimination of duplicated code, used when
-- merging ASTs with shared code. The first instance of a definition is kept,
-- while later re-definitions are considered duplicates. In addition,
-- references to re-definitions are updated to instead refer to the first
-- instance of that definition, ignoring shadowing.

include "common.mc"
include "map.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eq.mc"
include "mexpr/info.mc"
include "mexpr/symbolize.mc"

lang MExprEliminateDuplicateCode = MExprAst
  -- NOTE(larshum, 2022-09-13): For now, we need to consider both the info
  -- field AND the string of an identifier. This is because the MLang
  -- transformation may result in the same info field for multiple semantic
  -- functions. In the future, it may be sufficient to only look at the info
  -- field.
  type Definition = (Info, String)

  sem cmpDefinition : Definition -> Definition -> Int
  sem cmpDefinition lhs =
  | rhs ->
    let i = infoCmp lhs.0 rhs.0 in
    if eqi i 0 then cmpString lhs.1 rhs.1
    else i

  type DuplicateCodeEnv = {
    -- Maps the representation of a definition (as defined above) to an
    -- identifier.
    defIds : Map Definition Name,

    -- Maps the identifier of a duplicated definition to the identifier of the
    -- first instance of that definition in the current scope.
    replace : Map Name Name
  }

  sem emptyDuplicateCodeEnv : () -> DuplicateCodeEnv
  sem emptyDuplicateCodeEnv =
  | () -> {defIds = mapEmpty cmpDefinition, replace = mapEmpty nameCmp}

  sem lookupReplacement : DuplicateCodeEnv -> Name -> Name
  sem lookupReplacement env =
  | oldId ->
    match mapLookup oldId env.replace with Some newId then newId
    else oldId

  sem lookupDefinition : DuplicateCodeEnv -> Name -> Info -> Expr
                      -> (DuplicateCodeEnv -> Expr) -> Expr
  sem lookupDefinition env definitionId definitionInfo inexpr =
  | elsfn ->
    let definition = (definitionInfo, nameGetStr definitionId) in
    match mapLookup definition env.defIds with Some prevId then
      let env = {env with replace = mapInsert definitionId prevId env.replace} in
      eliminateDuplicateCodeExpr env inexpr
    else
      let env = {env with defIds = mapInsert definition definitionId env.defIds} in
      elsfn env

  sem eliminateDuplicateCode : Expr -> Expr
  sem eliminateDuplicateCode =
  | expr -> eliminateDuplicateCodeExpr (emptyDuplicateCodeEnv ()) expr

  sem eliminateDuplicateCodeExpr : DuplicateCodeEnv -> Expr -> Expr
  sem eliminateDuplicateCodeExpr env =
  | TmVar t ->
    TmVar {t with ident = lookupReplacement env t.ident}
  | TmConApp t ->
    TmConApp {t with ident = lookupReplacement env t.ident}
  | TmLet t ->
    lookupDefinition
      env t.ident t.info t.inexpr
      (lam env.
        let inexpr = eliminateDuplicateCodeExpr env t.inexpr in
        TmLet {t with body = eliminateDuplicateCodeExpr env t.body,
                      tyBody = eliminateDuplicateCodeType env t.tyBody,
                      inexpr = inexpr, ty = tyTm inexpr})
  | TmType t ->
    lookupDefinition
      env t.ident t.info t.inexpr
      (lam env.
        let inexpr = eliminateDuplicateCodeExpr env t.inexpr in
        TmType {t with tyIdent = eliminateDuplicateCodeType env t.tyIdent,
                       inexpr = inexpr, ty = tyTm inexpr})
  | TmConDef t ->
    lookupDefinition
      env t.ident t.info t.inexpr
      (lam env.
        let inexpr = eliminateDuplicateCodeExpr env t.inexpr in
        TmConDef {t with tyIdent = eliminateDuplicateCodeType env t.tyIdent,
                         inexpr = inexpr, ty = tyTm inexpr})
  | TmExt t ->
    lookupDefinition
      env t.ident t.info t.inexpr
      (lam env.
        let inexpr = eliminateDuplicateCodeExpr env t.inexpr in
        TmExt {t with tyIdent = eliminateDuplicateCodeType env t.tyIdent,
                      inexpr = inexpr, ty = tyTm inexpr})
  | TmRecLets t ->
    let eliminateDuplicateBinding = lam env. lam binding.
      let defn = (binding.info, nameGetStr binding.ident) in
      match mapLookup defn env.defIds with Some id then
        let env = {env with replace = mapInsert binding.ident id env.replace} in
        (env, None ())
      else
        let env = {env with defIds = mapInsert defn binding.ident env.defIds} in
        (env, Some binding)
    in
    let eliminateDuplicateBody = lam env. lam binding.
      {binding with body = eliminateDuplicateCodeExpr env binding.body,
                    tyBody = eliminateDuplicateCodeType env binding.tyBody}
    in
    match mapAccumL eliminateDuplicateBinding env (reverse t.bindings)
    with (env, optBindings) in
    let bindings =
      map
        (eliminateDuplicateBody env)
        (mapOption identity optBindings) in
    let inexpr = eliminateDuplicateCodeExpr env t.inexpr in
    TmRecLets {t with bindings = reverse bindings,
                      inexpr = inexpr, ty = tyTm inexpr}
  | t ->
    let t = smap_Expr_Expr (eliminateDuplicateCodeExpr env) t in
    let t = smap_Expr_Type (eliminateDuplicateCodeType env) t in
    let t = smap_Expr_Pat (eliminateDuplicateCodePat env) t in
    withType (eliminateDuplicateCodeType env (tyTm t)) t

  sem eliminateDuplicateCodeType : DuplicateCodeEnv -> Type -> Type
  sem eliminateDuplicateCodeType env =
  | TyCon t ->
    match mapLookup t.ident env.replace with Some newId then
      TyCon {t with ident = newId}
    else TyCon t
  | TyVar t ->
    match mapLookup t.ident env.replace with Some newId then
      TyVar {t with ident = newId}
    else TyVar t
  | ty -> smap_Type_Type (eliminateDuplicateCodeType env) ty

  sem eliminateDuplicateCodePat : DuplicateCodeEnv -> Pat -> Pat
  sem eliminateDuplicateCodePat env =
  | PatCon t ->
    PatCon {t with ident = lookupReplacement env t.ident,
                   subpat = eliminateDuplicateCodePat env t.subpat}
  | p ->
    let p = smap_Pat_Pat (eliminateDuplicateCodePat env) p in
    withTypePat (eliminateDuplicateCodeType env (tyPat p)) p
end

lang TestLang = MExprEliminateDuplicateCode + MExprEq + MExprSym
end

mexpr

use TestLang in
use MExprPrettyPrint in

let i = lam idx.
  Info {filename = "dummy.txt", row1 = idx, col1 = 0, row2 = idx, col2 = 0} in

-- Tests that it works for expressions
let fooDef = 
  withInfo (i 0) (ulet_ "foo" (ulam_ "x" (addi_ (var_ "x") (int_ 1)))) in
let t1 = bindall_ [
  fooDef,
  ulet_ "foo" (addi_ (int_ 1) (int_ 1))] in
let t2 = bindall_ [
  fooDef,
  app_ (var_ "foo") (int_ 3)] in
let t = bind_ (symbolize t1) (symbolize t2) in
let foo1 = nameSym "foo" in
let foo2 = nameSym "foo" in
let fooDefSym = nulet_ foo1 (ulam_ "x" (addi_ (var_ "x") (int_ 1))) in
let expected = bindall_ [
  fooDefSym,
  nulet_ foo2 (addi_ (int_ 1) (int_ 1)),
  app_ (nvar_ foo1) (int_ 3)
] in
utest eliminateDuplicateCode t with expected using eqExpr in

-- Tests that it works for types
let optionDef = bindall_ [
  withInfo (i 1) (type_ "Option" tyunknown_),
  withInfo (i 2) (condef_ "Some" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyapp_ (tycon_ "Option") (tyvar_ "a"))))),
  withInfo (i 3) (condef_ "None" (tyall_ "a" (tyarrow_ tyunit_ (tyapp_ (tycon_ "Option") (tyvar_ "a")))))] in
let fDef =
  withInfo (i 4)
    (ulet_ "f" (ulam_ "o"
      (match_ (var_ "o") (pcon_ "Some" (pvar_ "x"))
        (var_ "x")
        never_))) in
let included = bind_ optionDef fDef in
let t1 = withInfo (i 5) (ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1)))) in
let t2 = bind_
  (withInfo (i 6) (ulet_ "x" ((conapp_ "Some" (int_ 3)))))
  (app_ (var_ "f") (var_ "x")) in
let t = bind_
  (symbolize (bind_ included t1))
  (symbolize (bind_ included t2)) in

let fId = nameSym "f" in
let f =
  withInfo (i 7)
    (nulet_ fId (ulam_ "o"
      (match_ (var_ "o") (pcon_ "Some" (pvar_ "x"))
        (var_ "x")
        never_))) in
let expected = symbolize (bindall_ [
  optionDef,
  f,
  t1,
  ulet_ "x" ((conapp_ "Some" (int_ 3))),
  app_ (nvar_ fId) (var_ "x")]) in
-- NOTE(larshum, 2022-09-13): Compare pretty-printed strings as expression
-- equality is not yet implemented for TmType.
utest expr2str (eliminateDuplicateCode t) with expr2str expected using eqString in

-- Tests that it applies to bindings in recursive let-expressions
let ireclets = lam bindings.
  let bindFn = lam idx. lam entry : (String, Expr).
    {ident = nameNoSym entry.0, tyBody = tyunknown_, body = entry.1, info = i idx} in
  TmRecLets { bindings = mapi bindFn bindings, inexpr = uunit_,
              ty = tyunknown_, info = NoInfo () } in
let baseBindings = [
  ("a", ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ("b", ulam_ "x" (muli_ (var_ "x") (int_ 2)))
] in
let extraBinding = [
  ("c", ulam_ "x" (addi_ (app_ (var_ "a") (var_ "x")) (app_ (var_ "b") (var_ "x"))))] in
let extendedBindings = concat baseBindings extraBinding in
let t1 = bind_
  (ireclets baseBindings)
  (withInfo (i 3) (ulet_ "x" (app_ (var_ "a") (int_ 2)))) in
let t2 = bind_
  (ireclets extendedBindings)
  (withInfo (i 4) (addi_ (app_ (var_ "b") (int_ 3)) (app_ (var_ "c") (int_ 1)))) in
let t = bind_ (symbolize t1) (symbolize t2) in
let expected = symbolize (bindall_ [
  ireclets baseBindings,
  ulet_ "x" (app_ (var_ "a") (int_ 2)),
  ireclets extraBinding,
  addi_ (app_ (var_ "b") (int_ 3)) (app_ (var_ "c") (int_ 1))]) in

utest eliminateDuplicateCode t with expected using eqExpr in

-- Tests that it works for external identifiers
let sinExt = withInfo (i 0) (ext_ "sin" false (tyarrow_ tyfloat_ tyfloat_)) in
let t = bind_ sinExt sinExt in
utest eliminateDuplicateCode t with sinExt using eqExpr in

-- Tests that it works for patterns
let t1 = withInfo (i 4) (ulet_ "x" (conapp_ "Some" (int_ 2))) in
let t2 = bind_
  (ulet_ "o" (conapp_ "Some" (int_ 4)))
  (match_ (var_ "o") (pcon_ "Some" (pvar_ "x"))
    (var_ "x") never_) in
let t = bind_
  (symbolize (bind_ optionDef t1))
  (symbolize (bind_ optionDef t2)) in
let expected = symbolize (bindall_ [optionDef, t1, t2]) in

utest expr2str (eliminateDuplicateCode t) with expr2str expected using eqString in

()
