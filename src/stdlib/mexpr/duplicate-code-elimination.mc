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
include "string.mc"
include "name.mc"
include "basic-types.mc"
include "seq.mc"
include "option.mc"
include "mexpr/pprint.mc"

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

  sem toDefinition : Name -> Info -> Definition
  sem toDefinition id =
  | info -> (info, nameGetStr id)

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

  sem lookupReplacement : DuplicateCodeEnv -> Map Name Name -> Name -> (Map Name Name, Name)
  sem lookupReplacement env replaced =
  | oldId ->
    match mapLookup oldId env.replace with Some newId then
      (mapInsert oldId newId replaced, newId)
    else (replaced, oldId)

  sem lookupDefinition : DuplicateCodeEnv -> Map Name Name -> Name -> Info
                      -> Expr -> (DuplicateCodeEnv -> (Map Name Name, Expr))
                      -> (Map Name Name, Expr)
  sem lookupDefinition env replaced id info inexpr =
  | elsfn ->
    let definition = toDefinition id info in
    -- NOTE(larshum, 2022-10-28): All definitions containing NoInfo are
    -- considered not to be equal. This prevents eliminating code generated as
    -- part of the compilation.
    match info with NoInfo _ then elsfn env else
    match mapLookup definition env.defIds with Some prevId then
      let env = {env with replace = mapInsert id prevId env.replace} in
      let replaced = mapInsert id prevId replaced in
      eliminateDuplicateCodeExpr env replaced inexpr
    else
      let env = {env with defIds = mapInsert definition id env.defIds} in
      elsfn env

  sem eliminateDuplicateCode : Expr -> Expr
  sem eliminateDuplicateCode =
  | ast ->
    match eliminateDuplicateCodeWithSummary ast with (_, ast) in
    ast

  -- Performs the elimination of duplicate code, and includes a map from old to
  -- new identifiers that were updated in the resulting AST.
  sem eliminateDuplicateCodeWithSummary : Expr -> (Map Name Name, Expr)
  sem eliminateDuplicateCodeWithSummary =
  | ast ->
    eliminateDuplicateCodeExpr (emptyDuplicateCodeEnv ()) (mapEmpty nameCmp) ast

  sem eliminateDuplicateCodeExpr : DuplicateCodeEnv -> Map Name Name -> Expr -> (Map Name Name, Expr)
  sem eliminateDuplicateCodeExpr env replaced =
  | TmVar t ->
    match lookupReplacement env replaced t.ident with (replaced, ident) in
    match eliminateDuplicateCodeType env replaced t.ty with (replaced, ty) in
    (replaced, TmVar {t with ident = ident, ty = ty})
  | TmConApp t ->
    match lookupReplacement env replaced t.ident with (replaced, ident) in
    match eliminateDuplicateCodeExpr env replaced t.body with (replaced, body) in
    match eliminateDuplicateCodeType env replaced t.ty with (replaced, ty) in
    (replaced, TmConApp {t with ident = ident, body = body, ty = ty})
  | TmDecl (x & {decl = DeclLet t}) ->
    lookupDefinition
      env replaced t.ident t.info x.inexpr
      (lam env.
        match eliminateDuplicateCodeType env replaced t.tyAnnot with (replaced, tyAnnot) in
        match eliminateDuplicateCodeType env replaced t.tyBody with (replaced, tyBody) in
        match eliminateDuplicateCodeExpr env replaced t.body with (replaced, body) in
        match eliminateDuplicateCodeExpr env replaced x.inexpr with (replaced, inexpr) in
        match eliminateDuplicateCodeType env replaced x.ty with (replaced, ty) in
        ( replaced
        , TmDecl {x with decl = DeclLet {t with body = body, tyAnnot = tyAnnot, tyBody = tyBody}, inexpr = inexpr, ty = ty} ))
  | TmDecl (x & {decl = DeclType t}) ->
    lookupDefinition
      env replaced t.ident t.info x.inexpr
      (lam env.
        match eliminateDuplicateCodeType env replaced t.tyIdent with (replaced, tyIdent) in
        match eliminateDuplicateCodeExpr env replaced x.inexpr with (replaced, inexpr) in
        match eliminateDuplicateCodeType env replaced x.ty with (replaced, ty) in
        ( replaced
        , TmDecl {x with decl = DeclType {t with tyIdent = tyIdent}, inexpr = inexpr, ty = ty} ))
  | TmDecl (x & {decl = DeclConDef t}) ->
    lookupDefinition
      env replaced t.ident t.info x.inexpr
      (lam env.
        match eliminateDuplicateCodeType env replaced t.tyIdent with (replaced, tyIdent) in
        match eliminateDuplicateCodeExpr env replaced x.inexpr with (replaced, inexpr) in
        match eliminateDuplicateCodeType env replaced x.ty with (replaced, ty) in
        ( replaced
        , TmDecl {x with decl = DeclConDef {t with tyIdent = tyIdent}, inexpr = inexpr, ty = ty} ))
  | TmDecl (x & {decl = DeclExt t}) ->
    lookupDefinition
      env replaced t.ident t.info x.inexpr
      (lam env.
        match eliminateDuplicateCodeType env replaced t.tyIdent with (replaced, tyIdent) in
        match eliminateDuplicateCodeExpr env replaced x.inexpr with (replaced, inexpr) in
        match eliminateDuplicateCodeType env replaced x.ty with (replaced, ty) in
        ( replaced
        , TmDecl {x with decl = DeclExt {t with tyIdent = tyIdent}, inexpr = inexpr, ty = ty} ))
  | TmDecl (x & {decl = DeclRecLets t}) ->
    let eliminateDuplicateBinding = lam acc. lam binding.
      match acc with (replaced, env) in
      let defn = (binding.info, nameGetStr binding.ident) in
      match binding.info with NoInfo _ then ((replaced, env), Some binding) else
      match mapLookup defn env.defIds with Some id then
        let env = {env with replace = mapInsert binding.ident id env.replace} in
        let replaced = mapInsert binding.ident id replaced in
        ((replaced, env), None ())
      else
        let env = {env with defIds = mapInsert defn binding.ident env.defIds} in
        ((replaced, env), Some binding)
    in
    let eliminateDuplicateBody = lam env. lam replaced. lam binding.
      match eliminateDuplicateCodeType env replaced binding.tyAnnot with (replaced, tyAnnot) in
      match eliminateDuplicateCodeType env replaced binding.tyBody with (replaced, tyBody) in
      match eliminateDuplicateCodeExpr env replaced binding.body with (replaced, body) in
      (replaced, {binding with body = body, tyAnnot = tyAnnot, tyBody = tyBody})
    in
    match mapAccumL eliminateDuplicateBinding (replaced, env) (reverse t.bindings)
    with ((replaced, env), optBindings) in
    let bindings = filterOption optBindings in
    match mapAccumL (eliminateDuplicateBody env) replaced bindings with (replaced, bindings) in
    match eliminateDuplicateCodeExpr env replaced x.inexpr with (replaced, inexpr) in
    match eliminateDuplicateCodeType env replaced x.ty with (replaced, ty) in
    ( replaced
    , TmDecl {x with decl = DeclRecLets {t with bindings = reverse bindings}, inexpr = inexpr, ty = ty} )
  | t & TmOpaque _ -> (replaced, t)
  | t ->
    match smapAccumL_Expr_Expr (eliminateDuplicateCodeExpr env) replaced t with (replaced, t) in
    match smapAccumL_Expr_Type (eliminateDuplicateCodeType env) replaced t with (replaced, t) in
    match smapAccumL_Expr_TypeLabel (eliminateDuplicateCodeType env) replaced t with (replaced, t) in
    match smapAccumL_Expr_Pat (eliminateDuplicateCodePat env) replaced t with (replaced, t) in
    match eliminateDuplicateCodeType env replaced (tyTm t) with (replaced, tmTy) in
    (replaced, withType tmTy t)

  sem eliminateDuplicateCodeType : DuplicateCodeEnv -> Map Name Name -> Type -> (Map Name Name, Type)
  sem eliminateDuplicateCodeType env replaced =
  | TyCon t ->
    match lookupReplacement env replaced t.ident with (replaced, ident) in
    (replaced, TyCon {t with ident = ident})
  | TyVar t ->
    match lookupReplacement env replaced t.ident with (replaced, ident) in
    (replaced, TyVar {t with ident = ident})
  | ty -> smapAccumL_Type_Type (eliminateDuplicateCodeType env) replaced ty

  sem eliminateDuplicateCodePat : DuplicateCodeEnv -> Map Name Name -> Pat -> (Map Name Name, Pat)
  sem eliminateDuplicateCodePat env replaced =
  | PatCon t ->
    match lookupReplacement env replaced t.ident with (replaced, ident) in
    match eliminateDuplicateCodePat env replaced t.subpat with (replaced, subpat) in
    match eliminateDuplicateCodeType env replaced t.ty with (replaced, ty) in
    (replaced, PatCon {t with ident = ident, subpat = subpat, ty = ty})
  | p ->
    match smapAccumL_Pat_Pat (eliminateDuplicateCodePat env) replaced p with (replaced, p) in
    match eliminateDuplicateCodeType env replaced (tyPat p) with (replaced, patTy) in
    (replaced, withTypePat patTy p)

  sem eliminateDuplicateExternalsWithSummary : Expr -> (Map Name Name, Expr)
  sem eliminateDuplicateExternalsWithSummary =| tm ->
    eliminateDuplicateExternalsExpr (mapEmpty cmpString) (mapEmpty nameCmp) tm

  sem eliminateDuplicateExternals : Expr -> Expr
  sem eliminateDuplicateExternals =| tm ->
    (eliminateDuplicateExternalsWithSummary tm).1

  sem eliminateDuplicateExternalsExpr
    : Map String Name -> Map Name Name -> Expr -> (Map Name Name, Expr)
  sem eliminateDuplicateExternalsExpr externals replaced =
  | TmDecl (x & {decl = DeclExt r}) ->
    let identStr = nameGetStr r.ident in
    optionMapOrElse
      (lam.
        let externals = mapInsert identStr r.ident externals in
        match eliminateDuplicateExternalsExpr externals replaced x.inexpr
          with (replaced, inexpr)
        in
        (replaced, TmDecl {x with inexpr = inexpr }))
      (lam ident.
        eliminateDuplicateExternalsExpr
          externals
          (mapInsert r.ident ident replaced)
          x.inexpr)
      (mapLookup identStr externals)
  | TmVar r ->
    optionMapOr (replaced, TmVar r)
      (lam ident. (replaced, TmVar { r with ident = ident }))
      (mapLookup r.ident replaced)
  | tm ->
    smapAccumL_Expr_Expr (eliminateDuplicateExternalsExpr externals) replaced tm
end

lang TestLang = MExprEliminateDuplicateCode + MExprEq + MExprSym
end

mexpr

use TestLang in
use MExprPrettyPrint in

let i = lam idx.
  Info {filename = "dummy.txt", row1 = idx, col1 = 0, row2 = idx, col2 = 0} in

recursive let exprBind = lam tm1. lam tm2.
  match tm1 with TmDecl x
  then TmDecl {x with inexpr = exprBind x.inexpr tm2}
  else tm2
in

-- Tests that it works for expressions
let fooDef =
  declWithInfo (i 0) (ulet_ "foo" (ulam_ "x" (addi_ (var_ "x") (int_ 1)))) in
let t1 = bindall_ [
  fooDef,
  ulet_ "foo" (addi_ (int_ 1) (int_ 1))] unit_ in
let t2 = bindall_ [
  fooDef]
  (app_ (var_ "foo") (int_ 3)) in
let t = exprBind (symbolize t1) (symbolize t2) in
let foo1 = nameSym "foo" in
let foo2 = nameSym "foo" in
let fooDefSym = nulet_ foo1 (ulam_ "x" (addi_ (var_ "x") (int_ 1))) in
let expected = bindall_ [
  fooDefSym,
  nulet_ foo2 (addi_ (int_ 1) (int_ 1))]
  (app_ (nvar_ foo1) (int_ 3)
) in
utest eliminateDuplicateCode t with expected using eqExpr in

-- Tests that it works for types
let optionDef = bindall_ [
  declWithInfo (i 1) (type_ "Option" ["a"] (tyvariant_ [])),
  declWithInfo (i 2) (condef_ "Some" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyapp_ (tycon_ "Option") (tyvar_ "a"))))),
  declWithInfo (i 3) (condef_ "None" (tyall_ "a" (tyarrow_ tyunit_ (tyapp_ (tycon_ "Option") (tyvar_ "a")))))] unit_ in
let fDef = bind_
  (declWithInfo (i 4)
    (ulet_ "f" (ulam_ "o"
      (match_ (var_ "o") (pcon_ "Some" (pvar_ "x"))
        (var_ "x")
        never_)))) unit_ in
let included = exprBind optionDef fDef in
let t1 = withInfo (i 5) (bind_ (ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1)))) unit_) in
let t2 = bind_
  (declWithInfo (i 6) (ulet_ "x" ((conapp_ "Some" (int_ 3)))))
  (app_ (var_ "f") (var_ "x")) in
let t = exprBind
  (symbolize (exprBind included t1))
  (symbolize (exprBind included t2)) in

let fId = nameSym "f" in
let f =
  declWithInfo (i 7)
    (nulet_ fId (ulam_ "o"
      (match_ (var_ "o") (pcon_ "Some" (pvar_ "x"))
        (var_ "x")
        never_))) in
let expected = symbolize (foldr1 exprBind [
  optionDef,
  (bind_ f unit_),
  t1,
  bind_ (ulet_ "x" ((conapp_ "Some" (int_ 3)))) unit_,
  app_ (nvar_ fId) (var_ "x")]) in
-- NOTE(larshum, 2022-09-13): Compare pretty-printed strings as expression
-- equality is not yet implemented for TmType.
utest expr2str (eliminateDuplicateCode t) with expr2str expected using eqString in

-- Tests that it applies to bindings in recursive let-expressions
let ireclets = lam bindings.
  let bindFn = lam idx. lam entry : (String, Expr).
    {ident = nameNoSym entry.0, tyAnnot = tyunknown_, tyBody = tyunknown_, body = entry.1, info = i idx} in
  TmDecl {decl = DeclRecLets { bindings = mapi bindFn bindings, info = NoInfo () }, inexpr = uunit_,
              ty = tyunknown_, info = NoInfo ()} in
let baseBindings = [
  ("a", ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ("b", ulam_ "x" (muli_ (var_ "x") (int_ 2)))
] in
let extraBinding = [
  ("c", ulam_ "x" (addi_ (app_ (var_ "a") (var_ "x")) (app_ (var_ "b") (var_ "x"))))] in
let extendedBindings = concat baseBindings extraBinding in
let t1 = exprBind
  (ireclets baseBindings)
  (bind_ (declWithInfo (i 3) (ulet_ "x" (app_ (var_ "a") (int_ 2)))) unit_) in
let t2 = exprBind
  (ireclets extendedBindings)
  (withInfo (i 4) (addi_ (app_ (var_ "b") (int_ 3)) (app_ (var_ "c") (int_ 1)))) in
let t = exprBind (symbolize t1) (symbolize t2) in
let expected = symbolize (foldr1 exprBind [
  ireclets baseBindings,
  bind_ (ulet_ "x" (app_ (var_ "a") (int_ 2))) unit_,
  ireclets extraBinding,
  addi_ (app_ (var_ "b") (int_ 3)) (app_ (var_ "c") (int_ 1))]) in

utest eliminateDuplicateCode t with expected using eqExpr in

-- Tests that it works for external identifiers
let sinExt = declWithInfo (i 0) (ext_ "sin" false (tyarrow_ tyfloat_ tyfloat_)) in
let t = bind_ sinExt (bind_ sinExt unit_) in
utest eliminateDuplicateCode t with bind_ sinExt unit_ using eqExpr in

-- Tests that it works for patterns
let t1 = bind_ (declWithInfo (i 4) (ulet_ "x" (conapp_ "Some" (int_ 2)))) unit_ in
let t2 = exprBind
  (bind_ (ulet_ "o" (conapp_ "Some" (int_ 4))) unit_)
  (match_ (var_ "o") (pcon_ "Some" (pvar_ "x"))
    (var_ "x") never_) in
let t = exprBind
  (symbolize (exprBind optionDef t1))
  (symbolize (exprBind optionDef t2)) in
let expected = symbolize (foldr1 exprBind [optionDef, t1, t2]) in

match eliminateDuplicateCodeWithSummary t with (summary, t) in
utest expr2str t with expr2str expected using eqString in
utest mapSize summary with 3 using eqi in

-- Test that it does not eliminate bindings with the same identifier string if
-- they have no info-fields.
let t = bindall_ [
  ulet_ "t" (addi_ (int_ 2) (int_ 3)),
  ulet_ "t" (addi_ (int_ 4) (var_ "t"))]
  (var_ "t") in
utest eliminateDuplicateCode t with t using eqExpr in

let t = symbolize (bindall_ [
  declWithInfo (i 0) (type_ "T1" [] tyint_),
  declWithInfo (i 0) (type_ "T1" [] tyint_),
  type_ "T2" [] (tyseq_ (tycon_ "T1"))
] unit_) in
let expected = symbolize (bindall_ [
  type_ "T1" [] tyint_,
  type_ "T2" [] (tyseq_ (tycon_ "T1"))
] unit_) in
utest expr2str (eliminateDuplicateCode t) with expr2str expected using eqString in

-- Tests that eliminateDuplicateExternalsWithSummary works.
let sinExt = declWithInfo (i 0) (ext_ "sin" false (tyarrow_ tyfloat_ tyfloat_)) in
let t = bind_ sinExt (bind_ sinExt unit_) in
match eliminateDuplicateExternalsWithSummary t with (replaced, t) in
utest mapSize replaced with 1 in
utest eliminateDuplicateCode t with bind_ sinExt unit_ using eqExpr in

()
