include "mlang/ast.mc"
include "mlang/pprint.mc"

include "map.mc"
include "name.mc"
include "digraph.mc"
include "set.mc"

include "ast.mc"
include "pprint.mc"

type ResolveStaticEnv = {
  tydeps : Map Name (Set Name),
  baseMap : Map Name Name
}
type ResolveLangEnv = {
  prodFields : Map Name (Set Name),
  sumFields : Map Name (Set Name)
}
type ResolveQualifiedNameEnv = {
  langEnvs : Map Name ResolveLangEnv
}

-- TODO(voorberg, 03/09/2024): Maybe it would be better to get rid of qualified
-- names during type checking. As we can then just generate metavar with the
-- correct kind instead of having to introduce forall terms which may
-- not be legal in all places.
lang ResolveQualifiedName = MLangAst + RecordTypeAst + QualifiedTypeAst +
                            MLangPrettyPrint + ExtRecAst

  sem resolveQualifiedNameProgram tydeps baseMap =
  | prog ->
    let staticEnv = {tydeps = tydeps, baseMap = baseMap} in
    let accEnv = {langEnvs = mapEmpty nameCmp} in

    match smap_Prog_Decl (resolveQualifiedNames staticEnv) accEnv prog
    with (accEnv, prog) in

    let resolver = resolveTy staticEnv accEnv in
    recursive let worker = lam expr.
      let expr = smap_Expr_Type resolver expr in
      smap_Expr_Expr worker expr
    in

    {prog with expr = worker prog.expr}

  sem gatherLangEnvs tydeps baseMap=
  | prog ->
    let staticEnv = {tydeps = tydeps, baseMap = baseMap} in
    let accEnv = {langEnvs = mapEmpty nameCmp} in

    match smap_Prog_Decl (resolveQualifiedNames staticEnv) accEnv prog
    with (accEnv, prog) in

    accEnv.langEnvs

  sem resolveQualifiedNames : ResolveStaticEnv ->
                              ResolveQualifiedNameEnv ->
                              Decl ->
                              (ResolveQualifiedNameEnv, Decl)
  sem resolveQualifiedNames staticEnv accEnv =
  | DeclLang d & decl ->
    let emptyLangEnv : ResolveLangEnv = {prodFields = mapEmpty nameCmp,
                                         sumFields = mapEmpty nameCmp} in

    let includedLangEnvs : [ResolveLangEnv] = map
      (lam n. match mapLookup n accEnv.langEnvs with Some env in env)
      d.includes in

    let f = lam lhs. lam rhs.
      let lhs = optionGetOrElse (lam. mapEmpty nameCmp) lhs in
      let rhs = optionGetOrElse (lam. mapEmpty nameCmp) rhs in
      Some (mapUnion lhs rhs) in

    let merger : ResolveLangEnv -> ResolveLangEnv -> ResolveLangEnv = lam lhs. lam rhs.
      {sumFields = mapMerge f lhs.sumFields rhs.sumFields,
       prodFields = mapMerge f lhs.prodFields rhs.prodFields} in

    let newLangEnv : ResolveLangEnv = foldl merger emptyLangEnv includedLangEnvs in

    let accEnv : ResolveQualifiedNameEnv = {accEnv with langEnvs = mapInsert d.ident newLangEnv accEnv.langEnvs} in

    match smapAccumL_Decl_Decl (resolveQualifiedNamesWithinLang d.ident staticEnv) accEnv decl with
    (accEnv, decl) in

    match decl with DeclLang d in

    (accEnv, DeclLang {d with decls = d.decls})
  | other ->
    let worker = resolveTy staticEnv accEnv in
    let other = smap_Decl_Type worker other in
    let other = smap_Decl_Expr (lam e. smap_Expr_Type worker e) other in
    (accEnv, other)

  sem _updateProdFields langIdent accEnv =
  | {ident = ident, tyIdent = TyRecord r, tyName = tyName} ->
    match mapLookup langIdent accEnv.langEnvs with Some innerEnv in

    let ident = tyName in

    let labels : [SID] = mapKeys r.fields in
    let labels : [Name] = map (lam sid. nameNoSym (sidToString sid)) labels in

    let oldSet = mapLookupOr (mapEmpty nameCmp) tyName innerEnv.prodFields in
    let newSet = foldr setInsert oldSet labels in
    let innerEnv = {innerEnv with prodFields = mapInsert tyName newSet innerEnv.prodFields} in

    {accEnv with langEnvs = mapInsert langIdent innerEnv accEnv.langEnvs}
  | other ->
    errorSingle [infoTy other.tyIdent] (join [
      " * Expected a record as a constructor payload but got: \n",
      type2str (other.tyIdent)
    ])

  sem resolveQualifiedNamesWithinLang langIdent staticEnv accEnv =
  | DeclCosyn d & decl ->
    let ident = d.ident in

    match d.ty with TyRecord r in
    match mapLookup langIdent accEnv.langEnvs with Some innerEnv in

    let labels : [SID] = mapKeys r.fields in
    let labels : [Name] = map (lam sid. nameNoSym (sidToString sid)) labels in

    let oldSet = mapLookupOr
      (mapEmpty nameCmp)
      ident
      innerEnv.prodFields in
    let newSet = foldr setInsert oldSet labels in
    let innerEnv = {innerEnv with prodFields = mapInsert ident newSet innerEnv.prodFields} in

    let accEnv = {accEnv with langEnvs = mapInsert langIdent innerEnv accEnv.langEnvs} in
    (accEnv, decl)
  | DeclSyn d & decl ->
    match mapLookup langIdent accEnv.langEnvs with Some innerEnv in

    match mapLookup d.ident staticEnv.baseMap with Some baseIdent in

    let s = mapLookupOr (setEmpty nameCmp) baseIdent innerEnv.sumFields in
    let addedConstructors = map (lam d. d.ident) d.defs in
    let newS = foldr setInsert s addedConstructors in

    let innerEnv = {innerEnv with sumFields = mapInsert baseIdent newS innerEnv.sumFields} in
    let accEnv = {accEnv with langEnvs = mapInsert langIdent innerEnv accEnv.langEnvs} in

    let accEnv = foldl (_updateProdFields langIdent) accEnv d.defs in

    let decl = smap_Decl_Type (resolveTy staticEnv accEnv) decl in
    (accEnv, decl)
  | SynDeclProdExt d & decl ->
    let accEnv = foldl (_updateProdFields langIdent) accEnv d.individualExts in
    let decl = smap_Decl_Type (resolveTy staticEnv accEnv) decl in
    (accEnv, decl)
  | decl ->
    let decl = smap_Decl_Type (resolveTy staticEnv accEnv) decl in
    (accEnv, decl)

  sem resolveTy : ResolveStaticEnv -> ResolveQualifiedNameEnv -> Type -> Type
  sem resolveTy staticEnv accEnv =
  | ty ->
    match resolveTyHelper staticEnv accEnv [] ty with (acc, ty) in

    let worker = lam tyAcc. lam pair.
      match pair with (ident, kind) in
      nstyall_ ident kind tyAcc
    in
    foldl worker ty acc

  sem _identToBound env info =
  | ident ->
    match mapLookup ident env.prodFields with Some fields then
      Some {lower = fields, upper = None ()}
    else match mapLookup ident env.sumFields with Some fields then
      Some {lower = setEmpty nameCmp, upper = Some fields}
    else
      None ()

  sem _negate =
  | kindMap ->
    let f = lam bounds.
      let newUpper = (if setIsEmpty bounds.lower
                      then None ()
                      else Some bounds.lower) in
      match bounds.upper with Some newLower then
        {lower = newLower, upper = newUpper}
      else
        {lower = setEmpty nameCmp, upper = newUpper}
    in
    mapMap f kindMap

  sem resolveTyHelper : ResolveStaticEnv -> ResolveQualifiedNameEnv -> [(Name, Kind)] -> Type -> ([(Name, Kind)], Type)
  sem resolveTyHelper staticEnv accEnv acc =
  | TyQualifiedName t & ty ->
    let ident = t.rhs in
    let tydeps = match mapLookup ident staticEnv.tydeps with Some tydeps then tydeps
                 else errorSingle [t.info] (join [
                   " * Unknown right-hand side '",
                   nameGetStr t.rhs,
                   "' of qualified type!"
                 ]) in

    let env = mapLookupOrElse
      (lam. errorSingle [t.info] "* Langauge on left-hand side does not exist!")
      t.lhs
      accEnv.langEnvs
    in

    -- Update the environment based on the plus and minus sets.
    -- Note that we do this by updating the environment in place.
    -- This is only possible because we do not pass the environment into
    -- any recursive calls.
    let updateEnv = lam updater. lam env. lam pair.
      match pair with (tyIdent, conIdent) in
      match mapLookup tyIdent env.prodFields with Some fields then
        {env with prodFields = mapInsert tyIdent (updater conIdent fields) env.prodFields}
      else match mapLookup tyIdent env.sumFields with Some fields then
        {env with sumFields = mapInsert tyIdent (updater conIdent fields) env.sumFields}
      else
        env
    in
    let env = foldl (updateEnv setInsert) env t.plus in
    let env = foldl (updateEnv setRemove) env t.minus in

    let folder = lam acc. lam dep.
      let dep = mapLookupOr dep dep staticEnv.baseMap in
      match _identToBound env t.info dep with Some bound
      then mapInsert dep bound acc
      else acc
    in
    let kindMap = setFold folder (mapEmpty nameCmp) tydeps in

    let kindMap = if t.pos then kindMap else _negate kindMap in
    let kind = Data {types = kindMap} in

    let tyvarIdent = nameSym "ss" in
    let tyvar = TyVar {info = t.info, ident = tyvarIdent} in

    let ident = mapLookupOr ident ident staticEnv.baseMap in

    let newTy = match mapLookup ident env.prodFields with Some _ then
                  TyCon {ident = ident, info = t.info, data = tyvar}
                else match mapLookup ident env.sumFields with Some _ then
                  TyCon {ident = ident, info = t.info, data = tyvar}
                else errorSingle [t.info] (join [
                  " * Illegal state! The right-hand side '",
                  nameGetStr ident,
                  "' (",
                  if nameHasSym ident then "symbolized" else "not symbolized",
                  ") of this qualified name\n",
                  " * is neither a sum or product type. This should be impossible!"
                ])
    in


    -- TODO(11/10/2024, voorberg): There is a bug when we introduce syntactic
    -- sugar over cosyns relating to monomorphisation of the TyAlias.
    match mapLookup ident env.prodFields with Some _ then
      (cons (tyvarIdent, kind) acc, newTy)
    else
      (cons (tyvarIdent, kind) acc, TyAlias {display = ty, content = newTy})
  | ty ->
    smapAccumL_Type_Type (resolveTyHelper staticEnv accEnv) acc ty
end