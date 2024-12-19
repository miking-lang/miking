include "ast.mc"
include "collect-env.mc"

include "mlang/ast.mc"

include "digraph.mc"
include "error.mc"
include "map.mc"
include "name.mc"
include "set.mc"
include "tuple.mc"
include "ast.mc"

type GlobalExtInfo = use MLangAst in {
  ty : Type,
  excludedCons : Set Name
}

type MLangTyDepsEnv = {
  depGraph : DependencyGraph,
  extensibleTypes : Set Name,
  globalExtMap : Map Name [GlobalExtInfo],
  baseMap : Map Name Name
}



lang ComputeMLangTyDeps = MLangAst + MExprAst + ExtRecAst
  sem _collectNames : MLangTyDepsEnv -> Decl -> MLangTyDepsEnv
  sem _collectNames env =
  | _ -> env
  | DeclLang d ->
    foldl _collectNames env d.decls
  | DeclSyn d ->
    let env = if null d.includes
              then {env with extensibleTypes = setInsert d.ident env.extensibleTypes}
              else env in

    let typeIdents = map (lam def. def.tyName) d.defs in

    {env with extensibleTypes = foldr setInsert env.extensibleTypes typeIdents}
  | DeclCosyn d ->
    if d.isBase then
      {env with extensibleTypes = setInsert d.ident env.extensibleTypes}
    else
      env
  | SynDeclProdExt d ->
    match d.globalExt with Some globalExt then
      match mapLookup d.ident env.baseMap with Some baseIdent in

      let excludedCons = setOfSeq nameCmp (map (lam e. e.ident) d.individualExts) in

      let oldList = mapLookupOr [] baseIdent env.globalExtMap in
      let newList = cons {ty = globalExt, excludedCons = excludedCons} oldList in

      {env with globalExtMap = mapInsert baseIdent newList env.globalExtMap}
    else
      env

  sem _gatherDeps : MLangTyDepsEnv -> Set Name -> Type -> Set Name
  sem _gatherDeps env acc =
  | TyCon t ->
    if setMem t.ident env.extensibleTypes then
      setInsert t.ident acc
    else
      acc
  | ty ->
    sfold_Type_Type (_gatherDeps env) acc ty

  sem _handleDef : MLangTyDepsEnv -> [Type] -> {ident : Name, tyIdent : Type, tyName : Name} -> MLangTyDepsEnv
  sem _handleDef env exts =
  | {ident = ident, tyIdent = tyIdent, tyName = tyName} ->
    let mergeTy = lam l. lam r.
      match l with TyRecord leftRec in
      match r with TyRecord rightRec in
      TyRecord {leftRec with fields = mapUnion leftRec.fields rightRec.fields}
    in
    let ty = foldl mergeTy tyIdent exts in

    let deps = _gatherDeps env (setEmpty nameCmp) ty in

    {env with depGraph = setFold (lam g. lam dep. digraphMaybeAddEdge tyName dep () g) env.depGraph deps}

  sem _establishDepGraph : MLangTyDepsEnv -> Decl -> MLangTyDepsEnv
  sem _establishDepGraph env =
  | DeclLang d ->
    foldl _establishDepGraph env d.decls
  | DeclCosyn d ->
    let ident = d.ident in
    let deps = _gatherDeps env (setEmpty nameCmp) d.ty in
    {env with depGraph = setFold (lam g. lam dep. digraphMaybeAddEdge ident dep () g) env.depGraph deps}
  | DeclSyn d ->
    match mapLookup d.ident env.baseMap with Some baseIdent in

    let typeIdents = map (lam def. def.tyName) d.defs in

    let work = lam g. lam tyIdent. digraphMaybeAddEdge baseIdent tyIdent () g in
    let env = {env with depGraph = foldl work env.depGraph typeIdents} in

    let exts = match mapLookup baseIdent env.globalExtMap with Some extensions
      then extensions
      else []
    in

    let def2ext = lam d.
      mapOption (lam ext. if not (setMem d.ident ext.excludedCons) then Some (d.tyIdent) else None ()) exts
    in

    foldl (lam env. lam d. _handleDef env (def2ext d) d) env d.defs
  | SynDeclProdExt d ->
    foldl (lam env. lam d. _handleDef env [] d) env d.individualExts
  | _ -> env

  sem _updateTyDeps : DependencyGraph -> TyDeps -> Name -> TyDeps
  sem _updateTyDeps graph acc =
  | name ->
    let deps = setOfKeys (digraphBFS name graph) in
    mapInsert name deps acc

  sem _computeTyDeps : DependencyGraph -> TyDeps
  sem _computeTyDeps =
  | graph ->
    let vertices = digraphVertices graph in
    foldl (_updateTyDeps graph) (mapEmpty nameCmp) vertices

  sem getProgTyDeps : Map Name Name -> MLangProgram -> TyDeps
  sem getProgTyDeps baseMap =
  | {decls = decls} ->
    let env = {baseMap = baseMap,
               extensibleTypes = setEmpty nameCmp,
               globalExtMap = mapEmpty nameCmp,
               depGraph = digraphEmpty nameCmp (lam. lam. true)} in

    let env = foldl _collectNames env decls in

    let env = {env with depGraph = digraphAddVertices (setToSeq env.extensibleTypes) env.depGraph} in

    let env = foldl _establishDepGraph env decls in

    _computeTyDeps env.depGraph
end