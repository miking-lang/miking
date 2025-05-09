include "mexpr/ast.mc"
include "mexpr/type-check.mc"
include "mexpr/pprint.mc"

include "digraph.mc"
include "error.mc"
include "map.mc"
include "name.mc"
include "set.mc"
include "tuple.mc"
include "ast.mc"

type DependencyGraph = Digraph Name ()
type TyDeps = Map Name (Set Name)
type LabelTyDeps = Map Name (Map String (Set Name))

type AccEnv = {defs : ExtRecDefs}

let _emptyAccEnv : AccEnv = {
  defs = mapEmpty nameCmp
}

lang ExtRecCollectEnv = MExprAst + ExtRecordAst + MExprPrettyPrint +
                        TypeAbsAst
  sem collectEnv : AccEnv -> Expr -> AccEnv
  sem collectEnv env =
  | TmDecl (x & {decl = DeclRecType t}) ->
    match mapLookup t.ident env.defs with Some _ then
      errorMulti
        [(t.info, nameGetStr t.ident)]
        "An extensible record type with this Name already exists!"
    else
      let defs = mapInsert t.ident (mapEmpty cmpString) env.defs in
      collectEnv {env with defs = defs} x.inexpr
  | TmDecl (x & {decl = DeclRecField t}) ->
    match t.tyIdent with TyAll tyAll then

      -- Collect other parameters to re-insert later.
      recursive let work = lam acc. lam ty.
        match ty with TyAll tyAll then
          let acc = cons (tyAll.info, tyAll.ident, tyAll.kind) acc in
          work acc tyAll.ty
        else
          (acc, ty)
      in
      match work [] tyAll.ty with (params, ty) in

      recursive let work2 = lam ty.
        match ty with TyApp {lhs = lhs} then
          work2 lhs
        else
          ty
      in

      match ty with TyArrow {from = lhs, to = rhs} then
        let lhs = work2 lhs in

        match lhs with TyCon {ident = ident} then
          match mapLookup ident env.defs with Some labelTypeMap then
            let work = lam ty. lam triple.
              TyAbs {ident = triple.1,
                     kind  = triple.2,
                     body  = ty} in

            let params = cons (NoInfo(), tyAll.ident, Mono()) params in

            let ty = foldl work rhs (reverse params) in

            -- let ty = TyAbs {ident = tyAll.ident,
            --                 kind = Mono (),
            --                 body = rhs} in
            let labelTypeMap = mapInsert t.label (nameNoSym "", ty) labelTypeMap in

            let env = {env with defs = mapInsert ident labelTypeMap env.defs} in
            collectEnv env x.inexpr
          else
            errorMulti
              [(t.info, "")]
              "The tyCon on lhs must be an extensible record type!"
        else
          errorMulti
            [(t.info, "")]
            "The type of a record field must have TyCon on lhs!"
      else
        errorMulti
          [(t.info, "")]
          (concat
            "Expected an arrow arrow type! But found: "
            (type2str t.tyIdent))
    else
      errorSingle [t.info] "The type of a record field must be quantified over a mapping!"
  | expr ->
    sfold_Expr_Expr collectEnv env expr

  sem includedRowTypes : Set Name -> Type -> Set Name
  sem includedRowTypes acc =
  | TyCon {ident = ident} -> setInsert ident acc
  | ty -> sfold_Type_Type includedRowTypes acc ty

  sem updateDependencyGraph : DependencyGraph -> Name -> [Type] -> DependencyGraph
  sem updateDependencyGraph graph name =| types ->
    let includedTypes = foldl includedRowTypes (setEmpty nameCmp) types in
    let graph = digraphMaybeAddVertex name graph in
    let addEdge = lam g. lam n.
      let g = digraphMaybeAddVertex n g in
      digraphMaybeAddEdge name n () g
    in
    setFold addEdge graph includedTypes

  sem createDependencyGraph : ExtRecDefs -> DependencyGraph
  sem createDependencyGraph =
  | env ->
    let graph = digraphEmpty nameCmp (lam. lam. true) in

    let work = lam graph. lam name. lam labelTyMap.
      updateDependencyGraph graph name (map snd (mapValues labelTyMap)) in

    mapFoldWithKey work graph env

  sem updateTyDeps : DependencyGraph -> TyDeps -> Name -> TyDeps
  sem updateTyDeps graph acc =
  | name ->
    let deps = setOfKeys (digraphBFS name graph) in
    mapInsert name deps acc

  sem computeTyDeps : DependencyGraph -> TyDeps
  sem computeTyDeps =
  | graph ->
    let vertices = digraphVertices graph in
    foldl (updateTyDeps graph) (mapEmpty nameCmp) vertices

  sem computeLabelTyDeps : TyDeps -> ExtRecDefs -> LabelTyDeps
  sem computeLabelTyDeps tydeps =
  | defs ->
    let work = lam n. lam innerMap. mapMapWithKey (lam label. lam pair.
      match pair with (ext, ty) in
      let includedNames = includedRowTypes (setEmpty nameCmp) ty in
      setFold (lam acc. lam n. setUnion acc (match mapLookup n tydeps with Some s in s)) (setEmpty nameCmp) includedNames
    ) innerMap in
    mapMapWithKey work defs

  sem dumpTyDeps : TyDeps -> String
  sem dumpTyDeps =
  | tyDeps ->
    let pairs = mapToSeq tyDeps in
    let pprintPair = lam pair.
      match pair with (name, nameSet) in
      let nameSetStr = strJoin ", " (map nameGetStr (setToSeq nameSet)) in
      join ["tydeps(", nameGetStr name, ") = ", nameSetStr]
    in
    strJoin "\n" ["=== TyDeps ===", strJoin "\n" (map pprintPair pairs), "=== END TyDeps ==="]


  sem dumpDependencyGraph : DependencyGraph -> String
  sem dumpDependencyGraph =
  | graph ->
    let edges = digraphEdges graph in
    let edgesStr = map (lam e. join [nameGetStr e.0, " -> ", nameGetStr e.1]) edges in
    strJoin "\n" (snoc (cons "=== DEPENDECY GRAPH ===" edgesStr) "=== END GRAPH ===")
end
