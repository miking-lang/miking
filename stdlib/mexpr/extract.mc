-- Performs an extraction of an MExpr AST, where the bindings corresponding to
-- a given set of identifiers are extracted from a provided AST.
--
-- The extraction assumes all bindings that are to be part of the extraction
-- are in the top-level of the program. That is, they cannot be nested in a
-- let-expression, for example. This can be achieved through lambda lifting.

include "digraph.mc"
include "name.mc"
include "set.mc"
include "mexpr/ast.mc"
include "mexpr/call-graph.mc"

lang MExprExtract = MExprAst + MExprCallGraph
  sem extractAst : Set Name -> Expr -> Expr
  sem extractAst identifiers =
  | ast -> match extractAstH identifiers ast with (_, ast) in ast

  sem extractAstH : Set Name -> Expr -> (Set Name, Expr)
  sem extractAstH used =
  | TmLet t ->
    match extractAstH used t.inexpr with (used, inexpr) in
    if setMem t.ident used then
      let used = collectIdentifiersType used t.tyBody in
      let used = collectIdentifiersExpr used t.body in
      (used, TmLet {t with inexpr = inexpr, ty = tyTm inexpr})
    else (used, inexpr)
  | TmRecLets t ->
    let bindingIdents = map (lam bind. bind.ident) t.bindings in
    recursive let dfs = lam g. lam visited. lam ident.
      if setMem ident visited then visited
      else
        let visited = setInsert ident visited in
        foldl
          (lam visited. lam ident. dfs g visited ident)
          visited (digraphSuccessors ident g) in
    let collectBindIdents = lam used. lam bind.
      let used = collectIdentifiersType used bind.tyBody in
      collectIdentifiersExpr used bind.body in
    match extractAstH used t.inexpr with (used, inexpr) in
    let g = constructCallGraph (TmRecLets t) in
    let visited = setEmpty nameCmp in
    let usedIdents =
      foldl
        (lam visited. lam ident.
          if setMem ident used then dfs g visited ident else visited)
        visited bindingIdents in
    let usedBinds =
      filter
        (lam bind. setMem bind.ident usedIdents)
        t.bindings in
    let used = foldl collectBindIdents used usedBinds in
    if null usedBinds then (used, inexpr)
    else (used, TmRecLets {t with bindings = usedBinds, inexpr = inexpr})
  | TmType t ->
    match extractAstH used t.inexpr with (used, inexpr) in
    if setMem t.ident used then (used, TmType {t with inexpr = inexpr})
    else (used, inexpr)
  | TmConDef t ->
    let constructorIsUsed = lam used.
      match t.tyIdent with TyArrow {to = TyCon {ident = varTyId}} then
        or (setMem t.ident used) (setMem varTyId used)
      else setMem t.ident used in
    match extractAstH used t.inexpr with (used, inexpr) in
    if constructorIsUsed used then (used, TmConDef {t with inexpr = inexpr})
    else (used, inexpr)
  | TmUtest t -> extractAstH used t.next
  | TmExt t ->
    match extractAstH used t.inexpr with (used, inexpr) in
    if setMem t.ident used then (used, TmExt {t with inexpr = inexpr})
    else (used, inexpr)
  | t ->
    -- NOTE(larshum, 2022-09-06): In the base case, we return the integer
    -- literal 0, rather than an empty record, as the former works better in
    -- our C compiler.
    (used, TmConst {val = CInt {val = 0}, ty = TyInt {info = infoTm t},
                    info = infoTm t})

  sem collectIdentifiersExpr : Set Name -> Expr -> Set Name
  sem collectIdentifiersExpr used =
  | ast -> collectIdentifiersExprH (setEmpty nameCmp) used ast

  sem collectIdentifiersExprH : Set Name -> Set Name -> Expr -> Set Name
  sem collectIdentifiersExprH bound used =
  | TmVar t ->
    if setMem t.ident bound then used else setInsert t.ident used
  | TmLam t ->
    let bound = setInsert t.ident bound in
    collectIdentifiersExprH bound used t.body
  | TmMatch t ->
    let used = collectIdentifiersExprH bound used t.target in
    match collectIdentifiersPat (bound, used) t.pat with (bound, used) in
    let used = collectIdentifiersExprH bound used t.thn in
    collectIdentifiersExprH bound used t.els
  | TmConApp t ->
    if setMem t.ident bound then used else setInsert t.ident used
  | ast -> sfold_Expr_Expr (collectIdentifiersExprH bound) used ast

  sem collectIdentifiersType : Set Name -> Type -> Set Name
  sem collectIdentifiersType used =
  | TyCon t -> setInsert t.ident used
  | ty -> sfold_Type_Type collectIdentifiersType used ty

  sem collectIdentifiersPat : (Set Name, Set Name) -> Pat -> (Set Name, Set Name)
  sem collectIdentifiersPat boundUsed =
  | PatNamed t ->
    match boundUsed with (bound, used) in
    (bound, _collectPatNamed bound used t.ident)
  | PatSeqEdge t ->
    match foldl collectIdentifiersPat boundUsed t.prefix with (bound, used) in
    let used = _collectPatNamed bound used t.middle in
    foldl collectIdentifiersPat (bound, used) t.postfix
  | PatCon t ->
    match boundUsed with (bound, used) in
    let used = if setMem t.ident bound then used else setInsert t.ident used in
    collectIdentifiersPat (bound, used) t.subpat
  | pat -> sfold_Pat_Pat collectIdentifiersPat boundUsed pat

  sem _collectPatNamed : Set Name -> Set Name -> PatName -> Set Name
  sem _collectPatNamed bound used =
  | PName id -> if setMem id bound then used else setInsert id used
  | PWildcard _ -> used
end
