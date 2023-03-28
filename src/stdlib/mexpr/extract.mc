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
include "mexpr/type-check.mc"

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
    let used = collectIdentifiersType used t.tyIdent in
    if constructorIsUsed used then (used, TmConDef {t with inexpr = inexpr})
    else (used, inexpr)
  | TmUtest t -> extractAstH used t.next
  | TmExt t ->
    let used = collectIdentifiersType used t.tyIdent in
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
    let used =
      if setMem t.ident bound then used else setInsert t.ident used
    in
    collectIdentifiersExprH bound used t.body
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

lang TestLang =
  MExprExtract + MExprEq + MExprSym + MExprTypeCheck + MExprPrettyPrint
end

mexpr

use TestLang in

let preprocess = lam t. typeCheck (symbolize t) in
let setOfSeq = lam ids. setOfSeq nameCmp ids in

let f = nameSym "f" in
let g = nameSym "g" in
let h = nameSym "h" in
let tmp = nameSym "tmp" in
let t = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ g (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  nulet_ h (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  nulet_ tmp (app_ (nvar_ h) (int_ 2)),
  nvar_ tmp
]) in
let extractF = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  int_ 0
]) in
utest extractAst (setOfSeq [f]) t with extractF using eqExpr in

let extractG = preprocess (bindall_ [
  nulet_ g (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  int_ 0
]) in
utest extractAst (setOfSeq [g]) t with extractG using eqExpr in

let extractTmp = preprocess (bindall_ [
  nulet_ h (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  nulet_ tmp (app_ (nvar_ h) (int_ 2)),
  int_ 0
]) in
utest extractAst (setOfSeq [tmp]) t with extractTmp using eqExpr in

let t = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ g (ulam_ "x" (muli_ (app_ (nvar_ f) (var_ "x")) (int_ 2))),
  nulet_ h (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  nulet_ tmp (app_ (nvar_ g) (int_ 4)),
  nvar_ tmp
]) in

let extracted = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ g (ulam_ "x" (muli_ (app_ (nvar_ f) (var_ "x")) (int_ 2))),
  nulet_ tmp (app_ (nvar_ g) (int_ 4)),
  int_ 0
]) in
utest extractAst (setOfSeq [tmp]) t with extracted using eqExpr in

let t1 = nameSym "t" in
let t2 = nameSym "t" in
let distinctCalls = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  nulet_ g (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ t1 (app_ (nvar_ f) (int_ 1)),
  nulet_ t2 (app_ (nvar_ g) (int_ 0)),
  addi_ (nvar_ t1) (nvar_ t2)
]) in
let extracted = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  nulet_ g (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ t1 (app_ (nvar_ f) (int_ 1)),
  nulet_ t2 (app_ (nvar_ g) (int_ 0)),
  int_ 0
]) in
utest extractAst (setOfSeq [t1, t2]) distinctCalls with extracted using eqExpr in

let inRecursiveBinding = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  nureclets_ [
    (g, ulam_ "x" (app_ (nvar_ f) (addi_ (var_ "x") (int_ 1)))),
    (h, ulam_ "x" (app_ (nvar_ t1) (var_ "x"))),
    (t1, ulam_ "x" (app_ (nvar_ g) (var_ "x")))
  ],
  app_ (nvar_ h) (int_ 3)
]) in
let extracted = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  nureclets_ [
    (g, ulam_ "x" (app_ (nvar_ f) (addi_ (var_ "x") (int_ 1)))),
    (t1, ulam_ "x" (app_ (nvar_ g) (var_ "x")))],
  int_ 0
]) in
utest extractAst (setOfSeq [t1]) inRecursiveBinding with extracted using eqExpr in

-- Tests that a binding that is used by multiple extracted bindings is only
-- included once in the extracted AST.
let multipleDependOnSame = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ t1 (ulam_ "x" (ulam_ "y" (
    addi_ (var_ "x") (app_ (nvar_ f) (var_ "y"))))),
  nulet_ t2 (ulam_ "x" (ulam_ "y" (
    muli_ (var_ "x") (app_ (nvar_ f) (var_ "y"))))),
  addi_ (appf2_ (nvar_ t1) (int_ 0) (int_ 1)) (appf2_ (nvar_ t2) (int_ 3) (int_ 4))
]) in
let extracted = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  nulet_ t1 (ulam_ "x" (ulam_ "y" (
    addi_ (var_ "x") (app_ (nvar_ f) (var_ "y"))))),
  nulet_ t2 (ulam_ "x" (ulam_ "y" (
    muli_ (var_ "x") (app_ (nvar_ f) (var_ "y"))))),
  int_ 0
]) in
utest extractAst (setOfSeq [t1, t2]) multipleDependOnSame with extracted using eqExpr in

-- NOTE(larshum, 2023-05-30): This test checks that the type referred to only
-- by an external is included, even if type-checking has not ran yet (meaning
-- there are no other references to the type in the expression).
let extTypeDependency = preprocess (bindall_ [
  type_ "t" [] (tyvariant_ []),
  ext_ "fun" false (tyarrow_ tyint_ (tycon_ "t")),
  nulet_ f (ulam_ "x" (app_ (var_ "fun") (var_ "x"))),
  int_ 0
]) in
utest expr2str (extractAst (setOfSeq [f]) extTypeDependency)
with expr2str extTypeDependency using eqString in

-- NOTE(larshum, 2024-04-17): We only run symbolization, to expose a (now
-- fixed) bug in the collection of type identifiers in constructor definitions.
let extConApp = symbolize (bindall_ [
  type_ "T" [] (tyvariant_ []),
  condef_ "Con" (tyarrow_ tyint_ (tycon_ "T")),
  nulet_ f (ulam_ "x" (var_ "x")),
  nulet_ g (ulam_ "y" (conapp_ "Con" (app_ (nvar_ f) (var_ "y")))),
  int_ 0
]) in
utest expr2str (extractAst (setOfSeq [g]) extConApp)
with expr2str extConApp using eqString in

let multiConExtract = preprocess (bindall_ [
  type_ "T" [] (tyvariant_ []),
  condef_ "A" (tyarrow_ tyint_ (tycon_ "T")),
  condef_ "B" (tyarrow_ tyint_ (tycon_ "T")),
  nlet_ f (tyarrow_ tyint_ (tycon_ "T")) (ulam_ "x" (conapp_ "A" (var_ "x"))),
  int_ 0
]) in
utest expr2str (extractAst (setOfSeq [f]) multiConExtract)
with expr2str multiConExtract using eqString in

()
