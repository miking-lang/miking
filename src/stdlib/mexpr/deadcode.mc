include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/builtin.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/side-effect.mc"
include "mexpr/symbolize.mc"
include "mlang/lazy-ast.mc"
include "lazy.mc"
include "name.mc"
include "map.mc"
include "set.mc"
include "basic-types.mc"
include "int.mc"
include "bool.mc"
include "seq.mc"

lang DeadcodeElimination = Ast
  type NMapEntry = {
    -- The set of variables inside the let that points backwards.
    vars : Set Name,

    -- Flag determining if the let is used.
    used : Bool,

    -- Flag determining if the let body (possibly) contains side-effects.
    sideEffect : Bool,

    -- The number of lambdas at the top of the body.
    lambdaCount : Int
  }
  type NMap = Map Name NMapEntry

  -- Determines whether the provided expression may contain a side-effect. It
  -- is conservative and returns false only if the expression definitely does
  -- not contain a side-effect.
  sem tmHasSideEffect : NMap -> Bool -> Expr -> Bool

  -- Collects all variables in an expression
  sem collectVars : Set Name -> Expr -> Set Name

  -- Counts the number of lambdas directly below in an expression.
  sem lamCounts : Int -> NMap -> Expr -> Int

  -- Counts the number of lambdas directly below in an expression. If negative,
  -- it needs to be treated as an open let with side-effects.
  sem lambdasLeft : NMap -> Int -> Bool -> Expr -> (Int, Bool)

  -- Count the number of lambdas (arrow types) in a type.
  sem lambdasInType : Type -> Int

  -- Helper function that collects let information and free variables.
  -- Return a tuple consisting of two elements:
  -- 1. An NMap which maps let symbols to an entry.
  -- 2. A set of all variables that are free (not under a lambda in a let).
  sem collectInBody : Name -> NMap -> Set Name -> Expr -> (NMap, Set Name)

  -- Collect all mappings for lets (mapping the name of a let to the set of
  -- variables in its body). Also collects all variables that are free, not
  -- under a lambda in a let.
  sem collectLetsDecl : (NMap, Set Name) -> Decl -> (NMap, Set Name)
  sem collectLets : (NMap, Set Name) -> Expr -> (NMap, Set Name)

  -- Returns a new NMap where all lets that are used are marked as true. Uses
  -- depth-first search (DFS) with color marking. Returns the resulting NMap.
  sem markUsedLetsDfs : (Set Name, NMap) -> Name -> (Set Name, NMap)
  sem markUsedLets : NMap -> Set Name -> NMap

  -- Removes all lets that have not been marked as used.
  sem removeLetsDecl : NMap -> Decl -> Option Decl
  sem removeLets : NMap -> Expr -> Expr
end

lang MExprDeadcodeEliminationVar = DeadcodeElimination + VarAst
  sem tmHasSideEffect : NMap -> Bool -> Expr -> Bool
  sem tmHasSideEffect nmap acc +=
  | TmVar t ->
    if acc then true
    else match mapLookup t.ident nmap with Some {sideEffect = se} then se
    else false

  sem collectVars : Set Name -> Expr -> Set Name
  sem collectVars free +=
  | TmVar t ->
    setInsert t.ident free

  sem lamCounts : Int -> NMap -> Expr -> Int
  sem lamCounts n nmap +=
  | TmVar t ->
    match mapLookup t.ident nmap with Some {lambdaCount = lc} then
      addi n lc
    else n

  sem lambdasLeft : NMap -> Int -> Bool -> Expr -> (Int, Bool)
  sem lambdasLeft nmap n se +=
  | TmVar t ->
    match mapLookup t.ident nmap with Some {sideEffect = se2, lambdaCount = nLambdas} then
      let left = maxi 0 (addi n nLambdas) in
      (left, if gti left 0 then se else or se se2)
    else
      (0, se)

  sem collectLets : (NMap, Set Name) -> Expr -> (NMap, Set Name)
  sem collectLets acc +=
  | TmVar t ->
    match acc with (nmap, free) in
    (nmap, setInsert t.ident free)
end

lang MExprDeadcodeEliminationOpaque = DeadcodeElimination + OpaqueAst
  sem removeLets nmap +=
  | tm & TmOpaque _ -> tm
end

lang MExprDeadcodeEliminationApp = DeadcodeElimination + AppAst
  sem lambdasLeft : NMap -> Int -> Bool -> Expr -> (Int, Bool)
  sem lambdasLeft nmap n se +=
  | TmApp t ->
    let tmSe = tmHasSideEffect nmap false t.rhs in
    lambdasLeft nmap (subi n 1) (or se tmSe) t.lhs
end

lang MExprDeadcodeEliminationConst = DeadcodeElimination + ConstAst + ConstSideEffect
  sem tmHasSideEffect : NMap -> Bool -> Expr -> Bool
  sem tmHasSideEffect nmap acc +=
  | TmConst t ->
    if acc then true else constHasSideEffect t.val
end

lang MExprDeadcodeEliminationLam = DeadcodeElimination + LamAst
  sem lamCounts : Int -> NMap -> Expr -> Int
  sem lamCounts n nmap +=
  | TmLam t ->
    lamCounts (addi n 1) nmap t.body

  sem collectInBody : Name -> NMap -> Set Name -> Expr -> (NMap, Set Name)
  sem collectInBody s nmap free +=
  | TmLam t ->
    let vars = collectVars (setEmpty nameCmp) t.body in
    let se = tmHasSideEffect nmap false t.body in
    let entry = {
      vars = vars,
      used = false,
      sideEffect = se,
      lambdaCount = lamCounts 1 nmap t.body
    } in
    (mapInsert s entry nmap, free)
end

lang MExprDeadcodeEliminationDecl = DeadcodeElimination + DeclAst
  sem collectLets : (NMap, Set Name) -> Expr -> (NMap, Set Name)
  sem collectLets acc +=
  | TmDecl t ->
    let acc = collectLetsDecl acc t.decl in
    collectLets acc t.inexpr

  sem removeLets : NMap -> Expr -> Expr
  sem removeLets nmap +=
  | TmDecl t ->
    match removeLetsDecl nmap t.decl with Some decl then
      TmDecl {t with decl = decl, inexpr = removeLets nmap t.inexpr}
    else
      removeLets nmap t.inexpr
end

lang MExprDeadcodeEliminationLetDecl = DeadcodeElimination + LetDeclAst
  sem collectLetsDecl : (NMap, Set Name) -> Decl -> (NMap, Set Name)
  sem collectLetsDecl acc +=
  | DeclLet t ->
    match acc with (nmap, free) in
    collectInBody t.ident nmap free t.body

  sem removeLetsDecl : NMap -> Decl -> Option Decl
  sem removeLetsDecl nmap +=
  | DeclLet t ->
    match mapFindExn t.ident nmap with {used = true} then
      Some (DeclLet t)
    else
      None ()
end

lang MExprDeadcodeEliminationRecLetsDecl = DeadcodeElimination + RecLetsDeclAst + LazyAst
  sem collectLetsDecl : (NMap, Set Name) -> Decl -> (NMap, Set Name)
  sem collectLetsDecl acc +=
  | DeclRecLets t ->
    let f = lam acc : (NMap, Set Name). lam bind : DeclLetRecord.
      match acc with (nmap, free) in
      collectInBody bind.ident nmap free bind.body
    in
    match foldl f acc t.bindings with (nmap, free) in
    let update = lam orig : Name. lam nmap : NMap. lam bind : DeclLetRecord.
      let tt = mapFindExn bind.ident nmap in
      if setMem orig tt.vars then
        mapInsert bind.ident {tt with sideEffect = true} nmap
      else nmap
    in
    let handleSideEffect = lam nmap : NMap. lam bind : DeclLetRecord.
      let tt = mapFindExn bind.ident nmap in
      if tt.sideEffect then foldl (update bind.ident) nmap t.bindings else nmap
    in
    let nmap = foldl handleSideEffect nmap t.bindings in
    (nmap, free)

  sem removeLetsDecl : NMap -> Decl -> Option Decl
  sem removeLetsDecl nmap +=
  | DeclRecLets t ->
    let bindingIsUsed = lam bind.
      let entry = mapFindExn bind.ident nmap in
      entry.used
    in
    let bindings = filter bindingIsUsed t.bindings in
    if null bindings then None ()
    else Some (DeclRecLets {t with bindings = bindings})
end

lang MExprDeadcodeEliminationExtDecl = DeadcodeElimination + ExtDeclAst
  sem collectLetsDecl : (NMap, Set Name) -> Decl -> (NMap, Set Name)
  sem collectLetsDecl acc +=
  | DeclExt t ->
    match acc with (nmap, free) in
    let entry = {
      vars = setEmpty nameCmp,
      used = false,
      sideEffect = t.effect,
      lambdaCount = lambdasInType t.tyIdent
    } in
    let nmap = mapInsert t.ident entry nmap in
    (nmap, free)

  sem removeLetsDecl : NMap -> Decl -> Option Decl
  sem removeLetsDecl nmap +=
  | DeclExt t ->
    match mapFindExn t.ident nmap with {used = true} then
      Some (DeclExt t)
    else
      None ()
end

lang MExprDeadcodeEliminationFunType = DeadcodeElimination + FunTypeAst
  sem lambdasInType : Type -> Int
  sem lambdasInType +=
  | TyArrow t ->
    addi 1 (lambdasInType t.to)
end

lang MExprDeadcodeEliminationLazy = DeadcodeElimination + LazyAst
  sem tmHasSideEffect : NMap -> Bool -> Expr -> Bool
  sem tmHasSideEffect nmap acc +=
  | TmLazy t -> if acc then true else t.sideEffect

  sem collectVars : Set Name -> Expr -> Set Name
  sem collectVars free +=
  | TmLazy t -> setUnion free t.freeVars

  sem removeLets : NMap -> Expr -> Expr
  sem removeLets nmap +=
  | tm & TmLazy t -> tm
end

lang MExprDeadcodeElimination =
  MExprDeadcodeEliminationVar + MExprDeadcodeEliminationApp +
  MExprDeadcodeEliminationConst + MExprDeadcodeEliminationLam +
  MExprDeadcodeEliminationDecl + MExprDeadcodeEliminationLetDecl +
  MExprDeadcodeEliminationRecLetsDecl + MExprDeadcodeEliminationExtDecl +
  MExprDeadcodeEliminationFunType + MExprDeadcodeEliminationOpaque +
  MExprDeadcodeEliminationLazy

  sem tmHasSideEffect : NMap -> Bool -> Expr -> Bool
  sem tmHasSideEffect nmap acc +=
  | t ->
    if acc then true else sfold_Expr_Expr (tmHasSideEffect nmap) acc t

  sem collectVars : Set Name -> Expr -> Set Name
  sem collectVars free +=
  | t ->
    sfold_Expr_Expr collectVars free t

  sem lamCounts : Int -> NMap -> Expr -> Int
  sem lamCounts n nmap +=
  | _ ->
    n

  sem lambdasLeft : NMap -> Int -> Bool -> Expr -> (Int, Bool)
  sem lambdasLeft nmap n se +=
  | t ->
    let tmSe = tmHasSideEffect nmap false t in
    (maxi 0 n, or se tmSe)

  sem lambdasInType : Type -> Int
  sem lambdasInType +=
  | _ ->
    0

  sem collectInBody : Name -> NMap -> Set Name -> Expr -> (NMap, Set Name)
  sem collectInBody s nmap free +=
  | body ->
    match lambdasLeft nmap 0 false body with (lambdas, seFree) in
    let se = tmHasSideEffect nmap false body in
    let vars = collectVars (setEmpty nameCmp) body in
    let used =
      if and (gti lambdas 0) (not seFree) then false
      else se
    in
    let free = if used then mapUnion free vars else free in
    let entry = {
      vars = vars,
      used = used,
      sideEffect = se,
      lambdaCount = lambdas
    } in
    (mapInsert s entry nmap, free)

  sem collectLetsDecl : (NMap, Set Name) -> Decl -> (NMap, Set Name)
  sem collectLetsDecl acc +=
  | _ ->
    acc

  sem collectLets : (NMap, Set Name) -> Expr -> (NMap, Set Name)
  sem collectLets acc +=
  | t ->
    sfold_Expr_Expr collectLets acc t

  sem markUsedLetsDfs : (Set Name, NMap) -> Name -> (Set Name, NMap)
  sem markUsedLetsDfs acc +=
  | id ->
    match acc with (visited, nmap) in
    if setMem id visited then (visited, nmap)
    else
      let visited = setInsert id visited in
      match mapLookup id nmap with Some tt then
        let nmap = mapInsert id {tt with used = true} nmap in
        setFold markUsedLetsDfs (visited, nmap) tt.vars
      else
        (visited, nmap)

  sem markUsedLets : NMap -> Set Name -> NMap
  sem markUsedLets nmap +=
  | free ->
    match setFold markUsedLetsDfs (setEmpty nameCmp, nmap) free with (_, usedLets) in
    usedLets

  sem removeLetsDecl : NMap -> Decl -> Option Decl
  sem removeLetsDecl nmap +=
  | t -> Some t

  sem removeLets : NMap -> Expr -> Expr
  sem removeLets nmap +=
  | t -> smap_Expr_Expr (removeLets nmap) t

  sem deadcodeElimination : Expr -> Expr
  sem deadcodeElimination =
  | t ->
    match collectLets (mapEmpty nameCmp, setEmpty nameCmp) t with (nmap, free) in
    let nmap = markUsedLets nmap free in
    removeLets nmap t
end

lang TestLang = MExprDeadcodeElimination + MExprEq + MExprPrettyPrint
end

mexpr

use TestLang in

let pprintExprs = lam l. lam r.
  join ["LHS:\n", expr2str l, "\n\nRHS:\n", expr2str r]
in

let e =
  bind_
    (ulet_ "x" (int_ 2))
    (var_ "x")
in
utest deadcodeElimination e with e using eqExpr else pprintExprs in

let e =
  bindall_
    [ ulet_ "x" (int_ 2)
    , ulet_ "y" (int_ 3) ]
    (var_ "y")
in
let expected = bind_ (ulet_ "y" (int_ 3)) (var_ "y") in
utest deadcodeElimination e with expected using eqExpr else pprintExprs in

let e =
  bind_
    (ureclets_ [
      ("x", (ulam_ "a" (app_ (var_ "y") (var_ "a")))),
      ("y", (ulam_ "b" (int_ 0)))
    ])
    (var_ "x")
in
utest deadcodeElimination e with e using eqExpr else pprintExprs in

let e =
  bind_
    (ureclets_ [
      ("x", (ulam_ "a" (app_ (var_ "y") (var_ "a")))),
      ("y", (ulam_ "b" (app_ (var_ "x") (var_ "b")))),
      ("z", (ulam_ "c" (int_ 0)))
    ])
    (var_ "y")
in
let expected =
  bind_
    (ureclets_
      [ ("x", (ulam_ "a" (app_ (var_ "y") (var_ "a"))))
      , ("y", (ulam_ "b" (app_ (var_ "x") (var_ "b")))) ])
    (var_ "y")
in
utest deadcodeElimination e with expected using eqExpr else pprintExprs in

let e =
  bindall_
    [ ulet_ "z" (int_ 0)
    , ureclets_
      [ ("x", (ulam_ "a" (app_ (var_ "y") (var_ "a"))))
      , ("y", (ulam_ "b" (app_ (var_ "x") (var_ "b")))) ] ]
    (var_ "z")
in
let expected = bind_ (ulet_ "z" (int_ 0)) (var_ "z") in
utest deadcodeElimination e with expected using eqExpr else pprintExprs in

let e =
  bindall_
    [ ext_ "abs_int" true (tyarrow_ tyint_ tyint_)
    , ulet_ "" (app_ (var_ "abs_int") (int_ -3)) ]
    (int_ 0)
in
utest deadcodeElimination e with e using eqExpr else pprintExprs in

let e =
  bindall_
    [ ext_ "abs_int" false (tyarrow_ tyint_ tyint_)
    , ulet_ "" (app_ (var_ "abs_int") (int_ -3)) ]
    (int_ 0)
in
utest deadcodeElimination e with int_ 0 using eqExpr else pprintExprs in

()
