-- Defines a language fragment for constructing a call-graph of the bindings in
-- a recursive let-expression. The call graph contains an edge from a to b if
-- the body of binding a contains a call to binding b.

include "digraph.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"

lang MExprCallGraph = MExprAst
  sem constructCallGraph =
  | TmRecLets t ->
    let g : Digraph Name Int = digraphEmpty nameCmp eqi in
    let g = _addGraphVertices g (TmRecLets {t with inexpr = unit_}) in
    _addGraphCallEdges g t.bindings
  | t ->
    errorSingle [infoTm t] (join ["A call graph can only be constructed ",
                                    "from a recursive let-expression"])

  sem _addGraphVertices (g : Digraph Name Int) =
  | TmLet t ->
    let g =
      match t.tyBody with TyArrow _ then digraphAddVertex t.ident g
      else g
    in
    let g = _addGraphVertices g t.body in
    _addGraphVertices g t.inexpr
  | TmRecLets t ->
    let g =
      foldl
        (lam g. lam bind : RecLetBinding. digraphAddVertex bind.ident g)
        g t.bindings in
    let g =
      foldl
        (lam g. lam bind : RecLetBinding.
          _addGraphVertices g bind.body)
        g t.bindings in
    _addGraphVertices g t.inexpr
  | t -> sfold_Expr_Expr _addGraphVertices g t

  sem _addGraphCallEdges (g : Digraph Name Int) =
  | bindings /- : [RecLetBinding] -/ ->
    let edges =
      foldl
        (lam edges. lam bind : RecLetBinding.
          _findCallEdges bind.ident g edges bind.body)
        (mapEmpty nameCmp) bindings in
    mapFoldWithKey
      (lam g : Digraph Name Int. lam edgeSrc : Name. lam edgeDsts : Set Name.
        mapFoldWithKey
          (lam g : Digraph Name Int. lam edgeDst : Name. lam.
            digraphAddEdge edgeSrc edgeDst 0 g)
          g edgeDsts)
      g edges

  sem _findCallEdges (src : Name) (g : Digraph Name Int)
                            (edges : Map Name (Set Name)) =
  | TmVar t ->
    if digraphHasVertex t.ident g then
      let outEdges =
        match mapLookup src edges with Some outEdges then
          setInsert t.ident outEdges
        else setOfSeq nameCmp [t.ident] in
      mapInsert src outEdges edges
    else edges
  | TmLet t ->
    let letSrc = match t.tyBody with TyArrow _ then t.ident else src in
    let edges = _findCallEdges letSrc g edges t.body in
    _findCallEdges src g edges t.inexpr
  | TmRecLets t ->
    let edges =
      foldl
        (lam edges : Map Name (Set Name). lam bind : RecLetBinding.
          _findCallEdges bind.ident g edges bind.body)
        edges t.bindings in
    _findCallEdges src g edges t.inexpr
  | t -> sfold_Expr_Expr (_findCallEdges src g) edges t
end

lang TestLang = MExprCallGraph + MExprSym + MExprTypeCheck
end

mexpr

use TestLang in

let preprocess = lam t.
  typeCheck (symbolize t)
in

let a = nameSym "a" in
let b = nameSym "b" in
let c = nameSym "c" in
let d = nameSym "d" in
let t = preprocess (nureclets_ [
  (a, ulam_ "x" (bindall_ [
    nulet_ b (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
    nulet_ c (ulam_ "x" (app_ (nvar_ b) (var_ "x"))),
    nulet_ d (ulam_ "x" (app_ (nvar_ b) (var_ "x"))),
    addi_ (addi_ (app_ (nvar_ b) (var_ "x"))
                 (app_ (nvar_ c) (var_ "x")))
          (app_ (nvar_ d) (int_ 2))]))]) in
let g = constructCallGraph t in
utest digraphSuccessors a g with [b, c, d] using eqSeq nameEq in
utest digraphSuccessors b g with [] using eqSeq nameEq in
utest digraphSuccessors c g with [b] using eqSeq nameEq in
utest digraphSuccessors d g with [b] using eqSeq nameEq in

()
