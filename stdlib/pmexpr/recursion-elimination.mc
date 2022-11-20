-- Eliminates recursive bindings that do not make use of recursion by
-- translating them into regular let-bindings. The translation only takes place
-- if none of the bindings are recursive.

include "digraph.mc"
include "mexpr/ast-builder.mc"
include "pmexpr/ast.mc"
include "pmexpr/utils.mc"

lang PMExprRecursionElimination = PMExprAst
  -- Finds all outgoing edges, representing the indices of the bindings that
  -- are called from the given binding body.
  sem _recurElimFindCallEdges (bindingIdentToIndex : Map Name Int) =
  | t -> _recurElimFindCallEdgesH bindingIdentToIndex (setEmpty subi) t

  sem _recurElimFindCallEdgesH (bindingIdentToIndex : Map Name Int)
                               (edgesTo : Set Int) =
  | (TmApp _) & t ->
    match collectAppArguments t with (TmVar {ident = id}, _) then
      match mapLookup id bindingIdentToIndex with Some calledIndex then
        setInsert calledIndex edgesTo
      else edgesTo
    else sfold_Expr_Expr (_recurElimFindCallEdgesH bindingIdentToIndex) edgesTo t
  | t -> sfold_Expr_Expr (_recurElimFindCallEdgesH bindingIdentToIndex) edgesTo t

  -- Attempts to find a reverse topological ordering of the given recursive
  -- bindings, according to their dependency graph. On success, a permutation of
  -- the binding indices is returned. This permutation defines an order in which
  -- the bindings can be defined in sequence without use of recursion.
  sem findReverseTopologicalOrderingOfBindings =
  | bindings ->
    let bindings : [RecLetBinding] = bindings in

    -- Initialize graph with nodes representing each of the recursive bindings.
    let bindingIndices = create (length bindings) (lam i. i) in
    let g =
      foldl
        (lam g. lam index. digraphAddVertex index g)
        (digraphEmpty subi eqi)
        bindingIndices in

    -- Add edges from vertices of recursive bindings to vertices of bindings they
    -- contain a call to.
    let bindingIdentToIndex : Map Name Int =
      mapFromSeq nameCmp
        (mapi (lam i. lam binding : RecLetBinding. (binding.ident, i)) bindings)
    in
    let g =
      foldl
        (lam g. lam p : (Int, RecLetBinding).
          let idx = p.0 in
          let binding = p.1 in
          let outEdges = _recurElimFindCallEdges bindingIdentToIndex binding.body in
          mapFoldWithKey
            (lam g : Digraph Int Int. lam edgeEnd : Int. lam.
              digraphAddEdge idx edgeEnd 0 g)
            g outEdges)
        g (zip bindingIndices bindings) in

    -- If all SCCs have size 1, then Tarjan's SCC algorithm guarantees that the
    -- components will be ordered in reverse topological order. In addition, if
    -- there are no self-loops within these SCCs the bindings can safely be
    -- translated into a sequence of let-expressions in the (non-reversed)
    -- topological order.
    let s = digraphTarjan g in
    let canOrderBindingsTopologically =
      forAll
        (lam scc.
          if eqi (length scc) 1 then
            let vertex = head scc in
            null (digraphEdgesBetween vertex vertex g)
          else false)
        s in
    if canOrderBindingsTopologically then
      Some (join (reverse s))
    else None ()

  sem eliminateRecursion =
  | TmRecLets t ->
    let toLetBinding : Expr -> RecLetBinding -> Expr = lam inexpr. lam binding.
      TmLet {ident = binding.ident, tyAnnot = binding.tyAnnot, tyBody = binding.tyBody,
             body = binding.body, inexpr = inexpr,
             ty = tyTm inexpr, info = binding.info}
    in
    match findReverseTopologicalOrderingOfBindings t.bindings
    with Some permutation then
      let orderedBindings = permute t.bindings permutation in
      foldl toLetBinding t.inexpr orderedBindings
    else TmRecLets t
  | t -> smap_Expr_Expr eliminateRecursion t
end

mexpr

use PMExprRecursionElimination in

let t = symbolize (ureclets_ [
  ("b", ulam_ "y" (muli_ (var_ "y") (app_ (var_ "a") (int_ 3)))),
  ("c", ulam_ "z" (subi_ (var_ "z") (app_ (var_ "b") (int_ 2)))),
  ("a", ulam_ "x" (addi_ (var_ "x") (int_ 2)))
]) in
let expected = symbolize (bindall_ [
  ulet_ "a" (ulam_ "x" (addi_ (var_ "x") (int_ 2))),
  ulet_ "b" (ulam_ "y" (muli_ (var_ "y") (app_ (var_ "a") (int_ 3)))),
  ulet_ "c" (ulam_ "z" (subi_ (var_ "z") (app_ (var_ "b") (int_ 2)))),
  unit_
]) in
utest eliminateRecursion t with expected using eqExpr in

()
