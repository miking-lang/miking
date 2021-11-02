-- CFA framework for MExpr. Currently, only 0-CFA (context insensitive) is
-- supported. The algorithm is based on Table 3.7 in the book "Principles of
-- Program Analysis" (Nielson et al.).
--
-- Only works on terms in ANF (e.g., by transformation with mexpr/anf.mc).

include "set.mc"
include "either.mc"
include "name.mc"
include "ast.mc"

-- OPT(dlunde,2021-10-29): Map all names in analyzed program to integers 0,1,...,#variables-1
-- to speed up analysis? Or, use a hash table?

-- NOTE:
-- * We need to handle sequences of applications specially, (e.g., f a b c d)  since they are not labelled by ANF
-- * AVLam should perhaps be adapted to also contain currying information.

-- Extensible types (syn)
-- * Abstract values. By default, this will only contain term names (for, e.g., functions).
-- * Constraints. By default, we have direct constraints and implication constraints

-- Required data structures for algorithm
-- * A set of constraints (Could possibly just be a list?)
-- * A sequence W containing nodes for which constraints must be propagated.
-- * A data tensor D such that D[n] is a set of abstract values.
-- * Edge tensor E encoding constraints for each node.

-- Semantic functions (sem)
-- * Generate constraints from a program
-- * Build the graph from constraints
-- * Propagate constraints

-- NOTE(dlunde,2021-11-01): It would be nice if the CFAFunction type and
-- 'functions' component of CFAGraph could be defined/added in the fragment
-- LamCFA, rather than here. I guess this is what product extensions will
-- eventually allow?
type CFAFunction = { ident: Name, body: Either AbsVal Name }
type CFAGraph = {
  functions: [CFAFunction],
  constraints: [Constraint],
  worklist: [Name],
  data: Map Name (Set AbsVal),
  edges: Map Name [Constraint]
}

let emptyCFAGraph = {
  functions = [],
  constraints = [],
  worklist = [],
  data = mapEmpty nameCmp,
  edges = mapEmpty nameCmp
}

lang CFA = Ast + LetAst

  syn Constraint =
  -- Intentionally left blank

  syn AbsVal =
  -- Intentionally left blank

  sem exprName =
  | t -> infoErrorExit (infoTm t) "Unsupported in exprName for CFA"

  sem _collectConstraints (acc: CFAGraph) =
  | t ->
    let acc = { acc with
      constraints = concat (generateConstraints acc.functions t) acc.constraints
    } in
    sfold_Expr_Expr _collectConstraints acc t

  sem generateConstraints (functions: [CFAFunction]) =
  | t -> []

  sem initConstraint (graph: CFAGraph) =
  -- Intentionally left blank

  sem propagateConstraint (graph: CFAGraph) =
  -- Intentionally left blank

  -- CFAGraph -> Name -> Set AbsVal -> CFAGraph
  sem _addData (graph: CFAGraph) (q: Name) =
  | d ->
    match mapLookup q graph.data with Some dq in
    if setSubset d dq then graph else
      {{ graph with
           data = mapInsert q (setUnion dq d) graph.data } with
           worklist = cons q graph.worklist }

  sem _collectFunctions (acc: [CFAFunction]) =
  -- Intentionally left blank. NOTE(dlunde,2021-11-01): It would be nice if
  -- this and other possible functions could be defined in language fragments
  -- below, and then somehow used abstractly here. For instance, fragments
  -- could define various initialization functions and put them in a list, and
  -- then all functions in this list would be called as part of initialization
  -- here in this base fragment.

end

lang DirectConstraint = CFA

  syn Constraint =
  -- lhs ⊆ rhs
  | CstrDirect { lhs: Name, rhs: Name }
  -- {av} ⊆ rhs
  | CstrDirectAv { av: AbsVal, rhs: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrDirect r & cstr ->
    match mapLookup r.lhs graph.edges with Some elhs in
    { graph with edges = mapInsert r.lhs (cons cstr elhs) graph.edges }
  | CstrDirectAv r -> _addData graph r.rhs (setInsert r.av (setEmpty nameCmp))

  sem propagateConstraint (graph: CFAGraph) =
  | CstrDirect r ->
    match mapLookup r.lhs graph.data with Some dlhs in
    _addData graph r.rhs dlhs

end

lang ConditionalConstraint = CFA

  syn Constraint =
  -- av ∈  lrhs ⇒ rlhs ⊆ rrhs
  | CstrCond { av: AbsVal, lrhs: Name, rlhs: Name, rrhs: Name }
  -- lav ∈  lrhs ⇒ rav ⊆ rrhs
  | CstrCondAv { lav: AbsVal, lrhs: Name, rav: AbsVal, rrhs: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrCond r & cstr ->
    match mapLookup r.rlhs graph.edges with Some erlhs in
    match mapLookup r.lrhs graph.edges with Some elrhs in
    let es = mapInsert r.rlhs (cons cstr erlhs) graph.edges in
    let es = mapInsert r.lrhs (cons cstr elrhs) es in
    { graph with edges = es }
  | CstrCondAv r & cstr ->
    match mapLookup r.lrhs graph.edges with Some elrhs in
    let es = mapInsert r.lrhs (cons cstr elrhs) graph.edges in
    { graph with edges = es }

  sem propagateConstraint (graph: CFAGraph) =
  | CstrCond r ->
    match mapLookup r.lrhs graph.data with Some dlrhs in
    if setMem r.av dlrhs then
      match mapLookup r.rlhs with Some drlhs in
      _addData graph r.rrhs drlhs
    else graph
  | CstrCondAv r ->
    match mapLookup r.lrhs graph.data with Some dlrhs in
    if setMem r.av dlrhs then
      _addData graph r.rrhs (setInsert r.rav (setEmpty nameCmp))
    else graph

end

lang VarCFA = CFA + DirectConstraint + VarAst

  sem generateConstraints (functions: [CFAFunction]) =
  | TmLet { ident = ident, body = TmVar t } ->
    [ CstrDirect { lhs = t.ident, rhs = ident } ]

  sem exprName =
  | TmVar t -> t.ident

end

lang LamCFA = CFA + DirectConstraint + LamAst

  syn AbsVal =
  | AVLam { ident: Name }

  sem _collectFunctions (acc: [CFAFunction]) =
  | TmLam t & tm ->
    let body: Either AbsVal Name =
      match t.body with TmLam { ident = ident } then
        Left (AVLam { ident = ident })
      else Right (exprName t.body)
    in
    let cfaFun = { ident = t.ident, body = body } in
    sfold_Expr_Expr _collectFunctions (cons cfaFun acc) t
  | t -> sfold_Expr_Expr _collectFunctions acc t

  sem generateConstraints (functions: [CFAFunction]) =
  | TmLet { ident = ident, body = TmLam t } ->
    [ CstrDirectAv { lhs = AVLam { ident = t.ident }, rhs = ident } ]

end

lang AppCFA = CFA + ConditionalConstraint + LamCFA + AppAst

  sem generateConstraints (functions: [CFAFunction]) =
  | TmLet { ident = ident, body = TmApp _ & body} ->
    recursive let rec = lam acc: [Constraint]. lam res: Name. lam t: Expr.
      let nameLhs =
        match t.lhs with TmApp t then nameSym "cfaIntermediate"
        else match t.lhs with TmVar t then t.ident
        else infoErrorExit (infoTm t.lhs) "Not a variable or application in CFA"
      in
      let cstrs = join (map (lam f: CFAFunction.
        let c1 =
          match t.rhs with TmVar { ident = nameRhs } then
            [CstrCond {
               av = AVLam { ident = f.ident },
               lrhs = nameLhs,
               rlhs = nameRhs,
               rrhs = f.ident
            }]
          else [] in
        let c2 =
          match f.body with Left av then
            CstrCondAv {
              lav = AVLam { ident = f.ident },
              lrhs = nameLhs,
              rav = av,
              rrhs = res
            }
          else match f.body with Right n then
            CstrCond {
              lav = AVLam { ident = f.ident },
              lrhs = nameLhs,
              rlhs = n,
              rrhs = res
            }
          else never in
        cons c2 c1
      ) functions) in

      let acc = concat cstrs acc in

      match t.lhs with TmApp t then rec acc nameLhs t.lhs else acc
    in rec [] ident body
end

lang LetCFA = CFA + LetAst
  sem exprName =
  | TmLet t -> exprName t.inexpr
end

lang RecLetsCFA = CFA + RecLetsAst
  sem exprName =
  | TmRecLets t -> exprName t.inexpr
end

lang ConstCFA = CFA + ConstAst
end

lang SeqCFA = CFA + SeqAst
end

lang RecordCFA = CFA + RecordAst
end

lang TypeCFA = CFA + TypeAst
  sem exprName =
  | TmType t -> exprName t.inexpr
end

lang DataCFA = CFA + DataAst
  sem exprName =
  | TmConDef t -> exprName t.inexpr
end

lang MatchCFA = CFA + MatchAst
end

lang UtestCFA = CFA + UtestAst
  sem exprName =
  | TmUtest t -> exprName t.next
end

lang NeverCFA = CFA + NeverAst
end

lang ExtCFA = CFA + ExtAst
  sem exprName =
  | TmExt t -> exprName t.inexpr
end

