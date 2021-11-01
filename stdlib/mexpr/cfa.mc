-- CFA framework for MExpr. Currently, only 0-CFA (context insensitive) is
-- supported. The algorithm is based on Table 3.7 in the book "Principles of
-- Program Analysis" (Nielson et al.).

include "set.mc"
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

-- NOTE(dlunde,2021-11-01): It would be nice if CFAFunction type and the
-- 'functions' component of CFAGraph could be defined/added in the fragment
-- LamCFA, rather than here. I guess this is what product extensions will
-- eventually allow?
type CFAFunction = { fident: Name, idents: [Name], body: Name }
type CFAGraph = {
  functions: [CFAFunction],
  constraints: [Constraint],
  worklist: [Name],
  data: Map Name (Set AbsVal),
  edges: Map Name [Constraint]
}

emptyCFAGraph = {
  functions = [],
  constraints = [],
  worklist = [],
  data = mapEmpty nameCmp,
  edges = mapEmpty nameCmp
}

lang CFA = Ast

  syn Constraint =
  -- Intentionally left blank

  syn AbsVal =
  -- Intentionally left blank

  sem exprName =
  | t -> infoErrorExit (infoTm t) "Unsupported in exprName for CFA"

  sem _collectConstraints (acc: CFAGraph) =
  | t ->
    let acc = {
      acc with constraints =
        concat (generateConstraints acc.functions t) acc.constraints } in
    sfold_Expr_Expr _collectConstraints acc t

  sem generateConstraints (functions: [CFAFunction]) =
  -- Intentionally left blank

  sem initConstraint (graph: CFAGraph) =
  -- Intentionally left blank

  sem propagateConstraint (graph: CFAGraph) =
  -- Intentionally left blank

  -- CFAGraph -> Name -> Set AbsVal -> CFAGraph
  sem _addData (graph: CFAGraph) (q: Name) =
  | d ->
    match mapLookup q graph.data with Some dq then
    if subset d dq then graph else
      {{ graph with
           data = mapInsert q (setUnion dq d) graph.data } with
           worklist = cons q worklist }
    else never

  sem _collectFunctions (acc: CFAGraph) =
  -- Intentionally left blank. NOTE(dlunde,2021-11-01): It would be nice if
  -- this and other possible functions could be defined in language fragments
  -- below, and then somehow used abstractly here. For instance, fragments
  -- could define various initialization functions and put them in a list, and
  -- then all functions in this list would be called as part of initialization
  -- here in this base fragment.

end

-- av ∈ rhs
lang InitConstraint = CFA

  syn Constraint =
  | CstrInit { av: AbsVal, rhs: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrInit r -> _addData graph r.rhs (setInsert r.av setEmpty nameCmp)

end

-- lhs ⊆ rhs
lang DirectConstraint = CFA

  syn Constraint =
  | CstrDirect { lhs: Name, rhs: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrDirect r & cstr ->
    match mapLookup r.lhs graph.edges with Some elhs then
      { graph with edges = mapInsert r.lhs (cons cstr elhs) graph.edges }
    else never

  sem propagateConstraint (graph: CFAGraph) =
  | CstrDirect r ->
    match mapLookup r.lhs graph.data with Some dlhs then
      _addData graph r.rhs dlhs
    else never

end

lang ConditionalConstraint = CFA

  -- av ∈  lrhs ⇒ rlhs ⊆ rrhs
  syn Constraint =
  | CstrCond { av: AbsVal, lrhs: Name, rlhs: Name, rrhs: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrCond r & cstr ->
    match mapLookup r.rlhs graph.edges with Some erlhs then
    match mapLookup r.lrhs graph.edges with Some elrhs then
      let es = mapInsert r.rlhs (cons cstr erlhs) graph.edges in
      let es = mapInsert r.lrhs (cons cstr elrhs) es in
      { graph with edges = es }
    else never
    else never

  sem propagateConstraint (graph: CFAGraph) =
  | CstrCond r ->
    match mapLookup r.lrhs graph.data with Some dlrhs then
      if setMem r.av dlrhs then _addData graph r.rrhs dlrhs
      else graph
    else never

end

lang VarCFA = CFA + VarAst

  sem generateConstraints (functions: [CFAFunction]) =
  | TmVar t -> []

  sem exprName =
  | TmVar t -> t.ident

end

lang LamCFA = CFA + DirectConstraint + LamAst

  syn AbsVal =
  | AVLam { fident: Name, paramIdent: Name }

  sem _collectFunctions (acc: CFAGraph) =
  | TmLet { ident = fident, body = TmLam t } ->
    -- TODO Recurse here, collect all idents in sequence of lambda
    let cf = { fident = fident, ident = ident, body = exprName t.body } in
    { acc with functions = cons cf acc.functions }
  | TmLam t -> infoErrorExit t.info
      "Unbound TmLam. Did you run ANF transformation?"
  | t -> sfold_Expr_Expr _collectFunctions acc t

  sem generateConstraints (functions: [CFAFunction]) =
  | TmLet { ident = ident, body = TmLam _ } ->
    -- TODO The AVLam here will have a different form eventually
    [
      CstrInit { lhs = AVLam { ident = ident }, rhs = ident }
    ]

end

lang AppCFA = CFA + ConditionalConstraint + LamCFA + AppAst -- TODO Also reclets

  -- TODO Need to do something smart here... Actually, should be quite
  -- straightforward? a, b, and c flows to three first args in f.
  -- f a b c
  -- OPT f can only consist of functions of three or more arguments

  sem generateConstraints (functions: [CFAFunction]) =
  | TmApp t ->
    join (map (lam f: CFAFunction. [
      CstrCond { av = AVLam { ident = f.fident }, lrhs =, rlhs =, rrhs = },
      CstrCond { av =, lrhs =, rlhs =, rrhs = }
    ] ) functions)

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

-- NOTE We probably need more abstract values for records and variants to get
-- this right
lang MatchCFA = CFA + MatchAst
end

lang UtestCFA = CFA + UtestAst
  sem exprName =
  | TmUtest t -> exprName t.next
end

lang NeverCFA = CFA + NeverAst
end

lang ExtCFA = CFA + ExtAst
  sem exprName
  | TmExt t -> exprName t.inexpr
end

