-- CFA framework for MExpr. Currently, only 0-CFA (context insensitive) is
-- supported. The algorithm is based on Table 3.7 in the book "Principles of
-- Program Analysis" (Nielson et al.).
--
-- Only works on terms in ANF (e.g., by transformation with mexpr/anf.mc).

include "set.mc"
include "either.mc"
include "name.mc"

include "pprint.mc"
include "boot-parser.mc"
include "ast.mc"
include "anf.mc"
include "ast-builder.mc"

-- OPT(dlunde,2021-10-29): Map all names in analyzed program to integers
-- 0,1,...,#variables-1 to speed up analysis through tensor lookups? Current
-- analysis adds a log factor for lookups to the (already cubic) complexity.

-- NOTE(dlunde,2021-11-01): It would be nice if the CFAFunction type and
-- 'functions' component of CFAGraph could be defined/added in the fragment
-- LamCFA, rather than here. I guess this is what product extensions will
-- eventually allow?
-- NOTE(dlunde,2021-11-03): Also, CFAGraph should of course when possible be
-- defined as part of the CFA fragment (AbsVal and Constraint are not defined
-- out here).
type CFAFunction = { ident: Name, body: Either AbsVal Name }
type CFAGraph = {
  worklist: [Name],
  data: Map Name (Set AbsVal),
  edges: Map Name [Constraint]
}

let emptyCFAGraph = {
  worklist = [],
  data = mapEmpty nameCmp,
  edges = mapEmpty nameCmp
}

lang CFA = Ast + LetAst + MExprPrettyPrint

  syn Constraint =
  -- Intentionally left blank

  syn AbsVal =
  -- Intentionally left blank

  -- Main CFA algorithm
  sem cfa =
  | t ->

    -- Collect all functions
    let functions: [CFAFunction] = _collectFunctions [] t in

    -- Generate and collect all constraints
    let cstrs: [Constraint] = _collectConstraints functions [] t in

    -- Build the graph
    let graph = foldl initConstraint emptyCFAGraph cstrs in

    -- Iteration
    recursive let iter = lam graph: CFAGraph.
      if null graph.worklist then graph
      else
        let q = head graph.worklist in
        let graph = { graph with worklist = tail graph.worklist } in
        match _edgesLookup q graph.edges with cc in
        let graph = foldl propagateConstraint graph cc in
        iter graph
    in
    let graph = iter graph in

    -- Produce output
    graph

  -- Prints CFA names
  sem _printName (env: PprintEnv) =
  | n -> pprintCode 0 env (nvar_ n)

  -- Prints a CFA graph
  sem cfaGraphToString (env: PprintEnv) =
  | graph ->
    let graph: CFAGraph = graph in
    match mapAccumL _printName env graph.worklist with (env,worklist) in
    match mapAccumL (lam env: PprintEnv. lam b:(Name,Set AbsVal).
        match _printName env b.0 with (env,b0) in
        match mapAccumL absValToString env (setToSeq b.1) with (env,b1) in
        (env,(b0,b1))
      ) env (mapBindings graph.data)
    with (env, data) in
    match mapAccumL (lam env: PprintEnv. lam b:(Name,[Constraint]).
        match _printName env b.0 with (env,b0) in
        match mapAccumL constraintToString env b.1 with (env,b1) in
        (env,(b0,b1))
      ) env (mapBindings graph.edges)
    with (env, edges) in

    let str = join [
      "*** WORKLIST ***\n",
      "  [", strJoin ", " worklist, "]\n",
      "*** DATA ***\n",
      strJoin "\n" (map (lam b:(String,[String]).
        let avs = strJoin "\n" (map (concat "    ") b.1) in
        join ["  ", b.0, " =\n", avs]
      ) data), "\n",
      "*** EDGES ***\n",
      strJoin "\n" (map (lam b:(String,[String]).
        let cstrs = strJoin "\n" (map (concat "    ") b.1) in
        join ["  ", b.0, " =\n", cstrs]
      ) edges), "\n"
    ] in

    (env, str)

  -- Required for the data type Set AbsVal
  sem cmpAbsVal (lhs: AbsVal) =
  -- Intentionally left blank

  -- Required for the data type Set AbsVal
  sem eqAbsVal (lhs: AbsVal) =
  | rhs -> eqi (cmpAbsVal lhs rhs) 0

  -- For a given expression, returns the variable "labeling" that expression.
  -- The existence of such a label is guaranteed by ANF.
  sem exprName =
  | t -> infoErrorExit (infoTm t) "Unsupported in exprName for CFA"

  sem _collectConstraints (functions: [CFAFunction]) (acc: [Constraint]) =
  | t ->
    let acc = concat (generateConstraints functions t) acc in
    sfold_Expr_Expr (_collectConstraints functions) acc t

  sem generateConstraints (functions: [CFAFunction]) =
  | t -> []

  sem initConstraint (graph: CFAGraph) =
  -- Intentionally left blank

  sem propagateConstraint (graph: CFAGraph) =
  -- Intentionally left blank

  sem constraintToString (env: PprintEnv) =
  -- Intentionally left blank

  sem absValToString (env: PprintEnv) =
  -- Intentionally left blank

  sem _dataLookup (key: Name) =
  | dataMap -> mapLookupOrElse (lam. setEmpty cmpAbsVal) key dataMap

  sem _edgesLookup (key: Name) =
  | edgesMap -> mapLookupOrElse (lam. []) key edgesMap

  -- CFAGraph -> Name -> Set AbsVal -> CFAGraph
  sem _addData (graph: CFAGraph) (q: Name) =
  | d ->
    match _dataLookup q graph.data with dq in
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
  -- {lhs} ⊆ rhs
  | CstrDirectAv { lhs: AbsVal, rhs: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrDirect r & cstr ->
    match _edgesLookup r.lhs graph.edges with elhs in
    { graph with edges = mapInsert r.lhs (cons cstr elhs) graph.edges }
  | CstrDirectAv r -> _addData graph r.rhs (setInsert r.lhs (setEmpty cmpAbsVal))

  sem propagateConstraint (graph: CFAGraph) =
  | CstrDirect r ->
    match _dataLookup r.lhs graph.data with dlhs in
    _addData graph r.rhs dlhs

  sem constraintToString (env: PprintEnv) =
  | CstrDirect { lhs = lhs, rhs = rhs } ->
    match _printName env lhs with (env,lhs) in
    match _printName env rhs with (env,rhs) in
    (env, join [lhs, " ⊆ ", rhs])
  | CstrDirectAv { lhs = lhs, rhs = rhs } ->
    match absValToString env lhs with (env,lhs) in
    match _printName env rhs with (env,rhs) in
    (env, join ["{", lhs, "}", " ⊆ ", rhs])

end

lang ConditionalConstraint = CFA

  syn Constraint =
  -- {llhs} ⊆ lrhs ⇒ rlhs ⊆ rrhs
  | CstrCond { llhs: AbsVal, lrhs: Name, rlhs: Name, rrhs: Name }
  -- {lav} ⊆ lrhs ⇒ rlhs ⊆ rrhs
  | CstrCondAv { llhs: AbsVal, lrhs: Name, rlhs: AbsVal, rrhs: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrCond r & cstr ->
    match _edgesLookup r.rlhs graph.edges with erlhs in
    match _edgesLookup r.lrhs graph.edges with elrhs in
    let es = mapInsert r.rlhs (cons cstr erlhs) graph.edges in
    let es = mapInsert r.lrhs (cons cstr elrhs) es in
    { graph with edges = es }
  | CstrCondAv r & cstr ->
    match _edgesLookup r.lrhs graph.edges with elrhs in
    let es = mapInsert r.lrhs (cons cstr elrhs) graph.edges in
    { graph with edges = es }

  sem propagateConstraint (graph: CFAGraph) =
  | CstrCond r ->
    match _dataLookup r.lrhs graph.data with dlrhs in
    if setMem r.llhs dlrhs then
      match _dataLookup r.rlhs graph.data with drlhs in
      _addData graph r.rrhs drlhs
    else graph
  | CstrCondAv r ->
    match _dataLookup r.lrhs graph.data with dlrhs in
    if setMem r.llhs dlrhs then
      _addData graph r.rrhs (setInsert r.rlhs (setEmpty cmpAbsVal))
    else graph

  sem constraintToString (env: PprintEnv) =
  | CstrCond { llhs = llhs, lrhs = lrhs, rlhs = rlhs, rrhs = rrhs } ->
    match absValToString env llhs with (env,llhs) in
    match _printName env lrhs with (env,lrhs) in
    match _printName env rlhs with (env,rlhs) in
    match _printName env rrhs with (env,rrhs) in
    (env, join [ "{", llhs, "}", " ⊆ ", lrhs, " ⇒ ", rlhs, " ⊆ ", rrhs ])
  | CstrCondAv { llhs = llhs, lrhs = lrhs, rlhs = rlhs, rrhs = rrhs } ->
    match absValToString env llhs with (env,llhs) in
    match _printName env lrhs with (env,lrhs) in
    match absValToString env rlhs with (env,rlhs) in
    match _printName env rrhs with (env,rrhs) in
    join [ "{", llhs, "}", " ⊆ ", lrhs, " ⇒ ", "{",rlhs, "}", " ⊆ ", rrhs ]

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

  sem cmpAbsVal (lhs: AbsVal) =
  | AVLam { ident = nrhs } ->
    match lhs with AVLam { ident = nlhs } then
      nameCmp nlhs nrhs
    else error "Cannot compare in cmpAbsVal for AVLam"

  sem _collectFunctions (acc: [CFAFunction]) =
  | TmLam t & tm ->
    let body: Either AbsVal Name =
      match t.body with TmLam { ident = ident } then
        Left (AVLam { ident = ident })
      else Right (exprName t.body)
    in
    let cfaFun = { ident = t.ident, body = body } in
    sfold_Expr_Expr _collectFunctions (cons cfaFun acc) tm
  | t -> sfold_Expr_Expr _collectFunctions acc t

  sem generateConstraints (functions: [CFAFunction]) =
  | TmLet { ident = ident, body = TmLam t } ->
    [ CstrDirectAv { lhs = AVLam { ident = t.ident }, rhs = ident } ]

  sem absValToString (env: PprintEnv) =
  | AVLam { ident = ident } ->
    match _printName env ident with (env,ident) in
    (env, join ["lam ", ident])

end

lang AppCFA = CFA + ConditionalConstraint + LamCFA + AppAst

  sem generateConstraints (functions: [CFAFunction]) =
  | TmLet { ident = ident, body = TmApp _ & body} ->
    recursive let rec = lam acc: [Constraint]. lam res: Name. lam t: Expr.
      match t with TmApp t in
      match t.lhs with TmConst t then acc
      else
        let nameLhs =
          match t.lhs with TmApp t then nameSym "cfaIntermediate"
          else match t.lhs with TmVar t then t.ident
          else infoErrorExit (infoTm t.lhs) "Not a variable or application in CFA"
        in
        let cstrs = join (map (lam f: CFAFunction.
          let c1 =
            match t.rhs with TmVar { ident = nameRhs } then
              [CstrCond {
                 llhs = AVLam { ident = f.ident },
                 lrhs = nameLhs,
                 rlhs = nameRhs,
                 rrhs = f.ident
              }]
            else [] in
          let c2 =
            match f.body with Left av then
              CstrCondAv {
                llhs = AVLam { ident = f.ident },
                lrhs = nameLhs,
                rlhs = av,
                rrhs = res
              }
            else match f.body with Right n then
              CstrCond {
                llhs = AVLam { ident = f.ident },
                lrhs = nameLhs,
                rlhs = n,
                rrhs = res
              }
            else never in
          cons c2 c1
        ) functions) in

        let acc = concat cstrs acc in

        match t.lhs with TmApp _ then rec acc nameLhs t.lhs else acc
    in rec [] ident body
end

lang LetCFA = CFA + LetAst
  sem exprName =
  | TmLet t -> exprName t.inexpr
end

lang RecLetsCFA = CFA + LamCFA + RecLetsAst
  sem exprName =
  | TmRecLets t -> exprName t.inexpr

  sem generateConstraints (functions: [CFAFunction]) =
  | TmRecLets { bindings = bindings } ->
    map (lam b: RecLetBinding.
      match b.body with TmLam t then
        CstrDirectAv { lhs = AVLam { ident = t.ident}, rhs = b.ident }
      else infoErrorExit (infoTm b.body) "Not a lambda in recursive let body"
    ) bindings

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

lang MExprCFA =
  CFA + DirectConstraint + ConditionalConstraint + VarCFA + LamCFA + AppCFA +
  LetCFA + RecLetsCFA + ConstCFA + SeqCFA + RecordCFA + TypeCFA + DataCFA +
  MatchCFA + UtestCFA + NeverCFA + ExtCFA


-----------
-- TESTS --
-----------

lang Test = MExprCFA + MExprANF + BootParser + MExprPrettyPrint

mexpr
use Test in

-- Test functions --
let parse = parseMExprString [] in
let test: Bool -> Expr -> [String] -> [[AbsVal]] =
  lam debug: Bool. lam t: Expr. lam vars: [String].
    let tANF = normalizeTerm t in
    let cfaRes = cfa tANF in
    (if debug then
       match pprintCode 0 pprintEnvEmpty t with (_,tStr) in
       printLn "\n--- ORIGINAL PROGRAM ---";
       printLn tStr;
       match pprintCode 0 pprintEnvEmpty tANF with (env,tANFStr) in
       printLn "\n--- ANF ---";
       printLn tANFStr;
       match cfaGraphToString env cfaRes with (_, resStr) in
       printLn "\n--- FINAL CFA GRAPH ---";
       printLn resStr
     else ());
    map (lam var: String.
      (var, _dataLookup (nameNoSym var) cfaRes.data)
    ) vars
in
let _avslam = lam s. AVLam { ident = nameNoSym s } in
let eqTest = eqSeq (lam t1:(String,[AbsVal]). lam t2:(String,[String]).
  if eqString t1.0 t2.0 then
    let t21 = setOfSeq cmpAbsVal (map _avslam t2.1) in
    setEq t1.1 t21
  else false
) in
--------------------

-- First test from Nielson et al.
let t = parse "
  (lam x. x) (lam y. y)
------------------------" in
utest test false t ["x","y"] with [
  ("x", ["y"]),
  ("y", [])
] using eqTest in

-- Second test from Nielson et al.
let t = parse "
  let f = lam x. x 1 in
  let g = lam y. addi y 2 in
  let h = lam z. addi z 3 in
  let res = addi (f g) (f h) in
  res
------------------------" in
utest test false t ["f","g","h","x","y","z","res"] with [
  ("f", ["x"]),
  ("g", ["y"]),
  ("h", ["z"]),
  ("x", ["y","z"]),
  ("y", []),
  ("z", []),
  ("res", [])
] using eqTest in

-- Third test from Nielson et al.
let t = parse "
recursive let g = lam x. g (lam y. y) in
let res = g (lam z. z) in
res
------------------------" in
utest test false t ["g","x","y","z","res"] with [
  ("g", ["x"]),
  ("x", ["y","z"]),
  ("y", []),
  ("z", []),
  ("res", [])
] using eqTest in

()
