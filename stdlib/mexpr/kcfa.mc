-- k-CFA framework for MExpr, where k is the number of most recent
-- function calls to consider in the context. The algorithm is loosely based on
-- Table 3.7 in the book "Principles of Program Analysis" (Nielson et al.).
--
-- Some details:
-- - Only works on fully labelled terms provided by MExprANFAll (see mexpr/anf.mc).
-- - Uses efficient lazy constraint expansion, and not the static
--   constraints from table 3.7 in Nielson et al. (see p. 202 in Nielson et al.
--   for a discussion about this).
--
-- TODO(2023-07-11,dlunde): I just fixed a number of bugs in cfa.mc related to
-- higher-order constants (and this also involved quite significant changes in
-- other parts of the CFA framework). I am pretty sure k-CFA also have the same
-- bugs/problems with higher-order constants, but I have not fixed them. We
-- should rework kcfa.mc in the same way as for cfa.mc.

include "set.mc"
include "either.mc"
include "name.mc"
include "tensor.mc"
include "stringid.mc"

include "pprint.mc"
include "boot-parser.mc"
include "ast.mc"
include "anf.mc"
include "ast-builder.mc"
include "cmp.mc"
include "const-arity.mc"
include "index.mc"
include "free-vars.mc"

include "cfa.mc"

lang KCFA = CFABase

  type Ctx = [IName]
  type CtxEnv = Map IName Ctx
  type GenFunAcc = (CtxEnv, [Constraint])
  type GenFun = Ctx -> CtxEnv -> Expr -> GenFunAcc
  type MatchGenFun = (IName,Ctx) -> (IName,Ctx) -> Pat -> [Constraint]

  type CFAGraph = {

    -- Contains updates that needs to be processed in the main CFA loop
    worklist: [(IName,Ctx,AbsVal)],

    -- Contains abstract values currently associated with each name in the program.
    data: Tensor[Map Ctx (Set AbsVal)],

    -- For each name in the program, gives constraints which needs to be
    -- repropagated upon updates to the abstract values for the name.
    edges: Tensor[Map Ctx (Set Constraint)],

    -- Bidirectional mapping between names and integers.
    im: IndexMap,

    -- The "k" in k-CFA.
    k: Int,

    -- Contains a list of functions used for generating constraints
    cgfs: [GenFun],

    -- Contains a list of functions used for generating match constraints
    -- TODO(dlunde,2021-11-17): Should be added as a product extension
    -- in the MatchCFA fragment instead, when possible.
    mcgfs: [MatchGenFun],

    -- NOTE(dlunde,2021-11-18): Data needed for analyses based on this framework
    -- must be put below directly, since we do not yet have product extensions.

    -- Used to store any custom data in the graph
    graphData: Option GraphData

  }

  sem emptyCFAGraph: Int -> Expr -> CFAGraph
  sem emptyCFAGraph k =
  | t ->
    -- NOTE(Linnea,2022-06-22): Experiments have shown that lists are better
    -- than ropes for 'worklist' and 'edges', especially for 'worklist'
    let im = indexGen t in
    let shape = tensorShape im.int2name in
    { worklist = toList [],
      data = tensorCreateDense shape (lam. mapEmpty cmpCtx),
      edges = tensorCreateDense shape (lam. mapEmpty cmpCtx),
      im = im,
      k = k,
      cgfs = [],
      mcgfs = [],
      graphData = None () }

  -- This function converts the data-flow result into a map, which might be more
  -- convenient to operate on for later analysis steps.
  sem cfaGraphData: CFAGraph -> Map Name (Set AbsVal)
  sem cfaGraphData =
  | graph ->
    tensorFoldi (lam acc. lam i: [Int]. lam vals: Set AbsVal.
        mapInsert (int2name graph.im (head i)) vals acc
      ) (mapEmpty nameCmp) graph.data

  -- Main algorithm
  sem solveCfa: CFAGraph -> CFAGraph
  sem solveCfa =
  | graph ->
    -- Iteration
    recursive let iter = lam graph: CFAGraph.
      if null graph.worklist then graph
      else
        match head graph.worklist with (q,c,d) & h in
        let graph = { graph with worklist = tail graph.worklist } in
        match edgesLookup (q,c) graph with cc in
        let graph = setFold (propagateConstraint h) graph cc in
        iter graph
    in
    iter graph

  -- Main algorithm (debug version)
  sem solveCfaDebug : PprintEnv -> CFAGraph -> (PprintEnv, CFAGraph)
  sem solveCfaDebug pprintenv =
  | graph ->
    -- NOTE(Linnea,2022-06-22): Experiments have shown that using `cfaDebug` as
    -- the main entry point causes overhead when no printing takes place, as we
    -- have to match on the pprintenv in every iteration. Therefore, some code
    -- duplication takes place here.
    let printGraph = lam pprintenv. lam graph. lam str.
      match cfaGraphToString pprintenv graph with (pprintenv, graph) in
      printLn (join ["\n--- ", str, " ---"]);
      printLn graph;
      pprintenv
    in

    -- Iteration
    recursive let iter = lam i. lam pprintenv: PprintEnv. lam graph: CFAGraph.
      if null graph.worklist then (pprintenv,graph)
      else
        let header = concat "INTERMEDIATE CFA GRAPH " (int2string i) in
        let pprintenv = printGraph pprintenv graph header in
        match head graph.worklist with (q,c,d) & h in
        let graph = { graph with worklist = tail graph.worklist } in
        match edgesLookup (q,c) graph with cc in
        let graph = setFold (propagateConstraint h) graph cc in
        iter (addi i 1) pprintenv graph
    in
    iter 1 pprintenv graph

  -- Base constraint generation function (must still be included manually in
  -- constraintGenFuns)
  sem generateConstraints
  : IndexMap -> Ctx -> CtxEnv -> Expr -> GenFunAcc
  sem generateConstraints im ctx env =
  | t -> (env,[])

  -- Call a set of constraint generation functions on each term in program.
  -- Useful when defining values of type CFAGraph.
  sem collectConstraints: Ctx -> [GenFun] -> GenFunAcc -> Expr -> GenFunAcc
  sem collectConstraints ctx cgfs acc =
  | t ->
    let acc = foldl (lam acc. lam f: GenFun.
        match acc with (env, cstrs) in
        match f ctx env t with (env, fcstrs) in
        (env, concat fcstrs cstrs)
      ) acc cgfs
    in
    sfold_Expr_Expr (collectConstraints ctx cgfs) acc t

  sem initConstraint: CFAGraph -> Constraint -> CFAGraph

  -- Function that initializes all constraints in a CFAGraph for a given context
  -- and context environment
  sem initConstraints
  : Ctx -> CtxEnv -> CFAGraph -> Expr -> (CtxEnv, CFAGraph)
  sem initConstraints ctx env graph =
  | t ->
    -- Recurse over program and generate constraints
    match
      collectConstraints ctx graph.cgfs (env, []) t
    with (env, cstrs) in

    -- Initialize all collected constraints and return
    (env, foldl initConstraint graph cstrs)

  sem propagateConstraint
  : (IName,Ctx,AbsVal) -> CFAGraph -> Constraint -> CFAGraph

  -- Returns both the new graph, and a Boolean that is true iff the new edge was
  -- added to the graph.
  -- NOTE(Linnea, 2022-06-21): Updates the graph by a side effect
  sem addEdge: CFAGraph -> (IName,Ctx) -> Constraint -> (CFAGraph, Bool)
  sem addEdge (graph: CFAGraph) (qc: (IName,Ctx)) =
  | cstr ->
    match qc with (q,c) in
    let cstrsq = edgesLookup qc graph in
    if setMem cstr cstrsq then (graph, false)
    else
      let m = mapInsert c (setInsert cstr cstrsq) (
        tensorLinearGetExn graph.edges q) in
      tensorLinearSetExn graph.edges q m;
      (graph, true)

  -- Helper function for initializing a constraint for a given name (mainly
  -- used for convenience in initConstraint)
  sem initConstraintName: (IName,Ctx) -> CFAGraph -> Constraint -> CFAGraph
  sem initConstraintName name graph =
  | cstr ->
    match addEdge graph name cstr with (graph, new) in
    if new then
      let avs = dataLookup name graph in
      setFold (lam graph. lam av.
        propagateConstraint (name.0,name.1,av) graph cstr)
      graph avs
    else graph

  sem dataLookup: (IName,Ctx) -> CFAGraph -> Set AbsVal
  sem dataLookup key =
  | graph ->
    let m = tensorLinearGetExn graph.data key.0 in
    mapLookupOrElse (lam. setEmpty cmpAbsVal) key.1 m

  sem edgesLookup: (IName,Ctx) -> CFAGraph -> Set Constraint
  sem edgesLookup (key: (IName,Ctx)) =
  | graph ->
    let m = tensorLinearGetExn graph.edges key.0 in
    mapLookupOrElse (lam. setEmpty cmpConstraint) key.1 m

  -- Updates the graph by a side effect
  sem addData: CFAGraph -> AbsVal -> (IName,Ctx) -> CFAGraph
  sem addData (graph: CFAGraph) (d: AbsVal) =
  | (q,c) ->
    let dq = dataLookup (q,c) graph in
    if setMem d dq then graph else
      let m = mapInsert c (setInsert d dq) (tensorLinearGetExn graph.data q) in
      tensorLinearSetExn graph.data q m;
      { graph with worklist = cons (q,c,d) graph.worklist }

  --------------------------------------
  -- CONTEXTS AND CONTEXT ENVIRONMENT --
  --------------------------------------

  sem ctxEmpty: () -> Ctx
  sem ctxEmpty =
  | _ -> []

  sem ctxAdd: Int -> IName -> Ctx -> Ctx
  sem ctxAdd k n =
  | ctx ->
    let ctx = snoc ctx n in
    if leqi (length ctx) k then ctx else tail ctx

  -- Needed for `Map Ctx (Set AbsVal)`
  sem cmpCtx: Ctx -> Ctx -> Int
  sem cmpCtx ctx1 =
  | ctx2 -> seqCmp subi ctx1 ctx2

  -- Needed for `Set (IName,Ctx)`
  sem cmpINameCtx: (IName,Ctx) -> (IName,Ctx) -> Int
  sem cmpINameCtx t1 =
  | t2 ->
    let ndiff = subi t1.0 t2.0 in
    if eqi ndiff 0 then cmpCtx t1.1 t2.1
    else ndiff

  sem ctxToString: IndexMap -> PprintEnv -> Ctx -> (PprintEnv, String)
  sem ctxToString im env =
  | ctx ->
    match mapAccumL (pprintVarIName im) env ctx with (env,ctx) in
    (env, join ["<", strJoin "," ctx, ">"])

  sem ctxEnvEmpty: () -> CtxEnv
  sem ctxEnvEmpty =
  | _ -> mapEmpty subi

  sem ctxEnvAdd: IName -> Ctx -> CtxEnv -> CtxEnv
  sem ctxEnvAdd n c =
  | env ->
    mapInsert n c env

  sem ctxEnvLookup: IndexMap -> Info -> IName -> CtxEnv -> Ctx
  sem ctxEnvLookup im info n =
  | env ->
    mapLookupOrElse (lam.
        let name = int2name im n in
        errorSingle [info] (concat "ctxEnvLookup failed: " (nameGetStr name))
      ) n env

  -- Keep names that appear free in a given expression.
  sem ctxEnvFilterFree: IndexMap -> Expr -> CtxEnv -> CtxEnv
  sem ctxEnvFilterFree im e =
  | env ->
    let free: Set Name = freeVars e in
    mapFoldWithKey (lam acc. lam n. lam ctx.
        if setMem (int2name im n) free then mapInsert n ctx acc
        else acc
      ) (mapEmpty subi) env

  sem cmpCtxEnv: CtxEnv -> CtxEnv -> Int
  sem cmpCtxEnv env1 =
  | env2 -> mapCmp cmpCtx env1 env2

  ---------------------
  -- PRETTY PRINTING --
  ---------------------

  sem pprintVarINameCtx
  : IndexMap -> PprintEnv -> (IName,Ctx) -> (PprintEnv, String)
  sem pprintVarINameCtx im env =
  | (n,ctx) ->
    match pprintVarIName im env n with (env,n) in
    match ctxToString im env ctx with (env,ctx) in
    (env, join [n, ctx])

  sem pprintConINameCtx
  : IndexMap -> PprintEnv -> (IName,Ctx) -> (PprintEnv, String)
  sem pprintConINameCtx im env =
  | (n,ctx) ->
    match pprintConIName im env n with (env,n) in
    match ctxToString im env ctx with (env,ctx) in
    (env, join [n, ctx])

  -- Prints a CFA graph
  sem cfaGraphToString (env: PprintEnv) =
  | graph ->
    let graph: CFAGraph = graph in
    let f = lam env. lam e: (IName,Ctx,AbsVal).
      match pprintVarINameCtx graph.im env (e.0,e.1) with (env,n) in
      match absValToString graph.im env e.2 with (env,av) in
      (env,join ["(", n, ", ", av, ")"]) in
    match mapAccumL f env graph.worklist with (env,worklist) in
    match mapAccumL (lam env: PprintEnv. lam b:(IName,Map Ctx (Set AbsVal)).
        match pprintVarIName graph.im env b.0 with (env,b0) in
        let printAbsVals = lam env. lam s: Set AbsVal.
          mapAccumL (absValToString graph.im) env (setToSeq s)
        in
        match mapAccumL (lam env: PprintEnv. lam b:(Ctx,Set AbsVal).
            match ctxToString graph.im env b.0 with (env, ctx) in
            match printAbsVals env b.1 with (env, avs) in
            (env, (ctx, avs))
          ) env (mapBindings b.1)
        with (env,b1)
        in (env,(b0,b1))
      ) env (mapi (lam i. lam x. (i,x)) (tensorToSeqExn graph.data))
    with (env, data) in
    match mapAccumL (lam env: PprintEnv. lam b:(IName,Map Ctx (Set Constraint)).
        match pprintVarIName graph.im env b.0 with (env,b0) in
        let printCstrs = lam env. lam cstrs: Set Constraint.
          mapAccumL (constraintToString graph.im) env (setToSeq cstrs)
        in
        match mapAccumL (lam env: PprintEnv. lam b:(Ctx,Set Constraint).
            match ctxToString graph.im env b.0 with (env, ctx) in
            match printCstrs env b.1 with (env, cstrs) in
            (env, (ctx, cstrs))
          ) env (mapBindings b.1)
        with (env,(b1))
        in (env,(b0,b1))
      ) env (mapi (lam i. lam x. (i, x)) (tensorToSeqExn graph.edges))
    with (env, edges) in

    let strJoinNonEmpty = lam delim: String. lam strs: [String].
      strJoin delim (filter (lam s. not (null s)) strs)
    in

    let str = join [
      "*** WORKLIST ***\n",
      "  [", strJoin ", " worklist, "]\n",
      "*** DATA ***\n",
      strJoinNonEmpty "\n" (map (lam b:(String,[(String, [String])]).
        match b with (n, ctxsAvs) in
        let f = lam avs.
          strJoin "\n" (map (concat "    ") avs)
        in
        let entries: [String] = map (lam ctxAvs: (String, [String]).
            match ctxAvs with (ctx, avs) in
            join ["  ", join [b.0, ctx], " =\n", f avs]
          ) ctxsAvs
        in strJoin "\n" entries
      ) data), "\n",
      "*** EDGES ***\n",
      strJoinNonEmpty "\n" (map (lam b:(String,[(String, [String])]).
        match b with (n, ctxCstrs) in
        let f = lam cstrs.
          strJoin "\n" (map (concat "    ") cstrs)
        in
        let entries: [String] = map (lam cc: (String, [String]).
            match cc with (ctx, cstrs) in
            join ["  ", join [b.0, ctx], " =\n", f cstrs]
          ) ctxCstrs
        in strJoin "\n" entries
      ) edges), "\n"

    ] in

    (env, str)

end

----------------------
-- BASE CONSTRAINTS --
----------------------

lang KBaseConstraint = KCFA

  syn Constraint =
  -- {lhs} ⊆ rhs
  | CstrInit { lhs: AbsVal, rhs: (IName,Ctx) }
  -- lhs ⊆ rhs
  | CstrDirect { lhs: (IName,Ctx), rhs: (IName,Ctx) }
  -- {lhsav} ⊆ lhs ⇒ {rhsav} ⊆ rhs
  | CstrDirectAv { lhs: (IName,Ctx), lhsav: AbsVal,
                   rhs: (IName,Ctx), rhsav: AbsVal }
  -- {lhsav} ⊆ lhs ⇒ [rhs]
  | CstrDirectAvCstrs { lhs: (IName,Ctx), lhsav: AbsVal, rhs: [Constraint] }

  sem cmpConstraintH =
  | (CstrInit { lhs = lhs1, rhs = rhs1 },
     CstrInit { lhs = lhs2, rhs = rhs2 }) ->
     let d = cmpAbsVal lhs1 lhs2 in
     if eqi d 0 then cmpINameCtx rhs1 rhs2
     else d
  | (CstrDirect { lhs = lhs1, rhs = rhs1 },
     CstrDirect { lhs = lhs2, rhs = rhs2 }) ->
     let d = cmpINameCtx lhs1 lhs2 in
     if eqi d 0 then cmpINameCtx rhs1 rhs2
     else d
  | (CstrDirectAv t1, CstrDirectAv t2) ->
     let d = cmpINameCtx t1.lhs t2.lhs in
     if eqi d 0 then
       let d = cmpINameCtx t1.rhs t2.rhs in
       if eqi d 0 then
         let d = cmpAbsVal t1.lhsav t2.lhsav in
         if eqi d 0 then cmpAbsVal t1.rhsav t2.rhsav
         else d
       else d
     else d
  | (CstrDirectAvCstrs t1, CstrDirectAvCstrs t2) ->
     let d = cmpINameCtx t1.lhs t2.lhs in
     if eqi d 0 then
       let d = cmpAbsVal t1.lhsav t2.lhsav in
       if eqi d 0 then seqCmp cmpConstraint t1.rhs t2.rhs
       else d
     else d

  sem initConstraint (graph: CFAGraph) =
  | CstrInit r -> addData graph r.lhs r.rhs
  | CstrDirect r & cstr -> initConstraintName r.lhs graph cstr
  | CstrDirectAv r & cstr -> initConstraintName r.lhs graph cstr
  | CstrDirectAvCstrs r & cstr -> initConstraintName r.lhs graph cstr

  sem constraintToString im (env: PprintEnv) =
  | CstrInit { lhs = lhs, rhs = rhs } ->
    match absValToString im env lhs with (env,lhs) in
    match pprintVarINameCtx im env rhs with (env,rhs) in
    (env, join ["{", lhs, "}", " ⊆ ", rhs])
  | CstrDirect { lhs = lhs, rhs = rhs } ->
    match pprintVarINameCtx im env lhs with (env,lhs) in
    match pprintVarINameCtx im env rhs with (env,rhs) in
    (env, join [lhs, " ⊆ ", rhs])
  | CstrDirectAv { lhs = lhs, lhsav = lhsav, rhs = rhs, rhsav = rhsav } ->
    match pprintVarINameCtx im env lhs with (env,lhs) in
    match absValToString im env lhsav with (env,lhsav) in
    match pprintVarINameCtx im env rhs with (env,rhs) in
    match absValToString im env rhsav with (env,rhsav) in
    (env, join ["{", lhsav ,"} ⊆ ", lhs, " ⇒ {", rhsav ,"} ⊆ ", rhs])
  | CstrDirectAvCstrs { lhs = lhs, lhsav = lhsav, rhs = rhs } ->
    match mapAccumL (constraintToString im) env rhs with (env,rhs) in
    let rhs = strJoin " AND " rhs in
    match pprintVarINameCtx im env lhs with (env,lhs) in
    match absValToString im env lhsav with (env,lhsav) in
    (env, join [ "{", lhsav, "} ⊆ ", lhs, " ⇒ (", rhs, ")" ])

  sem isDirect: AbsVal -> Bool
  sem isDirect =
  | _ -> true

  sem directTransition: CFAGraph -> (IName,Ctx) -> AbsVal -> AbsVal
  sem directTransition graph rhs =
  | av -> av

  sem propagateConstraint (update: (IName,Ctx,AbsVal)) (graph: CFAGraph) =
  | CstrDirect r -> propagateDirectConstraint r.rhs graph update.2
  | CstrDirectAv r ->
    if eqAbsVal update.2 r.lhsav then
      addData graph r.rhsav r.rhs
    else graph
  | CstrDirectAvCstrs r & cstr ->
    if eqAbsVal update.2 r.lhsav then
      foldl initConstraint graph r.rhs
    else graph

  sem propagateDirectConstraint: (IName,Ctx) -> CFAGraph -> AbsVal -> CFAGraph
  sem propagateDirectConstraint rhs graph =
  | av ->
    if isDirect av then
      addData graph (directTransition graph rhs av) rhs
    else graph

  sem propagateConstraintConst
  : (IName,Ctx) -> [(IName,Ctx)] -> CFAGraph -> Const -> CFAGraph
end

-----------
-- TERMS --
-----------

lang VarKCFA = KCFA + KBaseConstraint + VarAst

  sem generateConstraints im ctx env =
  | TmLet { ident = ident, body = TmVar t, info = info } ->
    let ident = name2int im info ident in
    let lhs = name2int im t.info t.ident in
    let cstrs =
      [ CstrDirect {
        lhs = (lhs, ctxEnvLookup im t.info lhs env),
        rhs = (ident, ctx)
      } ]
    in
    (ctxEnvAdd ident ctx env, cstrs)

  sem exprName =
  | TmVar t -> t.ident
end

lang LamKCFA = KCFA + KBaseConstraint + LamAst

  -- Abstract representation of lambdas.
  syn AbsVal =
  | AVLam { ident: IName, bident: IName, body: Expr, env: CtxEnv }

  sem cmpAbsValH =
  | (AVLam { ident = lhs, bident = lbody, env = lenv },
     AVLam { ident = rhs, bident = rbody, env = renv }) ->
     let diff = subi lhs rhs in
     if eqi diff 0 then
       let diff = subi lbody rbody in
       if eqi diff 0 then cmpCtxEnv lenv renv else diff
     else diff

  sem generateConstraints im ctx env =
  | TmLet { ident = ident, body = TmLam t, info = info } ->
    let ident = name2int im info ident in
    let av: AbsVal = AVLam {
      ident = name2int im t.info t.ident,
      bident = name2int im (infoTm t.body) (exprName t.body),
      body = t.body,
      env = ctxEnvFilterFree im (TmLam t) env
    } in
    let cstrs = [ CstrInit { lhs = av, rhs = (ident, ctx) } ] in
    (ctxEnvAdd ident ctx env, cstrs)

  sem absValToString im (env: PprintEnv) =
  | AVLam { ident = ident, bident = bident } ->
    match pprintVarIName im env ident with (env,ident) in
    match pprintVarIName im env bident with (env,bident) in
    (env, join ["lam ", ident, ". ", bident])

  -- We analyze the terms in the lambda body when discovering an application of
  -- an `AVLam`. Hence, we do nothing here.
  sem collectConstraints ctx cgfs acc =
  | TmLam t -> acc
end

lang LetKCFA = KCFA + LetAst
  sem exprName =
  | TmLet t -> exprName t.inexpr
end

lang RecLetsKCFA = KCFA + LamKCFA + RecLetsAst
  sem exprName =
  | TmRecLets t -> exprName t.inexpr

  sem generateConstraints im ctx env =
  | TmRecLets ({ bindings = bindings } & t) ->
    -- Make each binding available in the environment
    let idents = map (lam b. name2int im b.info b.ident) bindings in
    let envBody = foldl (lam env. lam i.
        ctxEnvAdd i ctx env) (ctxEnvFilterFree im (TmRecLets t) env) idents in
    let cstrs = map (lam identBind: (IName, RecLetBinding).
      match identBind with (ident, b) in
      match b.body with TmLam t then
        let av: AbsVal = AVLam {
          ident = name2int im t.info t.ident,
          bident = name2int im (infoTm t.body) (exprName t.body),
          body = t.body,
          env = envBody
        } in
        CstrInit { lhs = av, rhs = (ident, ctx) }
      else errorSingle [infoTm b.body] "Not a lambda in recursive let body"
    ) (zip idents bindings) in
    let env = foldl (lam env. lam i. ctxEnvAdd i ctx env) env idents in
    (env, cstrs)
end

lang ConstKCFA = KCFA + ConstAst + KBaseConstraint + Cmp

  syn AbsVal =
  -- Abstract representation of constants. Contains the constant and the
  -- arguments applied to it. It also includes the `let` name that binds the
  -- constant and syntactically distinguishes it from other of its kind in the
  -- program.
  | AVConst { id: (IName,Ctx), const: Const, args: [(IName,Ctx)] }

  sem absValToString im (env: PprintEnv) =
  | AVConst { id = id, const = const, args = args } ->
    let const = getConstStringCode 0 const in
    match mapAccumL (pprintVarINameCtx im) env args with (env,args) in
    let args = strJoin ", " args in
    match pprintVarINameCtx im env id with (env,id) in
    (env, join [const,"<", id, ">", "(", args, ")"])

  sem cmpAbsValH =
  | (AVConst lhs, AVConst rhs) ->
    let cmp = cmpConst lhs.const rhs.const in
    if eqi 0 cmp then
      let ncmp = cmpINameCtx lhs.id rhs.id in
      if eqi 0 ncmp then seqCmp cmpINameCtx lhs.args rhs.args
      else ncmp
    else cmp

  sem generateConstraints im ctx env =
  | TmLet { ident = ident, body = TmConst t, info = info } ->
    let ident = name2int im info ident in
    let cstrs = generateConstraintsConst t.info (ident,ctx) t.val in
    (ctxEnvAdd ident ctx env, cstrs)

  sem generateConstraintsConst: Info -> (IName,Ctx) -> Const -> [Constraint]
  sem generateConstraintsConst info ident =
  | _ -> errorSingle [info] "Constant not supported in CFA"
end

lang AppKCFA = KCFA + ConstKCFA + KBaseConstraint + LamKCFA + AppAst + MExprArity

  syn Constraint =
  -- {lam x. b} ⊆ lhs ⇒ (rhs ⊆ x and b ⊆ res)
  | CstrLamApp { lhs: (IName,Ctx), rhs: (IName,Ctx), res: (IName,Ctx) }
  -- {const args} ⊆ lhs ⇒ {const args lhs} ⊆ res
  | CstrConstApp { lhs: (IName,Ctx), rhs: (IName,Ctx),
                   res: (IName,Ctx) }

  sem cmpConstraintH =
  | (CstrLamApp { lhs = lhs1, rhs = rhs1, res = res1 },
     CstrLamApp { lhs = lhs2, rhs = rhs2, res = res2 }) ->
     let d = cmpINameCtx res1 res2 in
     if eqi d 0 then
       let d = cmpINameCtx lhs1 lhs2 in
       if eqi d 0 then cmpINameCtx rhs1 rhs2
       else d
     else d
  | (CstrConstApp { lhs = lhs1, rhs = rhs1, res = res1 },
     CstrConstApp { lhs = lhs2, rhs = rhs2, res = res2 }) ->
     let d = cmpINameCtx res1 res2 in
     if eqi d 0 then
       let d = cmpINameCtx lhs1 lhs2 in
       if eqi d 0 then cmpINameCtx rhs1 rhs2
       else d
     else d

  sem initConstraint (graph: CFAGraph) =
  | CstrLamApp r & cstr -> initConstraintName r.lhs graph cstr
  | CstrConstApp r & cstr -> initConstraintName r.lhs graph cstr

  sem propagateConstraint (update: (IName,Ctx,AbsVal)) (graph: CFAGraph) =
  | CstrLamApp { lhs = lhs, rhs = rhs, res = res } ->
    match update.2 with AVLam { ident = x, bident = b, body = body, env = env }
    then
      let ctxBody = ctxAdd graph.k res.0 res.1 in
      let envBody = ctxEnvAdd x ctxBody env in
      -- Analyze the lambda body
      match initConstraints ctxBody envBody graph body with (envBody, graph) in
      -- Add rhs ⊆ x constraint
      let graph = initConstraint graph (CstrDirect {
          lhs = rhs, rhs = (x, ctxBody)
        }) in
      -- Add b ⊆ res constraint
      let graph = initConstraint graph (CstrDirect {
          lhs = (b, ctxEnvLookup graph.im (infoTm body) b envBody), rhs = res
        }) in
      graph
    else graph
  | CstrConstApp { lhs = lhs, rhs = rhs, res = res } ->
    match update.2 with AVConst ({ const = const, args = args } & avc) then
      let arity = constArity const in
      let args = snoc args rhs in
      if eqi arity (length args) then
        -- Last application
        propagateConstraintConst res args graph const
      else
        -- Curried application, add the new argument
        addData graph (AVConst { avc with args = args }) res
    else graph

  sem constraintToString im (env: PprintEnv) =
  | CstrLamApp { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarINameCtx im env lhs with (env,lhs) in
    match pprintVarINameCtx im env rhs with (env,rhs) in
    match pprintVarINameCtx im env res with (env,res) in
    (env, join ["{lam >x<. >b<} ⊆ ", lhs, " ⇒ ", rhs, " ⊆ >x< AND >b< ⊆ ", res])
  | CstrConstApp { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarINameCtx im env lhs with (env,lhs) in
    match pprintVarINameCtx im env rhs with (env,rhs) in
    match pprintVarINameCtx im env res with (env,res) in
    (env, join [
        ">const< >args< ⊆ ", lhs, " ⇒ ", ">const< >args< ", rhs, " ⊆ ", res
      ])

  sem generateConstraints im ctx env =
  | TmLet { ident = ident, body = TmApp app, info = info} ->
    let ident = name2int im info ident in
    match app.lhs with TmVar l then
      match app.rhs with TmVar r then
        let lhs = name2int im l.info l.ident in
        let rhs = name2int im r.info r.ident in
        let lenv = ctxEnvLookup im l.info lhs env in
        let renv = ctxEnvLookup im r.info rhs env in
        let cstrs =
          [ CstrLamApp {
              lhs = (lhs, lenv),
              rhs = (rhs, renv),
                res = (ident, ctx)
              },
            CstrConstApp {
              lhs = (lhs, lenv),
              rhs = (rhs, renv),
              res = (ident, ctx)
            }
          ]
        in
        (ctxEnvAdd ident ctx env, cstrs)
      else errorSingle [infoTm app.rhs] "Not a TmVar in application"
    else errorSingle [infoTm app.lhs] "Not a TmVar in application"
end

lang RecordKCFA = KCFA + KBaseConstraint + RecordAst

  syn AbsVal =
  -- Abstract representation of records. The bindings are from SIDs to names,
  -- rather than expressions.
  | AVRec { bindings: Map SID (IName,Ctx) }

  sem cmpAbsValH =
  | (AVRec { bindings = lhs }, AVRec { bindings = rhs }) ->
    mapCmp cmpINameCtx lhs rhs

  syn Constraint =
  -- r ∈ lhs ⇒ { r with key = val } ∈ rhs
  | CstrRecordUpdate { lhs: (IName,Ctx), key: SID, val: (IName,Ctx),
                       rhs: (IName,Ctx) }

  sem cmpConstraintH =
  | (CstrRecordUpdate { lhs = lhs1, key = key1, val = val1, rhs = rhs1 },
     CstrRecordUpdate { lhs = lhs2, key = key2, val = val2, rhs = rhs2 }) ->
     let d = cmpINameCtx lhs1 lhs2 in
     if eqi d 0 then
       let d = cmpSID key1 key2 in
       if eqi d 0 then
         let d = cmpINameCtx val1 val2 in
         if eqi d 0 then cmpINameCtx rhs1 rhs2
         else d
       else d
     else d

  sem initConstraint (graph: CFAGraph) =
  | CstrRecordUpdate r & cstr -> initConstraintName r.lhs graph cstr

  sem generateConstraints im ctx env =
  | TmLet { ident = ident, body = TmRecord t, info = info } ->
    let bindings = mapMap (lam v: Expr.
        match v with TmVar t then
          let vident = name2int im t.info t.ident in
          let vctx = ctxEnvLookup im t.info vident env in
          (vident,vctx)
        else errorSingle [infoTm v] "Not a TmVar in record"
      ) t.bindings
    in
    let av: AbsVal = AVRec { bindings = bindings } in
    let ident = name2int im info ident in
    let cstrs = [ CstrInit { lhs = av, rhs = (ident, ctx) } ] in
    (ctxEnvAdd ident ctx env, cstrs)
  | TmLet { ident = ident, body = TmRecordUpdate t, info = info } ->
    match t.rec with TmVar vrec then
      match t.value with TmVar vval then
        let lhs = name2int im vrec.info vrec.ident in
        let val = name2int im vval.info vval.ident in
        let ident = name2int im info ident in
        let cstrs =
          [ CstrRecordUpdate { lhs = (lhs, ctxEnvLookup im vrec.info lhs env),
                               key = t.key,
                               val = (val, ctxEnvLookup im vval.info val env),
                               rhs = (ident, ctx)}
          ] in
        (ctxEnvAdd ident ctx env, cstrs)
      else errorSingle [t.info] "Not a TmVar in record update"
    else errorSingle [t.info] "Not a TmVar in record update"

  sem propagateConstraint (update: (IName,Ctx,AbsVal)) (graph: CFAGraph) =
  | CstrRecordUpdate { lhs = lhs, key = key, val = val, rhs = rhs } ->
    match update.2 with AVRec { bindings = bindings } then
      let av = AVRec { bindings = mapInsert key val bindings } in
      initConstraint graph (CstrInit { lhs = av, rhs = rhs })
    else graph

  sem absValToString im (env: PprintEnv) =
  | AVRec { bindings = bindings } ->
    match mapMapAccum (lam env. lam k. lam v.
        match pprintVarINameCtx im env v with (env, v) in
        (env, join [pprintLabelString k, " = ", v])
      ) env bindings
    with (env, bindings) in
    let binds = mapValues bindings in
    let merged = strJoin ", " binds in
    (env, join ["{ ", merged, " }"])

  sem constraintToString im (env: PprintEnv) =
  | CstrRecordUpdate { lhs = lhs, key = key, val = val, rhs = rhs } ->
    match pprintVarINameCtx im env lhs with (env,lhs) in
    match pprintLabelString key with key in
    match pprintVarINameCtx im env val with (env,val) in
    match pprintVarINameCtx im env rhs with (env,rhs) in
    (env, join [">r< ∈ ", lhs, " ⇒ { >r< with ", key, " = ", val, " } ∈ ", rhs])

end

lang SeqKCFA = KCFA + KBaseConstraint + SeqAst

  syn AbsVal =
  -- Abstract representation of sequences. Contains a set of names that may
  -- flow to the sequence.
  | AVSeq { names: Set (IName,Ctx) }

  sem cmpAbsValH =
  | (AVSeq { names = lhs }, AVSeq { names = rhs }) -> setCmp lhs rhs

  sem generateConstraints im ctx env =
  | TmLet { ident = ident, body = TmSeq t, info = info } ->
    let names = foldl (lam acc: [(IName,Ctx)]. lam t: Expr.
      match t with TmVar t then
        let tident = name2int im t.info t.ident in
        cons (tident, ctxEnvLookup im t.info tident env) acc
      else acc) [] t.tms
    in
    let av: AbsVal = AVSeq { names = setOfSeq cmpINameCtx names } in
    let ident = name2int im info ident in
    let cstrs = [ CstrInit { lhs = av, rhs = (ident, ctx) } ] in
    (ctxEnvAdd ident ctx env, cstrs)

  sem absValToString im (env: PprintEnv) =
  | AVSeq { names = names } ->
    match mapAccumL (pprintVarINameCtx im) env (setToSeq names)
    with (env,names) in
    let names = strJoin ", " names in
    (env, join ["[{", names, "}]"])
end

lang TypeKCFA = KCFA + TypeAst
  sem exprName =
  | TmType t -> exprName t.inexpr
end

lang DataKCFA = KCFA + KBaseConstraint + DataAst
  syn AbsVal =
  -- Abstract representation of constructed data.
  | AVCon { ident: (IName,Ctx), body: (IName,Ctx) }

  sem cmpAbsValH =
  | (AVCon { ident = ilhs, body = blhs },
     AVCon { ident = irhs, body = brhs }) ->
    let idiff = cmpINameCtx ilhs irhs in
    if eqi idiff 0 then cmpINameCtx blhs brhs else idiff

  sem generateConstraints im ctx env =
  | TmLet { ident = ident, body = TmConApp t, info = info } ->
    let body =
      match t.body with TmVar v then name2int im v.info v.ident
      else errorSingle [infoTm t.body] "Not a TmVar in con app" in
    let ctxBody = ctxEnvLookup im (infoTm t.body) body env in
    let av: AbsVal = AVCon {
        ident = (name2int im t.info t.ident, ctx),
        body = (body, ctxBody)
      } in
    let ident = name2int im info ident in
    let cstrs = [ CstrInit { lhs = av, rhs = (ident,ctx) } ] in
    (ctxEnvAdd ident ctx env, cstrs)

  sem absValToString im (env: PprintEnv) =
  | AVCon { ident = ident, body = body } ->
    match pprintConINameCtx im env ident with (env,ident) in
    match pprintVarINameCtx im env body with (env,body) in
    (env, join [ident, " ", body])

  sem exprName =
  | TmConDef t -> exprName t.inexpr

end

lang MatchKCFA = KCFA + KBaseConstraint + MatchAst + MExprCmp

  syn Constraint =
  | CstrMatch { id: (IName,Ctx), pat: Pat, target: (IName,Ctx) }

  sem cmpConstraintH =
  | (CstrMatch { id = id1, pat = pat1, target = target1 },
     CstrMatch { id = id2, pat = pat2, target = target2 }) ->
     let d = cmpINameCtx id1 id2 in
     if eqi d 0 then
       let d = cmpINameCtx target1 target2 in
       if eqi d 0 then cmpPat pat1 pat2
       else d
     else d

  sem initConstraint (graph: CFAGraph) =
  | CstrMatch r & cstr -> initConstraintName r.target graph cstr

  sem propagateConstraint (update: (IName,Ctx,AbsVal)) graph =
  | CstrMatch r ->
    propagateMatchConstraint graph r.id (r.pat,update.2)

  sem propagateMatchConstraint
  : CFAGraph -> (IName,Ctx) -> (Pat,AbsVal) -> CFAGraph
  sem propagateMatchConstraint graph id =
  | _ -> graph -- Default: do nothing

  sem constraintToString im (env: PprintEnv) =
  | CstrMatch { id = id, pat = pat, target = target } ->
    match pprintVarINameCtx im env id with (env, id) in
    match getPatStringCode 0 env pat with (env, pat) in
    match pprintVarINameCtx im env target with (env, target) in
    (env, join [id, ": match ", target, " with ", pat])

  sem generateConstraintsMatch
  : IndexMap -> [MatchGenFun] -> Ctx -> CtxEnv -> Expr -> GenFunAcc
  sem generateConstraintsMatch im mcgfs ctx env =
  | _ -> (env,[])
  | TmLet { ident = ident, body = TmMatch t, info = info } ->
    let thn = name2int im (infoTm t.thn) (exprName t.thn) in
    let els = name2int im (infoTm t.els) (exprName t.els) in
    let ident = name2int im info ident in
    let cstrs = [
      CstrDirect { lhs = (thn,ctx), rhs = (ident,ctx) },
      CstrDirect { lhs = (els,ctx), rhs = (ident,ctx) }
    ] in
    let cstrs =
      match t.target with TmVar tv then
        let target = name2int im tv.info tv.ident in
        let targetCtx = ctxEnvLookup im tv.info target env in
        foldl (lam acc. lam f.
            concat (f (ident,ctx) (target, targetCtx) t.pat) acc
          ) cstrs mcgfs
      else errorSingle [infoTm t.target] "Not a TmVar in match target"
    in
    -- Add the names bound in the pattern to the environment
    let names = map (name2int im t.info) (patNames [] t.pat) in
    let env = foldl (lam acc. lam n. ctxEnvAdd n ctx acc) env names in
    (ctxEnvAdd ident ctx env, cstrs)

  sem generateMatchConstraints
  : (IName,Ctx) -> (IName,Ctx) -> Pat -> [Constraint]
  sem generateMatchConstraints id target =
  | pat -> [ CstrMatch { id = id, pat = pat, target = target } ]

  -- Returns the set of names bound in a pattern
  sem patNames: [Name] -> Pat -> [Name]
  sem patNames acc =
  | p ->
    sfold_Pat_Pat patNames acc p

end

lang UtestKCFA = KCFA + UtestAst
  sem exprName =
  | TmUtest t -> exprName t.next
end

lang NeverKCFA = KCFA + NeverAst
  -- Nothing to be done here
end

lang ExtKCFA = KCFA + ExtAst

  syn AbsVal =
  -- Abstract representation of externals. Handled in a similar way as
  -- constants. We directly store the external arity in the abstract
  -- value. Note that ANF eta expands all external definitions, so from the
  -- perspective of CFA, externals are curried (need not be fully applied as in
  -- standard MExpr).
  -- NOTE(dlunde,2022-06-15): I'm not convinced the current approach for
  -- handling externals is optimal. The additional `let` added by ANF to shadow
  -- the original external definition is quite clunky. Maybe we can
  -- incorporate the fact that externals are always fully applied into the
  -- analysis somehow?
  | AVExt { ext: (IName,Ctx), arity: Int, args: [(IName,Ctx)] }

  sem absValToString im (env: PprintEnv) =
  | AVExt { ext = ext, args = args } ->
    -- We ignore the arity (one can simply look up the ext to get the arity)
    match mapAccumL (pprintVarINameCtx im) env args with (env,args) in
    let args = strJoin ", " args in
    match pprintVarINameCtx im env ext with (env,ext) in
    (env, join [ext, "(", args, ")"])

  sem cmpAbsValH =
  | (AVExt lhs, AVExt rhs) ->
    -- We ignore the arity (if ext is the same, arity is the same)
    let cmp = cmpINameCtx lhs.ext rhs.ext in
    if eqi 0 cmp then seqCmp cmpINameCtx lhs.args rhs.args
    else cmp

  syn Constraint =
  -- {ext args} ⊆ lhs ⇒ {ext args lhs} ⊆ res
  | CstrExtApp { lhs: (IName,Ctx),
                 rhs : (IName,Ctx),
                 res: (IName,Ctx) }

  sem cmpConstraintH =
  | (CstrExtApp { lhs = lhs1, rhs = rhs1, res = res1 },
     CstrExtApp { lhs = lhs2, rhs = rhs2, res = res2 }) ->
     let d = cmpINameCtx res1 res2 in
     if eqi d 0 then
       let d = cmpINameCtx lhs1 lhs2 in
       if eqi d 0 then cmpINameCtx rhs1 rhs2
       else d
     else d

  sem initConstraint (graph: CFAGraph) =
  | CstrExtApp r & cstr -> initConstraintName r.lhs graph cstr

  sem propagateConstraint update graph =
  | CstrExtApp { lhs = lhs, rhs = rhs, res = res } ->
    match update.2
    with AVExt ({ ext = ext, args = args, arity = arity } & ave) then
      let args = snoc args rhs in
      if eqi arity (length args) then
        -- Last application
        -- TODO(dlunde,2022-06-15): We currently do nothing here. Optimally, we
        -- would like to delegate to a `propagateConstraintExt` here, similar
        -- to constants. I'm not sure where/how `propagateConstraintExt` should
        -- be defined.
        graph
      else
        -- Curried application, add the new argument
        addData graph (AVExt { ave with args = args }) res
    else graph

  -- This ensures that `collectConstraints` does _not_ try to collect constraints
  -- from `let`s immediately following externals. These `let`s are generated by
  -- the ANF transform and define eta expanded versions of the externals (so
  -- that they can be curried).
  sem collectConstraints ctx cgfs acc =
  | TmExt { inexpr = TmLet { ident = ident, inexpr = inexpr } } & t ->
    let acc = foldl (lam acc. lam f.
        match acc with (env, cstrs) in
        match f ctx env t with (env, fcstrs) in
        (env, concat fcstrs cstrs)
      ) acc cgfs in
    collectConstraints ctx cgfs acc inexpr

  sem generateConstraints im ctx env =
  | TmExt { inexpr = TmLet { ident = ident, inexpr = inexpr } } ->
    -- NOTE(dlunde,2022-06-15): Currently, we do not generate any constraints
    -- for externals. Similarly to constants, we probably want to delegate to
    -- `generateConstraintsExts` here. As with `propagateConstraintExt`, it is
    -- not clear where the `generateConstraintsExts` function should be defined.
    --
    (env,[])

  sem exprName =
  -- Skip the eta expanded let added by ANF,
  | TmExt { inexpr = TmLet { inexpr = inexpr }} -> exprName inexpr

end

---------------
-- CONSTANTS --
---------------
-- Most data-flow constraints will need to add data-flow components related to
-- constants (e.g., abstract values for positive and negative integers).
-- However, in this base version of k-CFA, only some data flow constraints are
-- generated.

-- To add data-flow constraints to a constant:
-- 1. Implement 'generateConstraintsConst' fot the constant.
-- 2. Implement 'propagateConstraintConst' for the constant.

lang IntKCFA = KCFA + ConstKCFA + IntAst
  sem generateConstraintsConst info ident =
  | CInt _ -> []
end

lang ArithIntKCFA = KCFA + ConstKCFA + ArithIntAst
  sem generateConstraintsConst info ident =
  | CAddi _ -> []
  | CSubi _ -> []
  | CMuli _ -> []
  | CDivi _ -> []
  | CNegi _ -> []
  | CModi _ -> []
end

lang ShiftIntKCFA = KCFA + ConstKCFA + ShiftIntAst
  sem generateConstraintsConst info ident =
  | CSlli _ -> []
  | CSrli _ -> []
  | CSrai _ -> []
end

lang FloatKCFA = KCFA + ConstKCFA + FloatAst
  sem generateConstraintsConst info ident =
  | CFloat _ -> []
end

lang ArithFloatKCFA = KCFA + ConstKCFA + ArithFloatAst
  sem generateConstraintsConst info ident =
  | CAddf _ -> []
  | CSubf _ -> []
  | CMulf _ -> []
  | CDivf _ -> []
  | CNegf _ -> []
end

lang FloatIntConversionKCFA = KCFA + ConstKCFA + FloatIntConversionAst
  sem generateConstraintsConst info ident =
  | CFloorfi _ -> []
  | CCeilfi _ -> []
  | CRoundfi _ -> []
  | CInt2float _ -> []
end

lang BoolKCFA = KCFA + ConstKCFA + BoolAst
  sem generateConstraintsConst info ident =
  | CBool _ -> []
end

lang CmpIntKCFA = KCFA + ConstKCFA + CmpIntAst
  sem generateConstraintsConst info ident =
  | CEqi _ -> []
  | CNeqi _ -> []
  | CLti _ -> []
  | CGti _ -> []
  | CLeqi _ -> []
  | CGeqi _ -> []
end

lang CmpFloatKCFA = KCFA + ConstKCFA + CmpFloatAst
  sem generateConstraintsConst info ident =
  | CEqf _ -> []
  | CLtf _ -> []
  | CLeqf _ -> []
  | CGtf _ -> []
  | CGeqf _ -> []
  | CNeqf _ -> []
end

lang CharKCFA = KCFA + ConstKCFA + CharAst
  sem generateConstraintsConst info ident =
  | CChar _ -> []
end

lang CmpCharKCFA = KCFA + ConstKCFA + CmpCharAst
  sem generateConstraintsConst info ident =
  | CEqc _ -> []
end

lang IntCharConversionKCFA = KCFA + ConstKCFA + IntCharConversionAst
  sem generateConstraintsConst info ident =
  | CInt2Char _ -> []
  | CChar2Int _ -> []
end

lang FloatStringConversionKCFA = KCFA + ConstKCFA + FloatStringConversionAst
  sem generateConstraintsConst info ident =
  | CStringIsFloat _ -> []
  | CString2float _ -> []
  | CFloat2string _ -> []
end

lang SymbKCFA = KCFA + ConstKCFA + SymbAst
  sem generateConstraintsConst info ident =
  | CSymb _ -> []
  | CGensym _ -> []
  | CSym2hash _ -> []
end

lang CmpSymbKCFA = KCFA + ConstKCFA + CmpSymbAst
  sem generateConstraintsConst info ident =
  | CEqsym _ -> []
end

lang SeqOpKCFA = KCFA + ConstKCFA + SeqKCFA + SeqOpAst + KBaseConstraint
               + LamKCFA

  syn Constraint =
  -- [{names}] ⊆ lhs ⇒ ∀n ∈ names: {n} ⊆ rhs
  | CstrSeq {lhs : (IName,Ctx), rhs : (IName,Ctx)}
  -- [{names}] ⊆ lhs ⇒ [{names} ∪ {rhs}] ⊆ res
  | CstrSeqUnion {lhs : (IName,Ctx),
                  rhs : (IName,Ctx),
                  res : (IName,Ctx)}
  -- [{names}] ∈ seq ⇒ [{f n : n ∈ names}] ∈ res
  | CstrSeqMap1 {seq: (IName,Ctx), f: (IName,Ctx), res: (IName,Ctx)}
  -- {lam x. b} ⊆ f ⇒ (names ⊆ x and [{b}] ∈ res)
  | CstrSeqMap2 {f: (IName,Ctx), names: Set (IName,Ctx), res: (IName,Ctx)}

  -- CstrSeqFold<n> implements foldl when left = true, and foldr otherwise
  -- l: [{names}] ∈ seq ⇒ [{f acc n : n ∈ names}] ∈ res
  -- r: [{names}] ∈ seq ⇒ [{f n acc : n ∈ names}] ∈ res
  | CstrSeqFold1 { seq: (IName,Ctx), f: (IName,Ctx), acc: (IName,Ctx),
                   res: (IName,Ctx), left: Bool }
  -- l: {lam x. b} ⊆ f ⇒ (acc ⊆ x and {lam y. c} ⊆ b ⇒ (names ⊆ y and c ⊆ res))
  -- r: {lam x. b} ⊆ f ⇒ (names ⊆ x and {lam y. c} ⊆ b ⇒ (acc ⊆ y and c ⊆ res))
  | CstrSeqFold2 { f: (IName,Ctx), acc: (IName,Ctx), names: Set (IName,Ctx),
                   res: (IName,Ctx), left: Bool }
  -- {lam x. b} ⊆ f ⇒ (names ⊆ x and b ⊆ res)
  | CstrSeqFold3 { f: (IName,Ctx), names: Set (IName,Ctx), res: (IName,Ctx) }

  sem cmpConstraintH =
  | (CstrSeq { lhs = lhs1, rhs = rhs1 },
     CstrSeq { lhs = lhs2, rhs = rhs2 }) ->
     let d = cmpINameCtx lhs1 lhs2 in
     if eqi d 0 then cmpINameCtx rhs1 rhs2
     else d
  | (CstrSeqUnion { lhs = lhs1, rhs = rhs1, res = res1 },
     CstrSeqUnion { lhs = lhs2, rhs = rhs2, res = res2 }) ->
     let d = cmpINameCtx res1 res2 in
     if eqi d 0 then
       let d = cmpINameCtx lhs1 lhs2 in
       if eqi d 0 then cmpINameCtx rhs1 rhs2
       else d
     else d
  | (CstrSeqMap1 { seq = seq1, f = f1, res = res1 },
     CstrSeqMap1 { seq = seq2, f = f2, res = res2 }) ->
     let d = cmpINameCtx res1 res2 in
     if eqi d 0 then
       let d = cmpINameCtx seq1 seq2 in
       if eqi d 0 then cmpINameCtx f1 f2
       else d
     else d
  | (CstrSeqMap2 { f = f1, names = names1, res = res1 },
     CstrSeqMap2 { f = f2, names = names2, res = res2 }) ->
     let d = cmpINameCtx res1 res2 in
     if eqi d 0 then
       let d = cmpINameCtx f1 f2 in
       if eqi d 0 then setCmp names1 names2
       else d
     else d
  | (CstrSeqFold1 { seq = seq1, f = f1, acc = acc1, res = res1, left = l1 },
     CstrSeqFold1 { seq = seq2, f = f2, acc = acc2, res = res2, left = l2 }) ->
     let d = cmpINameCtx res1 res2 in
     if eqi d 0 then
       let d = cmpINameCtx seq1 seq2 in
       if eqi d 0 then
         let d = cmpINameCtx acc1 acc2 in
         if eqi d 0 then
           let d = cmpINameCtx f1 f2 in
           if eqi d 0 then cmpBool l1 l2
           else d
         else d
       else d
     else d
  | (CstrSeqFold2 { f = f1, acc = acc1, names = names1, res = res1, left = l1 },
     CstrSeqFold2 { f = f2, acc = acc2, names = names2, res = res2, left = l2 }) ->
     let d = cmpINameCtx res1 res2 in
     if eqi d 0 then
       let d = cmpINameCtx acc1 acc2 in
       if eqi d 0 then
         let d = cmpINameCtx f1 f2 in
         if eqi d 0 then
           let d = setCmp names1 names2 in
           if eqi d 0 then cmpBool l1 l2
           else d
         else d
       else d
     else d
  | (CstrSeqFold3 { f = f1, names = names1, res = res1 },
     CstrSeqFold3 { f = f2, names = names2, res = res2 }) ->
     let d = cmpINameCtx res1 res2 in
     if eqi d 0 then
       let d = cmpINameCtx f1 f2 in
       if eqi d 0 then setCmp names1 names2
       else d
     else d

  sem initConstraint (graph: CFAGraph) =
  | CstrSeq r & cstr -> initConstraintName r.lhs graph cstr
  | CstrSeqUnion r & cstr -> initConstraintName r.lhs graph cstr
  | CstrSeqMap1 r & cstr -> initConstraintName r.seq graph cstr
  | CstrSeqMap2 r & cstr -> initConstraintName r.f graph cstr
  | CstrSeqFold1 r & cstr -> initConstraintName r.seq graph cstr
  | CstrSeqFold2 r & cstr -> initConstraintName r.f graph cstr
  | CstrSeqFold3 r & cstr -> initConstraintName r.f graph cstr

  sem constraintToString im (env: PprintEnv) =
  | CstrSeq { lhs = lhs, rhs = rhs } ->
    match pprintVarINameCtx im env lhs with (env,lhs) in
    match pprintVarINameCtx im env rhs with (env,rhs) in
    (env, join [ "[{names}] ⊆ ", lhs, " ⇒ ∀n ∈ names: {n} ⊆ ", rhs ])
  | CstrSeqUnion { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarINameCtx im env lhs with (env,lhs) in
    match pprintVarINameCtx im env rhs with (env,rhs) in
    match pprintVarINameCtx im env res with (env,res) in
    (env, join [
        "[{names}] ⊆ ", lhs, " ⇒ [{names} ∪ { ", rhs," }] ⊆ ", res
      ])
  | CstrSeqMap1 { seq = seq, f = f, res = res } ->
    match pprintVarINameCtx im env seq with (env,seq) in
    match pprintVarINameCtx im env f with (env,f) in
    match pprintVarINameCtx im env res with (env,res) in
    (env, join [
        "[{names}] ∈ ", seq, " ⇒ [{", f, " n : n ∈ names}] ∈ ", res
      ])
  | CstrSeqMap2 { f = f, names = names, res = res } ->
    match pprintVarINameCtx im env f with (env,f) in
    match mapAccumL (pprintVarINameCtx im) env (setToSeq names)
    with (env,names) in
    match pprintVarINameCtx im env res with (env,res) in
    (env, join [
        "{lam x. b} ⊆ ", f, " ⇒ {", strJoin ", " names, "} ⊆ x AND ",
        "[{b}] ∈ ", res
      ])
  | CstrSeqFold1 { seq = seq, f = f, acc = acc, res = res, left = left } ->
    match pprintVarINameCtx im env seq with (env,seq) in
    match pprintVarINameCtx im env f with (env,f) in
    match pprintVarINameCtx im env acc with (env,acc) in
    match pprintVarINameCtx im env res with (env,res) in
    let app = if left then [" ", acc, " n"] else [" n ", acc] in
    (env, join [
        "[{names}] ∈ ", seq, " ⇒ [{", f, join app, " : n ∈ names}] ∈ ", res
      ])
  | CstrSeqFold2 { f = f, acc = acc, names = names, res = res, left = left } ->
    match pprintVarINameCtx im env f with (env,f) in
    match pprintVarINameCtx im env acc with (env,acc) in
    match mapAccumL (pprintVarINameCtx im) env (setToSeq names)
    with (env,names) in
    match pprintVarINameCtx im env res with (env,res) in
    let args =
      if left then (acc, join ["{", strJoin ", " names, "}"])
      else (join ["{", strJoin ", " names, "}"], acc) in
    (env, join [
        "{lam x. b} ⊆ ", f, " ⇒ ", args.0, " ⊆ x AND ",
        "{lam y. c} ⊆ b ⇒ ", args.1, " ⊆ y AND {c} ⊆ ", res
      ])
  | CstrSeqFold3 { f = f, names = names, res = res } ->
    match pprintVarINameCtx im env f with (env,f) in
    match mapAccumL (pprintVarINameCtx im) env (setToSeq names)
    with (env,names) in
    match pprintVarINameCtx im env res with (env,res) in
    (env, join [
        "{lam x. b} ⊆ ", f, " ⇒ {", (strJoin ", " names), "} ⊆ x AND ",
        "b ⊆ ", res
      ])

  sem propagateConstraint update graph =
  | CstrSeq { lhs = lhs, rhs = rhs } ->
    match update.2 with AVSeq { names = names } then
      setFold (lam graph. lam name.
          initConstraint graph (CstrDirect {lhs = name, rhs = rhs})
        ) graph names
    else graph
  | CstrSeqUnion { lhs = lhs, rhs = rhs, res = res } ->
    match update.2 with AVSeq { names = names } then
      addData graph (AVSeq {names = setInsert rhs names}) res
    else graph
  | CstrSeqMap1 { seq = seq, f = f, res = res } ->
    match update.2 with AVSeq { names = names } then
      initConstraint graph (CstrSeqMap2 { f = f, names = names, res = res })
    else graph
  | CstrSeqMap2 { f = f, names = names, res = res } ->
    match update.2 with AVLam { ident = x, bident = b, body = body, env = env }
    then
      -- All calls to 'f' within the map get the same context
      let ctxBody = res.1 in
      let envBody = ctxEnvAdd x ctxBody env in
      -- Analyze the lambda body
      match initConstraints ctxBody envBody graph body with (envBody, graph) in
      -- Add names ⊆ x constraints
      let graph = setFold (lam graph. lam n.
          initConstraint graph (CstrDirect { lhs = n, rhs = (x, ctxBody) })
        ) graph names in
      -- Add [{b}] ⊆ res constraint
      let ctx = ctxEnvLookup graph.im (infoTm body) b envBody in
      initConstraint graph (CstrInit {
        lhs = AVSeq { names = setOfSeq cmpINameCtx [(b, ctx)]},
        rhs = res })
    else graph
  | CstrSeqFold1 { seq = seq, f = f, acc = acc, res = res, left = left } ->
    match update.2 with AVSeq { names = names } then
      initConstraint graph (
        CstrSeqFold2 { f = f, acc = acc, names = names, res = res, left = left }
      )
    else graph
  | CstrSeqFold2 { f = f, acc = acc, names = names, res = res, left = left } ->
    match update.2 with AVLam { ident = x, bident = b, body = body, env = env }
    then
      let ctxBody = res.1 in
      let envBody = ctxEnvAdd x ctxBody env in
      -- Analyze the lambda body
      match initConstraints ctxBody envBody graph body with (envBody, graph) in
      let ctxBident = ctxEnvLookup graph.im (infoTm body) b envBody in
      if left then
        -- Add acc ⊆ x constraint
        let graph = initConstraint graph (CstrDirect {
          lhs = acc, rhs = (x, ctxBody) }) in
        initConstraint graph (CstrSeqFold3 {
          f = (b, ctxBident), names = names, res = res})
      else
        -- Add names ⊆ x constraint
        let graph = setFold (lam graph. lam n.
            initConstraint graph (CstrDirect { lhs = n, rhs = (x, ctxBody) })
          ) graph names in
        initConstraint graph (CstrSeqFold3 {
          f = (b, ctxBident), names = setOfSeq cmpINameCtx [acc], res = res})
    else graph
  | CstrSeqFold3 { f = f, names = names, res = res } ->
    match update.2 with AVLam { ident = x, bident = b, body = body, env = env }
    then
      let ctxBody = res.1 in
      let envBody = ctxEnvAdd x ctxBody env in
      -- Analyze the lambda body
      match initConstraints ctxBody envBody graph body with (envBody, graph) in
      let ctxBident = ctxEnvLookup graph.im (infoTm body) b envBody in
      -- Add names ⊆ x constraints
      let graph = setFold (lam graph. lam n.
          initConstraint graph (CstrDirect { lhs = n, rhs = (x, ctxBody) })
        ) graph names in
      -- Add b ⊆ res constraint
      initConstraint graph (CstrDirect { lhs = (b, ctxBident), rhs = res })
    else graph

  sem generateConstraintsConst info ident =
  | ( CSet _
    | CGet _
    | CCons _
    | CSnoc _
    | CConcat _
    | CReverse _
    | CHead _
    | CTail _
    | CSubsequence _
    | CFoldl _
    | CFoldr _
    | CMap _
    ) & const ->
    [
      CstrInit {
        lhs = AVConst { id = ident, const = const, args = []}, rhs = ident
      }
    ]

  | ( CLength _
    | CNull _
    | CIsList _
    | CIsRope _
    ) -> []

  -- TODO(Linnea, 2022-05-13): Add flow constraints to all sequence operations
  -- | ( CMapi _
  --   | CIter _
  --   | CIteri _
  --   | CCreate _
  --   | CCreateList _
  --   | CCreateRope _
  --   | CSplitAt _
  --   ) -> []

  sem propagateConstraintConst res args graph =
  | CSet _ ->
    utest length args with 3 in
    let seq = get args 0 in
    let val = get args 2 in
    initConstraint graph (CstrSeqUnion {lhs = seq, rhs = val, res = res})
  | CGet _ ->
    utest length args with 2 in
    initConstraint graph (CstrSeq {lhs = head args, rhs = res})
  | CCons _ ->
    utest length args with 2 in
    let val = get args 0 in
    let seq = get args 1 in
    initConstraint graph (CstrSeqUnion {lhs = seq, rhs = val, res = res})
  | CSnoc _ ->
    utest length args with 2 in
    let seq = get args 0 in
    let val = get args 1 in
    initConstraint graph (CstrSeqUnion {lhs = seq, rhs = val, res = res})
  | CConcat _ ->
    utest length args with 2 in
    let graph = initConstraint graph (CstrDirect {lhs = head args, rhs = res}) in
    initConstraint graph (CstrDirect {lhs = get args 1, rhs = res})
  | CReverse _ ->
    utest length args with 1 in
    initConstraint graph (CstrDirect {lhs = head args, rhs = res})
  | CHead _ ->
    utest length args with 1 in
    initConstraint graph (CstrSeq {lhs = head args, rhs = res})
  | CTail _ ->
    utest length args with 1 in
    initConstraint graph (CstrDirect {lhs = head args, rhs = res})
  | CSubsequence _ ->
    utest length args with 3 in
    initConstraint graph (CstrDirect {lhs = head args, rhs = res})
  | CMap _ ->
    utest length args with 2 in
    initConstraint graph (
      CstrSeqMap1 {seq = get args 1, f = head args, res = res})
  | CFoldl _ ->
    utest length args with 3 in
    let seq = get args 2 in
    let f = head args in
    let acc = get args 1 in
    -- Add acc ⊆ res constraint
    let graph = initConstraint graph (CstrDirect { lhs = acc, rhs = res }) in
    initConstraint graph (CstrSeqFold1 {
      seq = seq, f = f, acc = acc, res = res, left = true})
  | CFoldr _ ->
    utest length args with 3 in
    let seq = get args 2 in
    let f = head args in
    let acc = get args 1 in
    -- Add acc ⊆ res constraint
    let graph = initConstraint graph (CstrDirect { lhs = acc, rhs = res }) in
    initConstraint graph (CstrSeqFold1 {
      seq = seq, f = f, acc = acc, res = res, left = false})

end

lang FileOpKCFA = KCFA + ConstKCFA + FileOpAst
  sem generateConstraintsConst info ident =
  | CFileRead _ -> []
  | CFileWrite _ -> []
  | CFileExists _ -> []
  | CFileDelete _ -> []
end

lang IOKCFA = KCFA + ConstKCFA + IOAst
  sem generateConstraintsConst info ident =
  | CPrint _ -> []
  | CPrintError _ -> []
  | CDPrint _ -> []
  | CFlushStdout _ -> []
  | CFlushStderr _ -> []
  | CReadLine _ -> []
  | CReadBytesAsString _ -> []
end

lang RandomNumberGeneratorKCFA = KCFA + ConstKCFA + RandomNumberGeneratorAst
  sem generateConstraintsConst info ident =
  | CRandIntU _ -> []
  | CRandSetSeed _ -> []
end

lang SysKCFA = KCFA + ConstKCFA + SysAst
  sem generateConstraintsConst info ident =
  | CExit _ -> []
  | CError _ -> []
  | CArgv _ -> []
  | CCommand _ -> []
end

lang TimeKCFA = KCFA + ConstKCFA + TimeAst
  sem generateConstraintsConst info ident =
  | CWallTimeMs _ -> []
  | CSleepMs _ -> []
end

lang ConTagKCFA = KCFA + ConstKCFA + ConTagAst
  sem generateConstraintsConst info ident =
  | CConstructorTag _ -> []
end

-- TODO(dlunde,2021-11-11): Mutability complicates the analysis, but could
-- probably be added.
lang RefOpKCFA = KCFA + ConstKCFA + RefOpAst
  sem generateConstraintsConst info ident =
  -- | CRef _ -> []
  -- | CModRef _ -> []
  -- | CDeRef _ -> []
end

-- TODO(dlunde,2021-11-11): Mutability complicates the analysis, but could
-- probably be added.
lang TensorOpKCFA = KCFA + ConstKCFA + TensorOpAst
  sem generateConstraintsConst info ident =
  -- | CTensorCreateUninitInt _ -> []
  -- | CTensorCreateUninitFloat _ -> []
  -- | CTensorCreateInt _ -> []
  -- | CTensorCreateFloat _ -> []
  -- | CTensorCreate _ -> []
  -- | CTensorGetExn _ -> []
  -- | CTensorSetExn _ -> []
  -- | CTensorLinearGetExn _ -> []
  -- | CTensorLinearSetExn _ -> []
  -- | CTensorRank _ -> []
  -- | CTensorShape _ -> []
  -- | CTensorReshapeExn _ -> []
  -- | CTensorCopy _ -> []
  -- | CTensorTransposeExn _ -> []
  -- | CTensorSliceExn _ -> []
  -- | CTensorSubExn _ -> []
  -- | CTensorIterSlice _ -> []
  -- | CTensorEq _ -> []
  -- | CTensorToString _ -> []
end

lang BootParserKCFA = KCFA + ConstKCFA + BootParserAst
  sem generateConstraintsConst info ident =
  | CBootParserParseMExprString _ -> []
  | CBootParserParseMLangString _ -> []
  | CBootParserParseMLangFile _ -> []
  | CBootParserParseMCoreFile _ -> []
  | CBootParserGetId _ -> []
  | CBootParserGetTerm _ -> []
  | CBootParserGetTop _ -> []
  | CBootParserGetDecl _ -> []
  | CBootParserGetType _ -> []
  | CBootParserGetString _ -> []
  | CBootParserGetInt _ -> []
  | CBootParserGetFloat _ -> []
  | CBootParserGetListLength _ -> []
  | CBootParserGetConst _ -> []
  | CBootParserGetPat _ -> []
  | CBootParserGetInfo _ -> []
end

--------------
-- PATTERNS --
--------------

lang NamedPatKCFA = MatchKCFA + NamedPat + KBaseConstraint
  sem propagateMatchConstraint graph (id: (IName,Ctx)) =
  | (PatNamed { ident = PName n, info = info }, av) ->
    -- OPT(Linnea,2022-06-29): Can we avoid doing name2int every time here?
    propagateDirectConstraint (name2int graph.im info n, id.1) graph av
  | (PatNamed { ident = PWildcard _ }, _) -> graph

  sem patNames acc =
  | PatNamed { ident = PName n } -> cons n acc
end

lang SeqTotPatKCFA = MatchKCFA + SeqKCFA + SeqTotPat
  sem propagateMatchConstraint graph (id: (IName,Ctx)) =
  | (PatSeqTot p, AVSeq { names = names }) ->
    let f = lam graph. lam pat: Pat. setFold (lam graph: CFAGraph. lam name.
        let cstrs =
          foldl (lam acc. lam f. concat (f id name pat) acc) [] graph.mcgfs
        in
        foldl initConstraint graph cstrs
      ) graph names in
    foldl f graph p.pats
end

lang SeqEdgePatKCFA = MatchKCFA + SeqKCFA + SeqEdgePat
  sem propagateMatchConstraint graph (id: (IName,Ctx)) =
  | (PatSeqEdge p, AVSeq { names = names } & av) ->
    let f = lam graph. lam pat: Pat. setFold (lam graph: CFAGraph. lam name.
        let cstrs = foldl (lam acc. lam f. concat (f id name pat) acc)
          [] graph.mcgfs in
        foldl initConstraint graph cstrs
      ) graph names in
    let graph = foldl f graph p.prefix in
    let graph = foldl f graph p.postfix in
    match p.middle with PName rhs
    then addData graph av (name2int graph.im p.info rhs, id.1)
    else graph
  | (PatSeqEdge p, av) ->
    match p.middle with PName rhs
    then addData graph av (name2int graph.im p.info rhs, id.1)
    else graph

  sem patNames acc =
  | PatSeqEdge { middle = PName n } & p ->
    sfold_Pat_Pat patNames (cons n acc) p
end

lang RecordPatKCFA = MatchKCFA + RecordKCFA + RecordPat
  sem propagateMatchConstraint graph id =
  | (PatRecord { bindings = pbindings }, AVRec { bindings = abindings }) ->
    -- Check if record pattern is compatible with abstract value record
    let compatible = mapAllWithKey (lam k. lam. mapMem k abindings) pbindings in
    if compatible then
      mapFoldWithKey (lam graph: CFAGraph. lam k. lam pb: Pat.
        let ab: (IName,Ctx) = mapFindExn k abindings in
        let cstrs = foldl (lam acc. lam f. concat (f id ab pb) acc)
          [] graph.mcgfs in
        foldl initConstraint graph cstrs
      ) graph pbindings
    else graph -- Nothing to be done
end

lang DataPatKCFA = MatchKCFA + DataKCFA + DataPat
  sem propagateMatchConstraint graph id =
  | (PatCon p, AVCon { ident = ident, body = body }) ->
    if nameEq p.ident (int2name graph.im ident.0) then
      let cstrs = foldl (lam acc. lam f. concat (f id body p.subpat) acc)
        [] graph.mcgfs in
      foldl initConstraint graph cstrs
    else graph
end

lang IntPatKCFA = MatchKCFA + IntPat
  sem propagateMatchConstraint graph id =
  | (PatInt p, _) -> graph
end

lang CharPatKCFA = MatchKCFA + CharPat
  sem propagateMatchConstraint graph id =
  | (PatChar p, _) -> graph
end

lang BoolPatKCFA = MatchKCFA + BoolPat
  sem propagateMatchConstraint graph id =
  | (PatBool p, _) -> graph
end

lang AndPatKCFA = MatchKCFA + AndPat
  sem propagateMatchConstraint graph id =
  | (PatAnd p, av) ->
    let graph = propagateMatchConstraint graph id (p.lpat, av) in
    propagateMatchConstraint graph id (p.rpat, av)
end

lang OrPatKCFA = MatchKCFA + OrPat
  sem propagateMatchConstraint graph id =
  | (PatOr p, av) ->
    let graph = propagateMatchConstraint graph id (p.lpat, av) in
    propagateMatchConstraint graph id (p.rpat, av)
end

lang NotPatKCFA = MatchKCFA + NotPat
  sem propagateMatchConstraint graph id =
  | (PatNot p, _) -> graph
end

-----------------
-- MEXPR k-CFA --
-----------------

lang MExprKCFA = KCFA +

  -- Base constraints
  KBaseConstraint +

  -- Terms
  VarKCFA + LamKCFA + AppKCFA +
  LetKCFA + RecLetsKCFA + ConstKCFA + SeqKCFA + RecordKCFA + TypeKCFA + DataKCFA +
  MatchKCFA + UtestKCFA + NeverKCFA + ExtKCFA +

  -- Constants
  IntKCFA + ArithIntKCFA + ShiftIntKCFA + FloatKCFA + ArithFloatKCFA +
  FloatIntConversionKCFA + BoolKCFA + CmpIntKCFA + CmpFloatKCFA + CharKCFA +
  CmpCharKCFA + IntCharConversionKCFA + FloatStringConversionKCFA + SymbKCFA +
  CmpSymbKCFA + SeqOpKCFA + FileOpKCFA + IOKCFA + RandomNumberGeneratorKCFA +
  SysKCFA + TimeKCFA + ConTagKCFA + RefOpKCFA + TensorOpKCFA + BootParserKCFA +

  -- Patterns
  NamedPatKCFA + SeqTotPatKCFA + SeqEdgePatKCFA + RecordPatKCFA + DataPatKCFA +
  IntPatKCFA + CharPatKCFA + BoolPatKCFA + AndPatKCFA + OrPatKCFA + NotPatKCFA

  -- Function that adds a set of universal base match constraints to a CFAGraph
  sem addBaseMatchConstraints =
  | graph ->
    { graph with mcgfs = concat [generateMatchConstraints] graph.mcgfs }

  -- Function that adds a set of universal base constraints to a CFAGraph
  sem addBaseConstraints =
  | graph ->
    let cgfs = [ generateConstraints graph.im,
                 generateConstraintsMatch graph.im graph.mcgfs ] in
    { graph with cgfs = concat cgfs graph.cgfs }

  -- Function that initializes the constraints in a CFAGraph for an empty
  -- context and context environment
  sem initConstraintsEmpty: CFAGraph -> Expr -> CFAGraph
  sem initConstraintsEmpty graph =
  | t ->
    match initConstraints (ctxEmpty ()) (ctxEnvEmpty ()) graph t with (_, graph)
    in graph

end

-----------------
-- TESTS k-CFA --
-----------------

lang KTest = MExprKCFA + MExprANFAll + BootParser + MExprPrettyPrint

  sem testCfa : Int -> Expr -> CFAGraph
  sem testCfa k =
  | t ->
    let graph = emptyCFAGraph k t in
    let graph = addBaseMatchConstraints graph in
    let graph = addBaseConstraints graph in
    let graph = initConstraintsEmpty graph t in
    solveCfa graph

  sem testCfaDebug : PprintEnv -> Int -> Expr -> (PprintEnv, CFAGraph)
  sem testCfaDebug pprintenv k =
  | t ->
    let graph = emptyCFAGraph k t in
    let graph = addBaseMatchConstraints graph in
    let graph = addBaseConstraints graph in
    let graph = initConstraintsEmpty graph t in
    solveCfaDebug pprintenv graph

end

mexpr

-----------------
-- TESTS k-CFA --
-----------------

use KTest in

-- Test functions --
let _parse = parseMExprStringKeywordsExn [] in
let _testBase: Option PprintEnv -> Int -> Expr -> (Option PprintEnv, CFAGraph) =
  lam env: Option PprintEnv. lam k. lam t: Expr.
    match env with Some env then
      -- Version with debug printouts
      let tANF = normalizeTerm t in
      match pprintCode 0 env t with (env,tStr) in
      printLn "\n--- ORIGINAL PROGRAM ---";
      printLn tStr;
      match pprintCode 0 env tANF with (env,tANFStr) in
      printLn "\n--- ANF ---";
      printLn tANFStr;
      match testCfaDebug env k tANF with (env,cfaRes) in
      match cfaGraphToString env cfaRes with (env, resStr) in
      printLn "\n--- FINAL CFA GRAPH ---";
      printLn resStr;
      (Some env,cfaRes)

    else
      -- Version without debug printouts
      let tANF = normalizeTerm t in
      let cfaRes = testCfa k tANF in
      (None (), cfaRes)
in

let _test : Bool -> Int -> Expr -> [(String, [String])]
          -> [(String,[String],[String])] =
  lam debug. lam k. lam t. lam vars.
    let env = if debug then Some pprintEnvEmpty else None () in
    match _testBase env k t with (_, cfaRes) in
    let stringMap: Map String Int = mapFoldWithKey (
        lam acc: Map String Int. lam n: Name. lam i: Int.
          mapInsert (nameGetStr n) i acc
      ) (mapEmpty cmpString) cfaRes.im.name2int
    in
    let string2int: String -> Int = lam s. mapFindExn s stringMap in
    let int2string: Int -> String = lam i. nameGetStr (int2name cfaRes.im i) in
    map (lam var: (String, [String]).
      let avs = mapFoldWithKey (lam acc: Set AbsVal. lam ctx. lam avs: Set AbsVal.
          let ctx = map int2string ctx in
          if eqSeq eqString ctx var.1 then avs else acc
        ) (setEmpty cmpAbsVal) (tensorLinearGetExn cfaRes.data (string2int var.0))
      in
      let val = setFold
        (lam acc. lam av.
           match av with AVLam { ident = i } then
             cons (nameGetStr (int2name cfaRes.im i)) acc
           else acc)
        [] avs
      in (var.0, var.1, val)
    ) vars
in

let _test0 : Bool -> Expr -> [String]
          -> [(String,[String],[String])] =
  lam debug. lam t. lam vars.
    _test debug 0 t (map (lam v. (v,[])) vars)
in

-- Custom equality function for testing lambda control flow only
let eqTestLam = eqSeq (
  lam t1:(String,[String],[String]). lam t2:(String,[String],[String]).
    if eqString t1.0 t2.0 then
      if eqSeq eqString t1.1 t2.1 then
        let t12 = setOfSeq cmpString t1.2 in
        let t22 = setOfSeq cmpString t2.2 in
        setEq t12 t22
      else false
    else false)
in

let eqTestLam0 =
  lam t1:[(String,[String],[String])]. lam t2:[(String,[String])].
    let f = map (lam t:(String,[String]). (t.0,[],t.1)) in
    eqTestLam t1 (f t2)
in
--------------------

-- First test from Nielson et al.
let t = _parse "
  (lam x. x) (lam y. y)
------------------------" in
utest _test0 false t ["x","y"] with [
  ("x", ["y"]),
  ("y", [])
] using eqTestLam0 in

-- Second test from Nielson et al.
let t = _parse "
  let f = lam x. x 1 in
  let g = lam y. addi y 2 in
  let h = lam z. addi z 3 in
  let res = addi (f g) (f h) in
  res
------------------------" in
utest _test0 false t ["f","g","h","x","y","z","res"] with [
  ("f", ["x"]),
  ("g", ["y"]),
  ("h", ["z"]),
  ("x", ["y","z"]),
  ("y", []),
  ("z", []),
  ("res", [])
] using eqTestLam0 in

-- Third test from Nielson et al.
let t = _parse "
recursive let g = lam x.
  g (lam y. y)
in
let res = g (lam z. z) in
res
------------------------" in
utest _test0 false t ["g","x","y","z","res"] with [
  ("g", ["x"]),
  ("x", ["y","z"]),
  ("y", []),
  ("z", []),
  ("res", [])
] using eqTestLam0 in

-- Example 3.34 from Nielson et al (0-CFA).
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let a = f f in
  let b = f g in
  b
------------------------" in
utest _test0 false t ["a", "b"] with [
  ("a", ["x", "y"]),
  ("b", ["x", "y"])
] using eqTestLam0 in

-- Example 3.34 from Nielson et al (1-CFA).
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let a = f f in
  let b = f g in
  b
------------------------" in
utest _test false 1 t [("a",[]), ("b",[]), ("x",["a"]), ("x",["b"])] with [
  ("a", [], ["x"]),
  ("b", [], ["y"]),
  ("x", ["a"], ["x"]),
  ("x", ["b"], ["y"])
] using eqTestLam in

-- Third test using 2-CFA
let t = _parse "
let f = lam y. y in
recursive let g = lam x.
  let a = g f in
  a
in
let res = g (lam z. z) in
res
------------------------" in
utest _test false 2 t [
  ("g",[]),
  ("x",["res"]),("x",["res","a"]),("x",["a","a"]),
  ("res", [])
] with [
  ("g", [], ["x"]),
  ("x", ["res"], ["z"]),
  ("x", ["res","a"], ["y"]),
  ("x", ["a","a"], ["y"]),
  ("res", [], [])
] using eqTestLam in

-- 2-CFA
let t = _parse "
let f = lam x. x in
let g = lam y.
  let t = f y in
  t
in
let h = lam z. z in
let a = g h in
let b = g f in
a
------------------------" in
utest _test false 2 t [("a",[]),("b",[]),("x",["a","t"]),("x",["b","t"])] with [
  ("a", [], ["z"]),
  ("b", [], ["x"]),
  ("x", ["a","t"], ["z"]),
  ("x", ["b","t"], ["x"])
] using eqTestLam in

-- Sequence
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let seq = [f, lam z. z] in
  let res = match seq with [a] ++ _ then
      a g
    else
      (lam v. v)
  in res
------------------------" in
utest _test0 false t ["res","a"] with [
  ("res", ["v","y"]),
  ("a", ["x","z"])
] using eqTestLam0 in

-- Sequence operations (basic)
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let s1 = [f, lam z. z] in
  let hd = head in
  let b = hd in
  let resHead = b s1 in
  let s2 = concat s1 [lam v. v] in
  let resConcat = b s2 in
  let s3 = set s1 0 g in
  let resSet = head s3 in
  let resGet = get s1 1 in
  let s4 = cons g s1 in
  let resCons = head s4 in
  let s5 = snoc s1 (lam r. r) in
  let resSnoc = head s5 in
  let resLength = length s1 in
  let s6 = reverse s1 in
  let resReverse = head s6 in
  let s7 = tail s1 in
  let resTail = head s1 in
  let resNull = null s1 in
  let resIsList = isList s1 in
  let resIsRope = isRope s1 in
  let s8 = subsequence s1 0 0 in
  let resSubsequence = head s8 in
  ()
------------------------" in
utest _test0 false t [
  "resHead",
  "resConcat",
  "resSet",
  "resGet",
  "resCons",
  "resSnoc",
  "resLength",
  "resReverse",
  "resTail",
  "resNull",
  "resIsList",
  "resIsRope",
  "resSubsequence"
] with [
  ("resHead", ["x","z"]),
  ("resConcat", ["x","z","v"]),
  ("resSet", ["x","z","y"]),
  ("resGet", ["x","z"]),
  ("resCons", ["x","z","y"]),
  ("resSnoc", ["x","z","r"]),
  ("resLength", []),
  ("resReverse", ["x","z"]),
  ("resTail", ["x","z"]),
  ("resNull", []),
  ("resIsList", []),
  ("resIsRope", []),
  ("resSubsequence", ["x", "z"])
] using eqTestLam0 in

-- Map over sequences
let t = _parse "
  let s1 = map (lam x. x) [lam y. y, lam z. z] in
  let r1 = head s1 in
  let s2 = map (lam a. lam d. d) [lam b. b, lam c. c] in
  let r2 = head s2 in
  ()
------------------------" in
utest _test0 false t ["r1", "r2"] with [
  ("r1", ["y", "z"]),
  ("r2", ["d"])
] using eqTestLam0 in

-- Foldl
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let h = lam z. z in
  let r1 = foldl (lam a1. lam e1. a1) f [g, h] in
  let r2 = foldl (lam a2. lam e2. a2 e2) f [g, h] in
  let r3 = foldl (lam a3. lam e3. a3 e3) (lam w. w) [] in
  ()
------------------------" in
utest _test0 false t ["r1", "r2", "r3"] with [
  ("r1", ["x"]),
  ("r2", ["x", "y", "z"]),
  ("r3", ["w"])
] using eqTestLam0 in

-- Foldr
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let h = lam z. z in
  let r1 = foldr (lam e1. lam a1. a1) f [g, h] in
  let r2 = foldr (lam e2. lam a2. a2 e2) f [g, h] in
  let r3 = foldr (lam e3. lam a3. a3 e3) (lam w. w) [] in
  ()
------------------------" in
utest _test0 false t ["r1", "r2", "r3"] with [
  ("r1", ["x"]),
  ("r2", ["x", "y", "z"]),
  ("r3", ["w"])
] using eqTestLam0 in

-- Record
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let r = { a = f, b = 3 } in
  let res = match r with { a = a } then
      a g
    else
      (lam z. z)
  in res
------------------------" in
utest _test0 false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["x"])
] using eqTestLam0 in

-- Record update
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let h = lam w. w in
  let r1 = { a = f, b = 3 } in
  let r2 = { r1 with a = h } in
  let res = match r2 with { a = a } then
      a g
    else
      (lam z. z)
  in res
------------------------" in
utest _test0 false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["w"])
] using eqTestLam0 in

-- ConApp
let t = _parse "
  type T in
  con C: (a -> a) -> T in
  let f = lam x. x in

  let g = lam y. y in
  let d = C f in
  let res = match d with C a then
      a g
    else
      (lam z. z)
  in res
------------------------" in
utest _test0 false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["x"])
] using eqTestLam0 in

-- Nested
let t = _parse "
  type T in
  con C: (a -> a) -> T in
  let f = lam x. x in
  let g = lam y. y in
  let d = { a = [C f], b = 3 } in
  let res = match d with { a = [C a] } then
      a g
    else
      (lam z. z)
  in res
------------------------" in
utest _test0 false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["x"])
] using eqTestLam0 in

let t = _parse "
  let f = lam x.
    recursive let g = lam y.
      let a = g x in
      a
    in
    let d = g x in
    d
  in
  let b = f (lam z. z) in
  let c = f (lam w. w) in
  c
------------------------" in
utest _test false 3 t [
  ("y", ["b","d","a"]),
  ("y", ["c","d","a"]),
  ("y", ["a","a","a"])
] with [
  ("y", ["b","d","a"], ["z"]),
  ("y", ["c","d","a"], ["w"]),
  ("y", ["a","a","a"], ["z", "w"])
] using eqTestLam in

-- And pattern
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let res =
    match f with a & b then a g
    else (lam z. z)
  in res
------------------------" in
utest _test0 false t ["res", "a", "b"] with [
  ("res", ["y","z"]),
  ("a", ["x"]),
  ("b", ["x"])
] using eqTestLam0 in

-- Or pattern
let t = _parse "
  type T in
  con C1: (a -> a) -> T in
  con C2: (a -> a) -> T in
  let f = lam x. x in
  let g = lam y. y in
  let h = (C1 f, f) in
  let res =
    match h with (C1 _, rhs) | (C2 _, rhs) then rhs g
    else (lam z. z)
  in res
------------------------" in
utest _test0 false t ["res", "rhs"] with [
  ("res", ["y","z"]),
  ("rhs", ["x"])
] using eqTestLam0 in

-- Not pattern
let t = _parse "
  type T in
  con C: (a -> a) -> T in
  let f = lam x. x in
  let g = lam y. y in
  let h = (C f, f) in
  let res =
    match h with ! (C _, rhs) then (lam yy. yy)
    else (lam z. z)
  in
  let res2 =
    match h with ! (C _, rhs) & (_, p) then (lam k. k)
    else (lam w. w)
  in res
------------------------" in
utest _test0 false t ["res", "res2", "p"] with [
  ("res", ["yy","z"]),
  ("res2", ["k","w"]),
  ("p", ["x"])
] using eqTestLam0 in

()
