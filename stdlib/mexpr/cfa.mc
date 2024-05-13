-- 0-CFA framework for MExpr. The algorithm is loosely
-- based on Table 3.7 in the book "Principles of Program Analysis" (Nielson et
-- al.).
--
-- Some details:
-- - Only works on fully labelled terms provided by MExprANFAll (see mexpr/anf.mc).
-- - Uses efficient lazy constraint expansion, and not the static
--   constraints from table 3.7 in Nielson et al. (see p. 202 in Nielson et al.
--   for a discussion about this).
--

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


type IName = Int

-------------------
-- BASE FRAGMENT --
-------------------

lang CFABase = Ast + LetAst + MExprIndex + MExprFreeVars + MExprPrettyPrint

  syn Constraint =
  -- Intentionally left blank

  syn AbsVal =
  -- Intentionally left blank

  syn GraphData =
  -- Intentionally left blank

  -- For a given expression, returns the variable "labeling" that expression.
  -- The existence of such a label is guaranteed by ANF.
  sem exprName: Expr -> Name
  sem exprName =
  | t -> errorSingle [infoTm t] "Error in exprName for CFA"

  -- Required for the data type Set AbsVal
  sem cmpAbsVal: AbsVal -> AbsVal -> Int
  sem cmpAbsVal lhs =
  | rhs -> cmpAbsValH (lhs, rhs)
  sem cmpAbsValH: (AbsVal, AbsVal) -> Int
  sem cmpAbsValH =
  | (lhs, rhs) ->
    let res = subi (constructorTag lhs) (constructorTag rhs) in
    if eqi res 0 then
      error
        "Missing case in cmpAbsValH for abstract values with same constructor."
    else res

  -- Required for the data type Set AbsVal
  sem eqAbsVal (lhs: AbsVal) =
  | rhs -> eqi (cmpAbsVal lhs rhs) 0

  -- Required for the data type Set Constraint
  sem cmpConstraint: Constraint -> Constraint -> Int
  sem cmpConstraint lhs =
  | rhs -> cmpConstraintH (lhs, rhs)
  sem cmpConstraintH: (Constraint, Constraint) -> Int
  sem cmpConstraintH =
  | (lhs, rhs) ->
    let res = subi (constructorTag lhs) (constructorTag rhs) in
    if eqi res 0 then
      error
        "Missing case in cmpConstraintH for constraints with same constructor."
    else res

  --------------------------
  -- NAME-INTEGER MAPPING --
  --------------------------

  sem name2intAcc: IndexAcc -> Info -> Name -> IName
  sem name2intAcc ia info =
  | name ->
    mapLookupOrElse (lam.
        errorSingle [info] (concat "name2intAcc failed: " (nameGetStr name))
      ) name ia.map

  sem name2int: IndexMap -> Info -> Name -> IName
  sem name2int im info =
  | name ->
    mapLookupOrElse (lam.
        errorSingle [info] (concat "name2int failed: " (nameGetStr name))
      ) name im.name2int

  sem int2name: IndexMap -> IName -> Name
  sem int2name im =
  | i -> tensorLinearGetExn im.int2name i

  ---------------------
  -- PRETTY PRINTING --
  ---------------------

  sem pprintVarIName: IndexMap -> PprintEnv -> IName -> (PprintEnv, String)
  sem pprintVarIName im env =
  | n -> pprintVarName env (int2name im n)

  sem pprintConIName: IndexMap -> PprintEnv -> IName -> (PprintEnv, String)
  sem pprintConIName im env =
  | n -> pprintConName env (int2name im n)

  sem constraintToString
  : IndexMap -> PprintEnv -> Constraint -> (PprintEnv, String)

  sem absValToString: IndexMap -> PprintEnv -> AbsVal -> (PprintEnv, String)

end

--------------------
-- 0-CFA FRAGMENT --
--------------------

lang CFA = CFABase

  type MatchGenFun = IName -> IName -> Pat -> [Constraint]
  type ConstPropFun = IName -> [IName] -> [IName] -> Const -> [Constraint]

  type CFAGraph = {

    -- Contains updates that needs to be processed in the main CFA loop
    worklist: [(IName,AbsVal)],

    -- Contains abstract values currently associated with each name in the program.
    data: Tensor[Set AbsVal],

    -- For each name in the program, gives constraints which needs to be
    -- repropagated upon updates to the abstract values for the name.
    edges: Tensor[Set Constraint],

    -- Contains a list of functions used for generating match constraints
    -- TODO(dlunde,2021-11-17): Should be added as a product extension
    -- in the MatchCFA fragment instead, when possible.
    mcgfs: [MatchGenFun],

    -- Constant propagation functions
    -- TODO(dlunde,2023-07-10): Should be added as a product extension
    -- in the MatchCFA fragment instead, when possible.
    cpfs: [ConstPropFun],

    -- Bidirectional mapping between names and integers.
    im: IndexMap,

    -- NOTE(dlunde,2021-11-18): Data needed for analyses based on this framework
    -- must be put below directly, since we do not yet have product extensions.

    -- Used to store any custom data in the graph
    graphData: Option GraphData

  }

  -- Used during CFAGraph construction
  type CFAGraphInit = {
    mcgfs: [MatchGenFun],
    cpfs: [ConstPropFun],
    cstrs: [Constraint],
    ia: IndexAcc,
    graphData: Option GraphData
  }

  type GenFun = CFAGraphInit -> Expr -> CFAGraphInit

  sem emptyCFAGraphInit: Expr -> CFAGraphInit
  sem emptyCFAGraphInit =
  | t -> { mcgfs = [], cpfs = [], cstrs = [], ia = indexAccGen t,
           graphData = None () }

  sem finalizeCFAGraphInit: CFAGraphInit -> CFAGraph
  sem finalizeCFAGraphInit =
  | t ->
    -- NOTE(Linnea,2022-06-22): Experiments have shown that lists are better
    -- than ropes for 'worklist' and 'edges', especially for 'worklist'
    let im = indexClose t.ia in
    let shape = tensorShape im.int2name in
    let elist = toList [] in
    let graph = { worklist = elist,
      data = tensorCreateDense shape (lam. setEmpty cmpAbsVal),
      edges = tensorCreateDense shape (lam. setEmpty cmpConstraint),
      mcgfs = t.mcgfs,
      cpfs = t.cpfs,
      im = im,
      graphData = t.graphData } in
    let graph = foldl initConstraint graph t.cstrs in
    graph


  -- This function converts the data-flow result into a map, which might be more
  -- convenient to operate on for later analysis steps.
  sem cfaGraphData: CFAGraph -> Map Name (Set AbsVal)
  sem cfaGraphData =
  | graph ->
    tensorFoldi (lam acc. lam i: [Int]. lam vals: Set AbsVal.
        mapInsert (int2name graph.im (head i)) vals acc
      ) (mapEmpty nameCmp) graph.data

  -- Main algorithm
  sem solveCfa: CFAGraphInit -> CFAGraph
  sem solveCfa =
  | graph ->
    -- Finalize graph
    let graph = finalizeCFAGraphInit graph in

    -- Iteration
    recursive let iter = lam graph: CFAGraph.
      if null graph.worklist then graph
      else
        match head graph.worklist with (q,d) & h in
        let graph = { graph with worklist = tail graph.worklist } in
        match edgesLookup q graph with cc in
        let graph = setFold (propagateConstraint h) graph cc in
        iter graph
    in
    iter graph

  -- Main algorithm (debug version)
  sem solveCfaDebug : PprintEnv -> CFAGraphInit -> (PprintEnv, CFAGraph)
  sem solveCfaDebug pprintenv =
  | graph ->
    -- NOTE(Linnea,2022-06-22): Experiments have shown that using `cfaDebug` as
    -- the main entry point causes overhead when no printing takes place, as we
    -- have to match on the pprintenv in every iteration. Therefore, some code
    -- duplication takes place here.

    -- Finalize graph
    let graph = finalizeCFAGraphInit graph in

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
        match head graph.worklist with (q,d) & h in
        let graph = { graph with worklist = tail graph.worklist } in
        match edgesLookup q graph with cc in
        let graph = setFold (propagateConstraint h) graph cc in
        iter (addi i 1) pprintenv graph
    in
    iter 1 pprintenv graph

  -- Base constraint generation function (must still be included manually in
  -- constraintGenFuns)
  sem generateConstraints : GenFun
  sem generateConstraints graph =
  | t -> graph

  -- Call a set of constraint generation functions on each term in program.
  -- Useful when defining values of type CFAGraph.
  sem collectConstraints: [GenFun] -> CFAGraphInit -> Expr -> CFAGraphInit
  sem collectConstraints (cgfs: [GenFun]) (graph: CFAGraphInit) =
  | t ->
    let graph = foldl (lam graph. lam f. f graph t) graph cgfs in
    sfold_Expr_Expr (collectConstraints cgfs) graph t

  sem initConstraint: CFAGraph -> Constraint -> CFAGraph

  sem propagateConstraint: (IName,AbsVal) -> CFAGraph -> Constraint -> CFAGraph

  sem propagateConstraintConst: ConstPropFun

  -- Returns both the new graph, and a Boolean that is true iff the new edge was
  -- added to the graph.
  -- NOTE(Linnea, 2022-06-21): Updates the graph by a side effect
  sem addEdge: CFAGraph -> IName -> Constraint -> (CFAGraph, Bool)
  sem addEdge (graph: CFAGraph) (q: IName) =
  | cstr ->
    let cstrsq = edgesLookup q graph in
    if setMem cstr cstrsq then (graph, false)
    else
      tensorLinearSetExn graph.edges q (setInsert cstr cstrsq);
      (graph, true)

  -- Helper function for initializing a constraint for a given name (mainly
  -- used for convenience in initConstraint)
  sem initConstraintName: IName -> CFAGraph -> Constraint -> CFAGraph
  sem initConstraintName (name: IName) (graph: CFAGraph) =
  | cstr ->
    match addEdge graph name cstr with (graph, new) in
    if new then
      let avs = dataLookup name graph in
      setFold (lam graph. lam av. propagateConstraint (name,av) graph cstr)
        graph avs
    else graph

  -- Helper function for initializing a constraint for a given name (mainly
  -- used for convenience in initConstraint)
  sem initConstraintNames: [IName] -> CFAGraph -> Constraint -> CFAGraph
  sem initConstraintNames (names: [IName]) (graph: CFAGraph) =
  | cstr ->
    foldl (lam graph. lam name. initConstraintName name graph cstr) graph names

  sem dataLookup: IName -> CFAGraph -> Set AbsVal
  sem dataLookup (key: IName) =
  | graph -> tensorLinearGetExn graph.data key

  sem edgesLookup (key: IName) =
  | graph -> tensorLinearGetExn graph.edges key

  -- NOTE(Linnea, 2022-06-21): Updates the graph by a side effect
  sem addData: CFAGraph -> AbsVal -> IName -> CFAGraph
  sem addData (graph: CFAGraph) (d: AbsVal) =
  | q ->
    let dq = dataLookup q graph in
    if setMem d dq then graph else
      tensorLinearSetExn graph.data q (setInsert d dq);
      { graph with worklist = cons (q,d) graph.worklist }

  ---------------------
  -- PRETTY PRINTING --
  ---------------------

  -- Prints a CFA graph
  sem cfaGraphToString (env: PprintEnv) =
  | graph ->
    let graph: CFAGraph = graph in
    let f = lam env. lam e: (IName,AbsVal).
      match pprintVarIName graph.im env e.0 with (env,n) in
      match absValToString graph.im env e.1 with (env,av) in
      (env,join ["(", n, ", ", av, ")"]) in
    match mapAccumL f env graph.worklist with (env,worklist) in
    match mapAccumL (lam env: PprintEnv. lam b:(IName,Set AbsVal).
        match pprintVarIName graph.im env b.0 with (env,b0) in
        match mapAccumL (absValToString graph.im) env (setToSeq b.1) with (env,b1)
        in (env,(b0,b1))
      ) env (mapi (lam i. lam x. (i,x)) (tensorToSeqExn graph.data))
    with (env, data) in
    match mapAccumL (lam env: PprintEnv. lam b:(IName,[Constraint]).
        match pprintVarIName graph.im env b.0 with (env,b0) in
        match mapAccumL (constraintToString graph.im) env b.1 with (env,b1) in
        (env,(b0,b1))
      ) env (mapi (lam i. lam x. (i, setToSeq x)) (tensorToSeqExn graph.edges))
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

end

----------------------
-- BASE CONSTRAINTS --
----------------------

lang BaseConstraint = CFA

  syn Constraint =
  -- {lhs} ⊆ rhs
  | CstrInit { lhs: AbsVal, rhs: IName }
  -- lhs ⊆ rhs
  | CstrDirect { lhs: IName, rhs: IName }
  -- {lhsav} ⊆ lhs ⇒ {rhsav} ⊆ rhs
  | CstrDirectAv { lhs: IName, lhsav: AbsVal, rhs: IName, rhsav: AbsVal }
  -- {lhsav} ⊆ lhs ⇒ [rhs]
  | CstrDirectAvCstrs { lhs: IName, lhsav: AbsVal, rhs: [Constraint] }

  sem cmpConstraintH =
  | (CstrInit { lhs = lhs1, rhs = rhs1 },
     CstrInit { lhs = lhs2, rhs = rhs2 }) ->
     let d = cmpAbsVal lhs1 lhs2 in
     if eqi d 0 then subi rhs1 rhs2
     else d
  | (CstrDirect { lhs = lhs1, rhs = rhs1 },
     CstrDirect { lhs = lhs2, rhs = rhs2 }) ->
     let d = subi lhs1 lhs2 in
     if eqi d 0 then subi rhs1 rhs2
     else d
  | (CstrDirectAv t1, CstrDirectAv t2) ->
     let d = subi t1.lhs t2.lhs in
     if eqi d 0 then
       let d = subi t1.rhs t2.rhs in
       if eqi d 0 then
         let d = cmpAbsVal t1.lhsav t2.lhsav in
         if eqi d 0 then cmpAbsVal t1.rhsav t2.rhsav
         else d
       else d
     else d
  | (CstrDirectAvCstrs t1, CstrDirectAvCstrs t2) ->
     let d = subi t1.lhs t2.lhs in
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
    match pprintVarIName im env rhs with (env,rhs) in
    (env, join ["{", lhs, "}", " ⊆ ", rhs])
  | CstrDirect { lhs = lhs, rhs = rhs } ->
    match pprintVarIName im env lhs with (env,lhs) in
    match pprintVarIName im env rhs with (env,rhs) in
    (env, join [lhs, " ⊆ ", rhs])
  | CstrDirectAv { lhs = lhs, lhsav = lhsav, rhs = rhs, rhsav = rhsav } ->
    match pprintVarIName im env lhs with (env,lhs) in
    match absValToString im env lhsav with (env,lhsav) in
    match pprintVarIName im env rhs with (env,rhs) in
    match absValToString im env rhsav with (env,rhsav) in
    (env, join ["{", lhsav ,"} ⊆ ", lhs, " ⇒ {", rhsav ,"} ⊆ ", rhs])
  | CstrDirectAvCstrs { lhs = lhs, lhsav = lhsav, rhs = rhs } ->
    match mapAccumL (constraintToString im) env rhs with (env,rhs) in
    let rhs = strJoin " AND " rhs in
    match pprintVarIName im env lhs with (env,lhs) in
    match absValToString im env lhsav with (env,lhsav) in
    (env, join [ "{", lhsav, "} ⊆ ", lhs, " ⇒ (", rhs, ")" ])

  sem isDirect: AbsVal -> Bool
  sem isDirect =
  | _ -> true

  sem directTransition: CFAGraph -> IName -> AbsVal -> AbsVal
  sem directTransition (graph: CFAGraph) (rhs: IName) =
  | av -> av

  sem propagateConstraint (update: (IName,AbsVal)) (graph: CFAGraph) =
  | CstrDirect r -> propagateDirectConstraint r.rhs graph update.1
  | CstrDirectAv r ->
    if eqAbsVal update.1 r.lhsav then
      addData graph r.rhsav r.rhs
    else graph
  | CstrDirectAvCstrs r & cstr ->
    if eqAbsVal update.1 r.lhsav then
      foldl initConstraint graph r.rhs
    else graph

  sem propagateDirectConstraint: IName -> CFAGraph -> AbsVal -> CFAGraph
  sem propagateDirectConstraint (rhs: IName) (graph: CFAGraph) =
  | av ->
    if isDirect av then
      addData graph (directTransition graph rhs av) rhs
    else graph
end

-----------
-- TERMS --
-----------

lang VarCFA = CFA + BaseConstraint + VarAst

  sem generateConstraints graph =
  | TmLet { ident = ident, body = TmVar t, info = info } ->
    let cstr = CstrDirect {
      lhs = name2intAcc graph.ia t.info t.ident,
      rhs = name2intAcc graph.ia info ident
    } in
    { graph with cstrs = cons cstr graph.cstrs }

  sem exprName =
  | TmVar t -> t.ident

end

lang LamCFA = CFA + BaseConstraint + LamAst

  -- Abstract representation of lambdas.
  syn AbsVal =
  | AVLam { ident: IName, body: IName }

  sem cmpAbsValH =
  | (AVLam { ident = lhs, body = lbody },
     AVLam { ident = rhs, body = rbody }) ->
     let diff = subi lhs rhs in
     if eqi diff 0 then subi lbody rbody else diff

  sem generateConstraints graph =
  | TmLet { ident = ident, body = TmLam t, info = info } ->
    let av: AbsVal = AVLam {
      ident = name2intAcc graph.ia t.info t.ident,
      body = name2intAcc graph.ia (infoTm t.body) (exprName t.body)
    } in
    let cstr = CstrInit { lhs = av, rhs = name2intAcc graph.ia info ident } in
    { graph with cstrs = cons cstr graph.cstrs }

  sem absValToString im (env: PprintEnv) =
  | AVLam { ident = ident, body = body } ->
    match pprintVarIName im env ident with (env,ident) in
    match pprintVarIName im env body with (env,body) in
    (env, join ["lam ", ident, ". ", body])

end

lang LetCFA = CFA + LetAst
  sem exprName =
  | TmLet t -> exprName t.inexpr
end

lang RecLetsCFA = CFA + LamCFA + RecLetsAst
  sem exprName =
  | TmRecLets t -> exprName t.inexpr

  sem generateConstraints graph =
  | TmRecLets { bindings = bindings } ->
    let cstrs = map (lam b: RecLetBinding.
        match b.body with TmLam t then
          let av: AbsVal = AVLam {
            ident = name2intAcc graph.ia t.info t.ident,
            body = name2intAcc graph.ia (infoTm t.body) (exprName t.body)
          } in
          CstrInit { lhs = av, rhs = name2intAcc graph.ia b.info b.ident }
        else errorSingle [infoTm b.body] "Not a lambda in recursive let body"
      ) bindings
    in
    { graph with cstrs = concat cstrs graph.cstrs }

end

lang ConstCFA = CFA + ConstAst + BaseConstraint + Cmp

  syn AbsVal =
  -- Abstract representation of constants. Contains the constant and the
  -- arguments applied to it. It also includes the `let` name that binds the
  -- constant and syntactically distinguishes it from other of its kind in the
  -- program.
  --
  -- The `intermediates` sequence stores internal generated names used to
  -- implement higher-order constants such as foldl and map. The intermediates
  -- sequence is empty for all non-higher-order constants.
  | AVConst { id: IName, const: Const, args: [IName], intermediates: [IName] }

  sem absValToString im (env: PprintEnv) =
  | AVConst { id = id, const = const, args = args, intermediates = intermediates } ->
    let const = getConstStringCode 0 const in
    match mapAccumL (pprintVarIName im) env args with (env,args) in
    let args = strJoin ", " args in
    match pprintVarIName im env id with (env,id) in
    match mapAccumL (pprintVarIName im) env intermediates with (env,intermediates) in
    (env, join [const,"<", id, ">", "(", args, ")",
                if null intermediates then "" else
                  join ["[", strJoin ", " intermediates, "]"]])

  sem cmpAbsValH =
  | (AVConst lhs, AVConst rhs) ->
    let cmp = cmpConst lhs.const rhs.const in
    if eqi 0 cmp then
      let ncmp = subi lhs.id rhs.id in
      if eqi 0 ncmp then
        -- We intentionally do not include the intermediates in the comparison.
        -- This ensures that every specific occurence of a constant have at
        -- most one initial AVConst. The result is that all ConstPropFuns
        -- operating on the constant share and have access to the same
        -- intermediates.
        seqCmp subi lhs.args rhs.args
      else ncmp
    else cmp

  sem generateConstraints graph =
  | TmLet { ident = ident, body = TmConst t, info = info } ->
    generateConstraintsConst graph t.info (name2intAcc graph.ia info ident) t.val

  sem generateConstraintsConst:
    CFAGraphInit -> Info -> IName -> Const -> CFAGraphInit
  sem generateConstraintsConst graph info ident =
  | _ -> errorSingle [info] "Constant not supported in CFA"

  sem numConstIntermediates: Const -> Int
  sem numConstIntermediates =
  | _ -> 0

  sem addNewConst: CFAGraphInit -> IName -> Const -> CFAGraphInit
  sem addNewConst graph ident =
  | const ->
    let intermediates =
      create (numConstIntermediates const) (lam. nameSym "_intrm_") in
    match mapAccumL addKeyGet graph.ia intermediates with (ia, intermediates) in
    let cstr = CstrInit {
      lhs = AVConst {
        id = ident,
        const = const,
        args = [],
        intermediates = intermediates
      },
      rhs = ident
    } in
    { graph with cstrs = cons cstr graph.cstrs, ia = ia }

end

lang AppCFA = CFA + ConstCFA + BaseConstraint + LamCFA + AppAst + MExprArity

  syn Constraint =
  -- {lam x. b} ⊆ lhs ⇒ (rhs ⊆ x and b ⊆ res)
  | CstrLamApp { lhs: IName, rhs: IName, res: IName }
  -- {const args} ⊆ lhs ⇒ {const args lhs} ⊆ res
  | CstrConstApp { lhs: IName, rhs: IName, res: IName }

  sem cmpConstraintH =
  | (CstrLamApp { lhs = lhs1, rhs = rhs1, res = res1 },
     CstrLamApp { lhs = lhs2, rhs = rhs2, res = res2 }) ->
     let d = subi res1 res2 in
     if eqi d 0 then
       let d = subi lhs1 lhs2 in
       if eqi d 0 then subi rhs1 rhs2
       else d
     else d
  | (CstrConstApp { lhs = lhs1, rhs = rhs1, res = res1},
     CstrConstApp { lhs = lhs2, rhs = rhs2, res = res2}) ->
     let d = subi res1 res2 in
     if eqi d 0 then
       let d = subi lhs1 lhs2 in
       if eqi d 0 then subi rhs1 rhs2
       else d
     else d

  sem initConstraint (graph: CFAGraph) =
  | CstrLamApp r & cstr -> initConstraintName r.lhs graph cstr
  | CstrConstApp r & cstr -> initConstraintName r.lhs graph cstr

  sem propagateConstraint (update: (IName,AbsVal)) (graph: CFAGraph) =
  | CstrLamApp { lhs = lhs, rhs = rhs, res = res } ->
    match update.1 with AVLam { ident = x, body = b } then
      -- Add rhs ⊆ x constraint
      let graph = initConstraint graph (CstrDirect { lhs = rhs, rhs = x }) in
      -- Add b ⊆ res constraint
      initConstraint graph (CstrDirect { lhs = b, rhs = res })
    else graph
  | CstrConstApp { lhs = lhs, rhs = rhs, res = res } ->
    match update.1 with AVConst avc then
      let arity = constArity avc.const in
      let args = snoc avc.args rhs in
      if eqi arity (length args) then
        -- Last application, call constant propagation functions
        let cstrs =
          foldl (lam acc. lam p.
                   concat (p res args avc.intermediates avc.const) acc)
            [] graph.cpfs
        in
        foldl initConstraint graph cstrs
      else
        -- Curried application, add the new argument
        addData graph (AVConst { avc with args = args }) res
    else graph

  sem constraintToString im (env: PprintEnv) =
  | CstrLamApp { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarIName im env lhs with (env,lhs) in
    match pprintVarIName im env rhs with (env,rhs) in
    match pprintVarIName im env res with (env,res) in
    (env, join [ "{lam >x<. >b<} ⊆ ", lhs, " ⇒ ", rhs, " ⊆ >x< AND >b< ⊆ ", res ])
  | CstrConstApp { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarIName im env lhs with (env,lhs) in
    match pprintVarIName im env rhs with (env,rhs) in
    match pprintVarIName im env res with (env,res) in
    (env, join [
        ">const< >args< ⊆ ", lhs, " ⇒ ", ">const< >args< ", rhs, " ⊆ ", res
      ])

  sem appConstraints lhs rhs =
  | res -> [
      CstrLamApp {lhs = lhs, rhs = rhs, res = res},
      CstrConstApp {lhs = lhs, rhs = rhs, res = res}
    ]

  sem generateConstraints graph =
  | TmLet { ident = ident, body = TmApp app, info = info} ->
    match app.lhs with TmVar l then
      match app.rhs with TmVar r then
        let lhs = name2intAcc graph.ia l.info l.ident in
        let rhs = name2intAcc graph.ia r.info r.ident in
        let res = name2intAcc graph.ia info ident in
        let cstrs = appConstraints lhs rhs res in
        { graph with cstrs = concat cstrs graph.cstrs }
      else errorSingle [infoTm app.rhs] "Not a TmVar in application"
    else errorSingle [infoTm app.lhs] "Not a TmVar in application"
end

lang RecordCFA = CFA + BaseConstraint + RecordAst

  syn AbsVal =
  -- Abstract representation of records. The bindings are from SIDs to names,
  -- rather than expressions.
  | AVRec { bindings: Map SID IName }

  sem cmpAbsValH =
  | (AVRec { bindings = lhs }, AVRec { bindings = rhs }) ->
    mapCmp subi lhs rhs

  syn Constraint =
  -- r ∈ lhs ⇒ { r with key = val } ∈ rhs
  | CstrRecordUpdate { lhs: IName, key: SID, val: IName, rhs: IName }

  sem cmpConstraintH =
  | (CstrRecordUpdate { lhs = lhs1, key = key1, val = val1, rhs = rhs1 },
     CstrRecordUpdate { lhs = lhs2, key = key2, val = val2, rhs = rhs2 }) ->
     let d = subi lhs1 lhs2 in
     if eqi d 0 then
       let d = cmpSID key1 key2 in
       if eqi d 0 then
         let d = subi val1 val2 in
         if eqi d 0 then subi rhs1 rhs2
         else d
       else d
     else d

  sem initConstraint (graph: CFAGraph) =
  | CstrRecordUpdate r & cstr -> initConstraintName r.lhs graph cstr

  sem generateConstraints graph =
  | TmLet { ident = ident, body = TmRecord t, info = info } ->
    let bindings = mapMap (lam v: Expr.
        match v with TmVar t then name2intAcc graph.ia t.info t.ident
        else errorSingle [infoTm v] "Not a TmVar in record"
      ) t.bindings
    in
    let av: AbsVal = AVRec { bindings = bindings } in
    let cstr = CstrInit { lhs = av, rhs = name2intAcc graph.ia info ident }  in
    { graph with cstrs = cons cstr graph.cstrs }

  | TmLet { ident = ident, body = TmRecordUpdate t, info = info } ->
    match t.rec with TmVar vrec then
      match t.value with TmVar vval then
        let lhs = name2intAcc graph.ia vrec.info vrec.ident in
        let val = name2intAcc graph.ia vval.info vval.ident in
        let ident = name2intAcc graph.ia info ident in
        let cstr = CstrRecordUpdate { lhs = lhs, key = t.key, val = val, rhs = ident } in
        { graph with cstrs = cons cstr graph.cstrs }
      else errorSingle [t.info] "Not a TmVar in record update"
    else errorSingle [t.info] "Not a TmVar in record update"

  sem propagateConstraint (update: (IName,AbsVal)) (graph: CFAGraph) =
  | CstrRecordUpdate { lhs = lhs, key = key, val = val, rhs = rhs } ->
    match update.1 with AVRec { bindings = bindings } then
      let av = AVRec { bindings = mapInsert key val bindings } in
      initConstraint graph (CstrInit { lhs = av, rhs = rhs })
    else graph

  sem absValToString im (env: PprintEnv) =
  | AVRec { bindings = bindings } ->
    match mapMapAccum (lam env. lam k. lam v.
        match pprintVarIName im env v with (env, v) in
        (env, join [pprintLabelString k, " = ", v])
      ) env bindings
    with (env, bindings) in
    let binds = mapValues bindings in
    let merged = strJoin ", " binds in
    (env, join ["{ ", merged, " }"])

  sem constraintToString im (env: PprintEnv) =
  | CstrRecordUpdate { lhs = lhs, key = key, val = val, rhs = rhs } ->
    match pprintVarIName im env lhs with (env,lhs) in
    match pprintLabelString key with key in
    match pprintVarIName im env val with (env,val) in
    match pprintVarIName im env rhs with (env,rhs) in
    (env, join [">r< ⊆ ", lhs, " ⇒ { >r< with ", key, " = ", val, " } ⊆ ", rhs])

end

-- Abstract values representing sets/collections.
lang SetCFA = CFA + LamCFA

  syn AbsVal =
  | AVSet { names: Set IName }

  sem cmpAbsValH =
  | (AVSet { names = lhs }, AVSet { names = rhs }) -> setCmp lhs rhs

  sem absValToString im (env: PprintEnv) =
  | AVSet { names = names } ->
    match mapAccumL (pprintVarIName im) env (setToSeq names)
    with (env,names) in
    let names = strJoin ", " names in
    (env, join ["[{", names, "}]"])

  syn Constraint =

  -- [{names}] ∈ lhs ⇒ ∀n ∈ names: {n} ⊆ rhs
  | CstrSet {lhs : IName, rhs : IName}

  -- [{names}] ∈ lhs ⇒ [{names} ∪ {rhs}] ⊆ res
  | CstrSetUnion {lhs : IName, rhs : IName, res : IName}

  sem cmpConstraintH =
  | (CstrSet { lhs = lhs1, rhs = rhs1 },
     CstrSet { lhs = lhs2, rhs = rhs2 }) ->
     let d = subi lhs1 lhs2 in
     if eqi d 0 then subi rhs1 rhs2
     else d
  | (CstrSetUnion { lhs = lhs1, rhs = rhs1, res = res1 },
     CstrSetUnion { lhs = lhs2, rhs = rhs2, res = res2 }) ->
     let d = subi res1 res2 in
     if eqi d 0 then
       let d = subi lhs1 lhs2 in
       if eqi d 0 then subi rhs1 rhs2
       else d
     else d

  sem initConstraint (graph: CFAGraph) =
  | CstrSet r & cstr -> initConstraintName r.lhs graph cstr
  | CstrSetUnion r & cstr -> initConstraintName r.lhs graph cstr

  sem constraintToString im (env: PprintEnv) =
  | CstrSet { lhs = lhs, rhs = rhs } ->
    match pprintVarIName im env lhs with (env,lhs) in
    match pprintVarIName im env rhs with (env,rhs) in
    (env, join [ "[{names}] ∈ ", lhs, " ⇒ ∀n ∈ names: {n} ⊆ ", rhs ])
  | CstrSetUnion { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarIName im env lhs with (env,lhs) in
    match pprintVarIName im env rhs with (env,rhs) in
    match pprintVarIName im env res with (env,res) in
    (env, join [
        "[{names}] ∈ ", lhs, " ⇒ [{names} ∪ { ", rhs," }] ⊆ ", res
      ])

  sem propagateConstraint (update: (IName,AbsVal)) (graph: CFAGraph) =
  | CstrSet { lhs = lhs, rhs = rhs } ->
    match update.1 with AVSet { names = names } then
      setFold (lam graph. lam name.
          initConstraint graph (CstrDirect {lhs = name, rhs = rhs})
        ) graph names
    else graph
  | CstrSetUnion { lhs = lhs, rhs = rhs, res = res } ->
    match update.1 with AVSet { names = names } then
      addData graph (AVSet {names = setInsert rhs names}) res
    else graph

end

lang SeqCFA = CFA + BaseConstraint + SetCFA + SeqAst

  sem generateConstraints graph =
  | TmLet { ident = ident, body = TmSeq t, info = info } ->
    let names = foldl (lam acc: [IName]. lam t: Expr.
      match t with TmVar t then
        cons (name2intAcc graph.ia t.info t.ident) acc
      else acc) [] t.tms
    in
    let av: AbsVal = AVSet { names = setOfSeq subi names } in
    let cstr = CstrInit { lhs = av, rhs = name2intAcc graph.ia info ident } in
    { graph with cstrs = cons cstr graph.cstrs }

end

lang TypeCFA = CFA + TypeAst
  sem exprName =
  | TmType t -> exprName t.inexpr
end

lang DataCFA = CFA + BaseConstraint + DataAst
  syn AbsVal =
  -- Abstract representation of constructed data.
  | AVCon { ident: IName, body: IName }

  sem cmpAbsValH =
  | (AVCon { ident = ilhs, body = blhs },
     AVCon { ident = irhs, body = brhs }) ->
    let idiff = subi ilhs irhs in
    if eqi idiff 0 then subi blhs brhs else idiff

  sem generateConstraints graph =
  | TmLet { ident = ident, body = TmConApp t, info = info } ->
    let body =
      match t.body with TmVar v then name2intAcc graph.ia v.info v.ident
      else errorSingle [infoTm t.body] "Not a TmVar in con app" in
    let av: AbsVal = AVCon { ident = name2intAcc graph.ia t.info t.ident, body = body } in
    let cstr = CstrInit { lhs = av, rhs = name2intAcc graph.ia info ident }  in
    { graph with cstrs = cons cstr graph.cstrs }

  sem absValToString im (env: PprintEnv) =
  | AVCon { ident = ident, body = body } ->
    match pprintConIName im env ident with (env,ident) in
    match pprintVarIName im env body with (env,body) in
    (env, join [ident, " ", body])

  sem exprName =
  | TmConDef t -> exprName t.inexpr

end

lang MatchCFA = CFA + BaseConstraint + MatchAst + MExprCmp

  syn Constraint =
  | CstrMatch { id: IName, pat: Pat, target: IName }

  sem cmpConstraintH =
  | (CstrMatch { id = id1, pat = pat1, target = target1 },
     CstrMatch { id = id2, pat = pat2, target = target2 }) ->
     let d = subi id1 id2 in
     if eqi d 0 then
       let d = subi target1 target2 in
       if eqi d 0 then cmpPat pat1 pat2
       else d
     else d

  sem initConstraint (graph: CFAGraph) =
  | CstrMatch r & cstr -> initConstraintName r.target graph cstr

  sem propagateConstraint (update: (IName,AbsVal)) (graph: CFAGraph) =
  | CstrMatch r ->
    propagateMatchConstraint graph r.id (r.pat,update.1)

  sem propagateMatchConstraint: CFAGraph -> IName -> (Pat, AbsVal) -> CFAGraph
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | _ -> graph -- Default: do nothing

  sem constraintToString im (env: PprintEnv) =
  | CstrMatch { id = id, pat = pat, target = target } ->
    match pprintVarIName im env id with (env, id) in
    match getPatStringCode 0 env pat with (env, pat) in
    match pprintVarIName im env target with (env, target) in
    (env, join [id, ": match ", target, " with ", pat])

  sem generateConstraintsMatch: GenFun
  sem generateConstraintsMatch graph =
  | _ -> graph
  | TmLet { ident = ident, body = TmMatch t, info = info } ->
    let thn = name2intAcc graph.ia (infoTm t.thn) (exprName t.thn) in
    let els = name2intAcc graph.ia (infoTm t.els) (exprName t.els) in
    let ident = name2intAcc graph.ia info ident in
    let cstrs = [
      CstrDirect { lhs = thn, rhs = ident },
      CstrDirect { lhs = els, rhs = ident }
    ] in
    let graph = { graph with cstrs = concat cstrs graph.cstrs } in
    match t.target with TmVar tv then
      foldl (lam graph. lam f.
          let cstrs = (f ident (name2intAcc graph.ia tv.info tv.ident) t.pat) in
          { graph with cstrs = concat cstrs graph.cstrs }
        ) graph graph.mcgfs
    else errorSingle [infoTm t.target] "Not a TmVar in match target"

  sem generateMatchConstraints: MatchGenFun
  sem generateMatchConstraints id target =
  | pat ->
    [CstrMatch { id = id, pat = pat, target = target }]

end

lang UtestCFA = CFA + UtestAst
  sem exprName =
  | TmUtest t -> exprName t.next
end

lang NeverCFA = CFA + NeverAst
  -- Nothing to be done here
end

lang ExtCFA = CFA + ExtAst

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
  -- NOTE(2023-07-12,dlunde): Do we have higher-order externals and/or
  -- externals returning functions (or constant functions) in Miking? If so,
  -- I'm not sure how we should handle that (seems very difficult to have some
  -- general mechanism for this). For now, we assume that externals are never
  -- higher-order and do not return functions (or constant functions).
  | AVExt { ext: IName, arity: Int, args: [IName] }

  sem absValToString im (env: PprintEnv) =
  | AVExt { ext = ext, args = args } ->
    -- We ignore the arity (one can simply look up the ext to get the arity)
    match mapAccumL (pprintVarIName im) env args with (env,args) in
    let args = strJoin ", " args in
    match pprintVarIName im env ext with (env,ext) in
    (env, join [ext, "(", args, ")"])

  sem cmpAbsValH =
  | (AVExt lhs, AVExt rhs) ->
    -- We ignore the arity (if ext is the same, arity is the same)
    let cmp = subi lhs.ext rhs.ext in
    if eqi 0 cmp then seqCmp subi lhs.args rhs.args
    else cmp

  syn Constraint =
  -- {ext args} ⊆ lhs ⇒ {ext args lhs} ⊆ res
  | CstrExtApp { lhs: IName, rhs : IName, res: IName }

  sem cmpConstraintH =
  | (CstrExtApp { lhs = lhs1, rhs = rhs1, res = res1 },
     CstrExtApp { lhs = lhs2, rhs = rhs2, res = res2 }) ->
     let d = subi res1 res2 in
     if eqi d 0 then
       let d = subi lhs1 lhs2 in
       if eqi d 0 then subi rhs1 rhs2
       else d
     else d

  sem initConstraint (graph: CFAGraph) =
  | CstrExtApp r & cstr -> initConstraintName r.lhs graph cstr

  sem propagateConstraint (update: (IName,AbsVal)) (graph: CFAGraph) =
  | CstrExtApp { lhs = lhs, rhs = rhs, res = res } ->
    match update.1
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
  sem collectConstraints cgfs graph =
  | TmExt { inexpr = TmLet { ident = ident, inexpr = inexpr } } & t ->
    let graph = foldl (lam acc. lam f. f graph t) graph cgfs in
    collectConstraints cgfs graph inexpr

  sem generateConstraints graph =
  | TmExt { inexpr = TmLet { ident = ident, inexpr = inexpr } } ->
    -- NOTE(dlunde,2022-06-15): Currently, we do not generate any constraints
    -- for externals. Similarly to constants, we probably want to delegate to
    -- `generateConstraintsExts` here. As with `propagateConstraintExt`, it is
    -- not clear where the `generateConstraintsExts` function should be defined.
    --
    graph

  sem exprName =
  -- Skip the eta expanded let added by ANF,
  | TmExt { inexpr = TmLet { inexpr = inexpr }} -> exprName inexpr

end

---------------
-- CONSTANTS --
---------------
-- Most data-flow constraints will need to add data-flow components related to
-- constants (e.g., abstract values for positive and negative integers).
-- However, in this base version of 0-CFA, only some data flow constraints are
-- generated.

-- To add data-flow constraints to a constant:
-- 1. Implement 'generateConstraintsConst' fot the constant.
-- 2. Implement 'propagateConstraintConst' for the constant.

lang IntCFA = CFA + ConstCFA + IntAst
  sem generateConstraintsConst graph info ident =
  | CInt _ -> graph
end

lang ArithIntCFA = CFA + ConstCFA + ArithIntAst
  sem generateConstraintsConst graph info ident =
  | CAddi _ -> graph
  | CSubi _ -> graph
  | CMuli _ -> graph
  | CDivi _ -> graph
  | CNegi _ -> graph
  | CModi _ -> graph
end

lang ShiftIntCFA = CFA + ConstCFA + ShiftIntAst
  sem generateConstraintsConst graph info ident =
  | CSlli _ -> graph
  | CSrli _ -> graph
  | CSrai _ -> graph
end

lang FloatCFA = CFA + ConstCFA + FloatAst
  sem generateConstraintsConst graph info ident =
  | CFloat _ -> graph
end

lang ArithFloatCFA = CFA + ConstCFA + ArithFloatAst
  sem generateConstraintsConst graph info ident =
  | CAddf _ -> graph
  | CSubf _ -> graph
  | CMulf _ -> graph
  | CDivf _ -> graph
  | CNegf _ -> graph
end

lang FloatIntConversionCFA = CFA + ConstCFA + FloatIntConversionAst
  sem generateConstraintsConst graph info ident =
  | CFloorfi _ -> graph
  | CCeilfi _ -> graph
  | CRoundfi _ -> graph
  | CInt2float _ -> graph
end

lang BoolCFA = CFA + ConstCFA + BoolAst
  sem generateConstraintsConst graph info ident =
  | CBool _ -> graph
end

lang CmpIntCFA = CFA + ConstCFA + CmpIntAst
  sem generateConstraintsConst graph info ident =
  | CEqi _ -> graph
  | CNeqi _ -> graph
  | CLti _ -> graph
  | CGti _ -> graph
  | CLeqi _ -> graph
  | CGeqi _ -> graph
end

lang CmpFloatCFA = CFA + ConstCFA + CmpFloatAst
  sem generateConstraintsConst graph info ident =
  | CEqf _ -> graph
  | CLtf _ -> graph
  | CLeqf _ -> graph
  | CGtf _ -> graph
  | CGeqf _ -> graph
  | CNeqf _ -> graph
end

lang CharCFA = CFA + ConstCFA + CharAst
  sem generateConstraintsConst graph info ident =
  | CChar _ -> graph
end

lang CmpCharCFA = CFA + ConstCFA + CmpCharAst
  sem generateConstraintsConst graph info ident =
  | CEqc _ -> graph
end

lang IntCharConversionCFA = CFA + ConstCFA + IntCharConversionAst
  sem generateConstraintsConst graph info ident =
  | CInt2Char _ -> graph
  | CChar2Int _ -> graph
end

lang FloatStringConversionCFA = CFA + ConstCFA + FloatStringConversionAst
  sem generateConstraintsConst graph info ident =
  | CStringIsFloat _ -> graph
  | CString2float _ -> graph
  | CFloat2string _ -> graph
end

lang SymbCFA = CFA + ConstCFA + SymbAst
  sem generateConstraintsConst graph info ident =
  | CSymb _ -> graph
  | CGensym _ -> graph
  | CSym2hash _ -> graph
end

lang CmpSymbCFA = CFA + ConstCFA + CmpSymbAst
  sem generateConstraintsConst graph info ident =
  | CEqsym _ -> graph
end

lang SeqOpCFA =
  CFA + ConstCFA + SeqCFA + SeqOpAst + BaseConstraint + RecordCFA + AppCFA

  -- The number
  sem numConstIntermediates =
  | CFoldl _ -> 4
  | CFoldr _ -> 3
  | CMap _ -> 2
  | CMapi _ -> 4
  | CIter _ -> 2
  | CIteri _ -> 4
  | ( CCreate _
    | CCreateList _
    | CCreateRope _ )
    -> 2

  sem generateConstraintsConst graph info ident =
  | ( CSet _
    | CGet _
    | CCons _
    | CSnoc _
    | CConcat _
    | CReverse _
    | CHead _
    | CTail _
    | CSubsequence _
    | CSplitAt _
    -- !! Higher-order !! --
    | CFoldl _
    | CFoldr _
    | CMap _
    | CMapi _
    | CIter _
    | CIteri _
    | CCreate _
    | CCreateList _
    | CCreateRope _
    -----------------
    ) & const ->
      addNewConst graph ident const

  | ( CLength _
    | CNull _
    | CIsList _
    | CIsRope _
    ) -> graph

  sem propagateConstraintConst res args intermediates =
  | CSet _ ->
    utest length args with 3 in
    let seq = get args 0 in
    let val = get args 2 in
    [CstrSetUnion {lhs = seq, rhs = val, res = res}]
  | CGet _ ->
    utest length args with 2 in
    [CstrSet {lhs = head args, rhs = res}]
  | CCons _ ->
    utest length args with 2 in
    let val = get args 0 in
    let seq = get args 1 in
    [CstrSetUnion {lhs = seq, rhs = val, res = res}]
  | CSnoc _ ->
    utest length args with 2 in
    let seq = get args 0 in
    let val = get args 1 in
    [CstrSetUnion {lhs = seq, rhs = val, res = res}]
  | CConcat _ ->
    utest length args with 2 in
    [
      CstrDirect {lhs = head args, rhs = res},
      CstrDirect {lhs = get args 1, rhs = res}
    ]
  | CReverse _ ->
    utest length args with 1 in
    [CstrDirect {lhs = head args, rhs = res}]
  | CHead _ ->
    utest length args with 1 in
    [CstrSet {lhs = head args, rhs = res}]
  | CTail _ ->
    utest length args with 1 in
    [CstrDirect {lhs = head args, rhs = res}]
  | CSubsequence _ ->
    utest length args with 3 in
    [CstrDirect {lhs = head args, rhs = res}]
  | CSplitAt _ ->
    utest length args with 2 in
    let seq = head args in
    let bindings = mapEmpty subi in
    let bindings = mapInsert (stringToSid "0") seq bindings in
    let bindings = mapInsert (stringToSid "1") seq bindings in
    [CstrInit {lhs = AVRec { bindings = bindings }, rhs = res}]

  -- !! Higher-order !! --
  | CFoldl _ ->
    utest length args with 3 in
    let seq = get args 2 in
    let f = head args in
    let acc = get args 1 in
    match intermediates with [li,a1,a2,a3] in
    join [
      [CstrDirect { lhs = acc, rhs = res }],
      [CstrSet { lhs = seq, rhs = li }],
      appConstraints f acc a1,
      appConstraints a1 li a2,
      [CstrDirect { lhs = a2, rhs = res }],
      appConstraints f a2 a3,
      appConstraints a3 li res
    ]
  | CFoldr _ ->
    utest length args with 3 in
    let seq = get args 2 in
    let f = head args in
    let acc = get args 1 in
    match intermediates with [li,a1,a2] in
    join [
      [CstrDirect { lhs = acc, rhs = res }],
      [CstrSet { lhs = seq, rhs = li }],
      appConstraints f li a1,
      appConstraints a1 acc a2,
      [CstrDirect { lhs = a2, rhs = res }],
      appConstraints a1 a2 res
    ]
  | CMap _ ->
    utest length args with 2 in
    let seq = get args 1 in
    let f = head args in
    match intermediates with [li,a1] in
    join [
      [CstrSet { lhs = seq, rhs = li }],
      appConstraints f li a1,
      [CstrInit { lhs = AVSet {names = setOfSeq subi [a1]}, rhs = res }]
    ]
  | CMapi _ ->
    utest length args with 2 in
    let seq = get args 1 in
    let f = head args in
    -- NOTE(2023-07-12,dlunde): We assume i is empty here. For some analysis
    -- that want to track integer values, this won't work.
    match intermediates with [li,i,a1,a2] in
    join [
      [CstrSet { lhs = seq, rhs = li }],
      appConstraints f i a1,
      appConstraints a1 li a2,
      [CstrInit { lhs = AVSet {names = setOfSeq subi [a2]}, rhs = res }]
    ]
  | CIter _ ->
    utest length args with 2 in
    let seq = get args 1 in
    let f = head args in
    match intermediates with [li,empty] in
    join [
      [CstrSet { lhs = seq, rhs = li }],
      appConstraints f li empty
    ]
  | CIteri _ ->
    utest length args with 2 in
    let seq = get args 1 in
    let f = head args in
    -- NOTE(2023-07-12,dlunde): We assume i is empty here. For some analysis
    -- that want to track integer values, this won't work.
    match intermediates with [li,i,a1,empty] in
    join [
      [CstrSet { lhs = seq, rhs = li }],
      appConstraints f i a1,
      appConstraints a1 li empty
    ]
  | ( CCreate _
    | CCreateList _
    | CCreateRope _
    ) ->
    utest length args with 2 in
    let f = get args 1 in
    -- NOTE(2023-07-12,dlunde): We assume i is empty here. For some analysis
    -- that want to track integer values, this won't work.
    match intermediates with [i,a1] in
    join [
      appConstraints f i a1,
      [CstrInit { lhs = AVSet {names = setOfSeq subi [a1]}, rhs = res }]
    ]
  --------------------------------


end

lang FileOpCFA = CFA + ConstCFA + FileOpAst
  sem generateConstraintsConst graph info ident =
  | CFileRead _ -> graph
  | CFileWrite _ -> graph
  | CFileExists _ -> graph
  | CFileDelete _ -> graph
end

lang IOCFA = CFA + ConstCFA + IOAst
  sem generateConstraintsConst graph info ident =
  | CPrint _ -> graph
  | CPrintError _ -> graph
  | CDPrint _ -> graph
  | CFlushStdout _ -> graph
  | CFlushStderr _ -> graph
  | CReadLine _ -> graph
  | CReadBytesAsString _ -> graph
end

lang RandomNumberGeneratorCFA = CFA + ConstCFA + RandomNumberGeneratorAst
  sem generateConstraintsConst graph info ident =
  | CRandIntU _ -> graph
  | CRandSetSeed _ -> graph
end

lang SysCFA = CFA + ConstCFA + SysAst
  sem generateConstraintsConst graph info ident =
  | CExit _ -> graph
  | CError _ -> graph
  | CArgv _ -> graph
  | CCommand _ -> graph
end

lang TimeCFA = CFA + ConstCFA + TimeAst
  sem generateConstraintsConst graph info ident =
  | CWallTimeMs _ -> graph
  | CSleepMs _ -> graph
end

lang ConTagCFA = CFA + ConstCFA + ConTagAst
  sem generateConstraintsConst graph info ident =
  | CConstructorTag _ -> graph
end

lang RefOpCFA = CFA + ConstCFA + RefOpAst
  syn AbsVal =
  -- Abstract representation of references
  | AVRef { contents: IName }

  sem cmpAbsValH =
  | (AVRef { contents = ilhs }, AVRef { contents = irhs }) -> subi ilhs irhs

  sem absValToString im (env: PprintEnv) =
  | AVRef { contents = contents } ->
    match pprintVarIName im env contents with (env,contents) in
    (env, join ["ref(", contents, ")"])

  syn Constraint =
  -- ref(name) ∈ lhs ⇒ {name} ⊆ rhs
  | CstrRef {lhs : IName, rhs : IName}

  sem cmpConstraintH =
  | (CstrRef { lhs = lhs1, rhs = rhs1 },
     CstrRef { lhs = lhs2, rhs = rhs2 }) ->
     let d = subi lhs1 lhs2 in
     if eqi d 0 then subi rhs1 rhs2
     else d

  sem initConstraint (graph: CFAGraph) =
  | CstrRef r & cstr -> initConstraintName r.lhs graph cstr

  sem constraintToString im (env: PprintEnv) =
  | CstrRef { lhs = lhs, rhs = rhs } ->
    match pprintVarIName im env lhs with (env,lhs) in
    match pprintVarIName im env rhs with (env,rhs) in
    (env, join [ "ref(name) ∈ ", lhs, " ⇒ {name} ⊆ ", rhs ])

  sem propagateConstraint (update: (IName,AbsVal)) (graph: CFAGraph) =
  | CstrRef { lhs = lhs, rhs = rhs } ->
    match update.1 with AVRef { contents = contents } then
      initConstraint graph (CstrDirect {lhs = contents, rhs = rhs})
    else graph

  sem generateConstraintsConst graph info ident =
  | (CRef _ | CDeRef _) & const ->
    addNewConst graph ident const

  -- TODO(dlunde,2021-11-11): Mutability complicates the analysis, but could
  -- probably be added.
  -- | CModRef _ -> graph

  sem propagateConstraintConst res args intermediates =
  | CRef _ ->
    utest length args with 1 in
    [CstrInit {lhs = AVRef { contents = head args }, rhs = res}]
  | CDeRef _ ->
    utest length args with 1 in
    [CstrRef {lhs = head args, rhs = res}]

end

lang TensorOpCFA = CFA + ConstCFA + TensorOpAst + SetCFA + AppCFA

  sem numConstIntermediates =
  | CTensorCreateInt _ -> 2
  | CTensorCreateFloat _ -> 2
  | CTensorCreate _ -> 2
  | CTensorIterSlice _ -> 4

  sem generateConstraintsConst graph info ident =
  | ( CTensorCreateUninitInt _
    | CTensorCreateUninitFloat _
    | CTensorGetExn _
    | CTensorLinearGetExn _
    | CTensorReshapeExn _
    | CTensorCopy _
    | CTensorTransposeExn _
    | CTensorSliceExn _
    | CTensorSubExn _
    | CTensorShape _
    -- !! Higher-order !! --
    | CTensorCreateInt _
    | CTensorCreateFloat _
    | CTensorCreate _
    | CTensorIterSlice _
    -------------------
    ) & const -> addNewConst graph ident const

  | ( CTensorRank _
    | CTensorEq _
    | CTensorToString _ ) -> graph

  -- TODO(dlunde,2023-07-10): Mutability complicates the analysis, but could
  -- probably be added.
  -- | CTensorSetExn _ -> graph
  -- | CTensorLinearSetExn _ -> graph

  sem propagateConstraintConst res args intermediates =
  -- NOTE(2023-07-10,dlunde): We do not need to track integers and floats (at
  -- least in the basic analysis) and can therefore just initialize empty AVSets
  -- here.
  --
  | ( CTensorCreateUninitInt _
    | CTensorCreateUninitFloat _
    | CTensorShape _) ->
    -- NOTE(2023-07-12,dlunde): We can include CTensorShape here as well, since
    -- it only returns sequences of integers. For some analysis that want to
    -- track sequences of integer values (e.g., tensor shapes), this won't
    -- work.
    let av: AbsVal = AVSet { names = setEmpty subi } in
    [CstrInit { lhs = av, rhs = res }]
  | ( CTensorCreateInt _
    | CTensorCreateFloat _
    | CTensorCreate _ ) ->
    utest length args with 2 in
    let f = get args 1 in
    -- NOTE(2023-07-12,dlunde): We assume i is empty here. For some analysis
    -- that want to track sequences of integer values (e.g., tensor shapes),
    -- this won't work.
    match intermediates with [i,a1] in
    join [
      appConstraints f i a1,
      [CstrInit { lhs = AVSet {names = setOfSeq subi [a1]}, rhs = res }]
    ]
  | CTensorIterSlice _ ->
    utest length args with 2 in
    let f = get args 0 in
    let tensor = get args 1 in
    match intermediates with [ti,i,a1,empty] in
    join [
      [CstrSet {lhs = tensor, rhs = ti}],
      appConstraints f i a1,
      appConstraints a1 ti empty
    ]
  | ( CTensorGetExn _
    | CTensorLinearGetExn _ ) ->
    utest length args with 2 in
    [CstrSet { lhs = head args, rhs = res }]
  | CTensorReshapeExn _ ->
    utest length args with 2 in
    [CstrDirect {lhs = get args 0, rhs = res}]
  | CTensorCopy _ ->
    utest length args with 1 in
    [CstrDirect {lhs = get args 0, rhs = res}]
  | CTensorTransposeExn _ ->
    utest length args with 3 in
    [CstrDirect {lhs = get args 0, rhs = res}]
  | CTensorSliceExn _ ->
    utest length args with 2 in
    [CstrDirect {lhs = get args 0, rhs = res}]
  | CTensorSubExn _ ->
    utest length args with 3 in
    [CstrDirect {lhs = get args 0, rhs = res}]

end

lang BootParserCFA = CFA + ConstCFA + BootParserAst
  sem generateConstraintsConst graph info ident =
  | CBootParserParseMExprString _ -> graph
  | CBootParserParseMLangString _ -> graph
  | CBootParserParseMLangFile _ -> graph
  | CBootParserParseMCoreFile _ -> graph
  | CBootParserGetId _ -> graph
  | CBootParserGetTerm _ -> graph
  | CBootParserGetTop _ -> graph
  | CBootParserGetDecl _ -> graph
  | CBootParserGetType _ -> graph
  | CBootParserGetString _ -> graph
  | CBootParserGetInt _ -> graph
  | CBootParserGetFloat _ -> graph
  | CBootParserGetListLength _ -> graph
  | CBootParserGetConst _ -> graph
  | CBootParserGetPat _ -> graph
  | CBootParserGetInfo _ -> graph
end

--------------
-- PATTERNS --
--------------

lang NamedPatCFA = MatchCFA + NamedPat + BaseConstraint
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatNamed { ident = PName n, info = info }, av) ->
    propagateDirectConstraint (name2int graph.im info n) graph av
  | (PatNamed { ident = PWildcard _ }, _) -> graph
end

lang SeqTotPatCFA = MatchCFA + SeqCFA + SeqTotPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatSeqTot p, AVSet { names = names }) ->
    let f = lam graph. lam pat: Pat. setFold (lam graph: CFAGraph. lam name.
        let cstrs =
          foldl (lam acc. lam f. concat (f id name pat) acc) [] graph.mcgfs
        in
        foldl initConstraint graph cstrs
      ) graph names in
    foldl f graph p.pats
end

lang SeqEdgePatCFA = MatchCFA + SeqCFA + SeqEdgePat
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatSeqEdge p, AVSet { names = names } & av) ->
    let f = lam graph. lam pat: Pat. setFold (lam graph: CFAGraph. lam name.
        let cstrs = foldl (lam acc. lam f. concat (f id name pat) acc)
          [] graph.mcgfs in
        foldl initConstraint graph cstrs
      ) graph names in
    let graph = foldl f graph p.prefix in
    let graph = foldl f graph p.postfix in
    match p.middle with PName rhs
    then addData graph av (name2int graph.im p.info rhs)
    else graph
  | (PatSeqEdge p, av) ->
    match p.middle with PName rhs
    then addData graph av (name2int graph.im p.info rhs)
    else graph
end

lang RecordPatCFA = MatchCFA + RecordCFA + RecordPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatRecord { bindings = pbindings }, AVRec { bindings = abindings }) ->
    -- Check if record pattern is compatible with abstract value record
    let compatible = mapAllWithKey (lam k. lam. mapMem k abindings) pbindings in
    if compatible then
      mapFoldWithKey (lam graph: CFAGraph. lam k. lam pb: Pat.
        let ab: IName = mapFindExn k abindings in
        let cstrs = foldl (lam acc. lam f. concat (f id ab pb) acc)
          [] graph.mcgfs in
        foldl initConstraint graph cstrs
      ) graph pbindings
    else graph -- Nothing to be done
end

lang DataPatCFA = MatchCFA + DataCFA + DataPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatCon p, AVCon { ident = ident, body = body }) ->
    if nameEq p.ident (int2name graph.im ident) then
      let cstrs = foldl (lam acc. lam f. concat (f id body p.subpat) acc)
        [] graph.mcgfs in
      foldl initConstraint graph cstrs
    else graph
end

lang IntPatCFA = MatchCFA + IntPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatInt p, _) -> graph
end

lang CharPatCFA = MatchCFA + CharPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatChar p, _) -> graph
end

lang BoolPatCFA = MatchCFA + BoolPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatBool p, _) -> graph
end

lang AndPatCFA = MatchCFA + AndPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatAnd p, av) ->
    let graph = propagateMatchConstraint graph id (p.lpat, av) in
    propagateMatchConstraint graph id (p.rpat, av)
end

lang OrPatCFA = MatchCFA + OrPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatOr p, av) ->
    let graph = propagateMatchConstraint graph id (p.lpat, av) in
    propagateMatchConstraint graph id (p.rpat, av)
end

lang NotPatCFA = MatchCFA + NotPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatNot p, _) -> graph
end

-----------------
-- MEXPR 0-CFA --
-----------------

lang MExprCFA = CFA +

  -- Base constraints
  BaseConstraint +

  -- Terms
  VarCFA + LamCFA + AppCFA +
  LetCFA + RecLetsCFA + ConstCFA + SeqCFA + RecordCFA + TypeCFA + DataCFA +
  MatchCFA + UtestCFA + NeverCFA + ExtCFA +

  -- Constants
  IntCFA + ArithIntCFA + ShiftIntCFA + FloatCFA + ArithFloatCFA +
  FloatIntConversionCFA + BoolCFA + CmpIntCFA + CmpFloatCFA + CharCFA +
  CmpCharCFA + IntCharConversionCFA + FloatStringConversionCFA + SymbCFA +
  CmpSymbCFA + SeqOpCFA + FileOpCFA + IOCFA + RandomNumberGeneratorCFA +
  SysCFA + TimeCFA + ConTagCFA + RefOpCFA + TensorOpCFA + BootParserCFA +

  -- Patterns
  NamedPatCFA + SeqTotPatCFA + SeqEdgePatCFA + RecordPatCFA + DataPatCFA +
  IntPatCFA + CharPatCFA + BoolPatCFA + AndPatCFA + OrPatCFA + NotPatCFA

  -- Function that adds a set of universal base match constraints to a CFAGraph
  sem addBaseMatchConstraints: CFAGraphInit -> CFAGraphInit
  sem addBaseMatchConstraints =
  | graph ->
    { graph with mcgfs = cons generateMatchConstraints graph.mcgfs }

  -- Function that adds a set of universal base constraints to a CFAGraph
  sem addBaseConstraints (graph: CFAGraphInit) =
  | t ->

    -- Set constant propagation functions
    let graph = {graph with cpfs = cons propagateConstraintConst graph.cpfs} in

    -- Initialize constraint generating functions
    let cgfs = [ generateConstraints, generateConstraintsMatch ] in

    -- Recurse over program and generate constraints
    let graph = collectConstraints cgfs graph t in

    graph

end

-----------------
-- TESTS 0-CFA --
-----------------

lang Test = MExprCFA + MExprANFAll + BootParser + MExprPrettyPrint

  sem testCfa : Expr -> CFAGraph
  sem testCfa =
  | t ->
    let graph = emptyCFAGraphInit t in
    let graph = addBaseMatchConstraints graph in
    let graph = addBaseConstraints graph t in
    solveCfa graph

  sem testCfaDebug : PprintEnv -> Expr -> (PprintEnv, CFAGraph)
  sem testCfaDebug pprintenv =
  | t ->
    let graph = emptyCFAGraphInit t in
    let graph = addBaseMatchConstraints graph in
    let graph = addBaseConstraints graph t in
    solveCfaDebug pprintenv graph

end

mexpr
use Test in

-- Test functions --
let _parse = parseMExprStringKeywordsExn [] in
let _testBase: Option PprintEnv -> Expr -> (Option PprintEnv, CFAGraph) =
  lam env: Option PprintEnv. lam t: Expr.
    match env with Some env then
      -- Version with debug printouts
      let tANF = normalizeTerm t in
      match pprintCode 0 env t with (env,tStr) in
      printLn "\n--- ORIGINAL PROGRAM ---";
      printLn tStr;
      match pprintCode 0 env tANF with (env,tANFStr) in
      printLn "\n--- ANF ---";
      printLn tANFStr;
      match testCfaDebug env tANF with (env,cfaRes) in
      match cfaGraphToString env cfaRes with (env, resStr) in
      printLn "\n--- FINAL CFA GRAPH ---";
      printLn resStr;
      (Some env,cfaRes)

    else
      -- Version without debug printouts
      let tANF = normalizeTerm t in
      let cfaRes = testCfa tANF in
      (None (), cfaRes)
in

let _test: Bool -> Expr -> [String] -> [(String,[String])] =
  lam debug. lam t. lam vars.
    let env = if debug then Some pprintEnvEmpty else None () in
    match _testBase env t with (_, cfaRes) in
    let stringMap: Map String Int = mapFoldWithKey (
        lam acc: Map String Int. lam n: Name. lam i: Int.
          mapInsert (nameGetStr n) i acc
      ) (mapEmpty cmpString) cfaRes.im.name2int
    in
    let string2int: String -> Int = lam s. mapFindExn s stringMap in
    map (lam var: String.
      let avs = dataLookup (string2int var) cfaRes in
      let val = setFold
        (lam acc. lam av.
           match av with AVLam { ident = i } then
             cons (nameGetStr (int2name cfaRes.im i)) acc
           else acc)
        [] avs
      in (var, val)
    ) vars
in

-- Custom equality function for testing lambda control flow only
let eqTestLam = eqSeq (lam t1:(String,[String]). lam t2:(String,[String]).
  if eqString t1.0 t2.0 then
    let t11 = setOfSeq cmpString t1.1 in
    let t21 = setOfSeq cmpString t2.1 in
    setEq t11 t21
  else false
) in
--------------------

-- First test from Nielson et al.
let t = _parse "
  (lam x. x) (lam y. y)
------------------------" in
utest _test false t ["x","y"] with [
  ("x", ["y"]),
  ("y", [])
] using eqTestLam in

-- Second test from Nielson et al.
let t = _parse "
  let f = lam x. x 1 in
  let g = lam y. addi y 2 in
  let h = lam z. addi z 3 in
  let res = addi (f g) (f h) in
  res
------------------------" in
utest _test false t ["f","g","h","x","y","z","res"] with [
  ("f", ["x"]),
  ("g", ["y"]),
  ("h", ["z"]),
  ("x", ["y","z"]),
  ("y", []),
  ("z", []),
  ("res", [])
] using eqTestLam in

-- Third test from Nielson et al.
let t = _parse "
recursive let g = lam x. g (lam y. y) in
let res = g (lam z. z) in
res
------------------------" in
utest _test false t ["g","x","y","z","res"] with [
  ("g", ["x"]),
  ("x", ["y","z"]),
  ("y", []),
  ("z", []),
  ("res", [])
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
utest _test false t ["res","a"] with [
  ("res", ["v","y"]),
  ("a", ["x","z"])
] using eqTestLam in

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
utest _test false t [
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
] using eqTestLam in

-- Map over sequences
let t = _parse "
  let s1 = map (lam x. x) [lam y. y, lam z. z] in
  let r1 = head s1 in
  let s2 = map (lam a. lam d. d) [lam b. b, lam c. c] in
  let r2 = head s2 in
  let s3 = mapi (lam i. lam x. x) [lam y. y, lam z. z] in
  let r3 = head s3 in
  let s4 = map (map (lam x. let t1 = x in x)) [[lam y. y], [lam z. z]] in
  let r4 = head (head s4) in
  let s5 = map (mapi (lam i. lam x. let t1 = x in x)) [[lam y. y], [lam z. z]] in
  let r5 = head (head s4) in
  ()
------------------------" in
utest _test false t ["r1", "r2", "r3", "r4", "r5"] with [
  ("r1", ["y", "z"]),
  ("r2", ["d"]),
  ("r3", ["y", "z"]),
  ("r4", ["y", "z"]),
  ("r5", ["y", "z"])
] using eqTestLam in

-- Iter over sequences
let t = _parse "
  let s0 = lam a. a in
  let s1 = iter (lam x. let t1 = x in x) [lam y. y, lam z. z] in
  let s2 = iteri (lam i. lam x. let t2 = x in x) [lam y. y, lam z. z] in
  let s3 = iter (iter (lam x. let t3 = x in x)) [[lam y. y], [lam z. z]] in
  let s4 = iter (iteri (lam i. lam x. let t4 = x in x)) [[lam y. y], [lam z. z]] in
  ()
------------------------" in
utest _test false t ["t1", "t2", "t3", "t4"] with [
  ("t1", ["y", "z"]),
  ("t2", ["y", "z"]),
  ("t3", ["y", "z"]),
  ("t4", ["y", "z"])
] using eqTestLam in

-- Create sequences
let t = _parse "
  let s1 = create 1 (lam i1. lam x. x) in
  let r1 = head s1 in
  let s2 = createList 2 (lam i2. lam y. y) in
  let r2 = head s2 in
  let s3 = createRope 3 (lam i3. lam z. z) in
  let r3 = head s3 in
  ()
------------------------" in
utest _test false t ["r1", "r2", "r3"] with [
  ("r1", ["x"]),
  ("r2", ["y"]),
  ("r3", ["z"])
] using eqTestLam in

-- Split sequences
let t = _parse "
  let s1 = [lam x. x, lam y. y, lam z. z] in
  match splitAt s1 1 with (t1,t2) in
  let r1 = head t1 in
  let r2 = head t2 in
  ()
------------------------" in
utest _test false t ["r1", "r2"] with [
  ("r1", ["x", "y", "z"]),
  ("r2", ["x", "y", "z"])
] using eqTestLam in

-- Foldl
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let h = lam z. z in
  let r1 = foldl (lam a1. lam e1. a1) f [g, h] in
  let r2 = foldl (lam a2. lam e2. a2 e2) f [g, h] in
  let r3 = foldl (lam a3. lam e3. a3 e3) (lam w. w) [] in
  let r4 = foldl (lam a4. lam e4. let t1 = a4 in e4) (lam v. v) [f,g,h] in
  let r5 =
    foldl (foldl (lam a5. lam e5. let t2 = a5 in e5)) (lam u. u)
      [[f],[g],[h]] in
  ()
------------------------" in
utest _test false t ["r1", "r2", "r3", "r4", "t1", "r5", "t2"] with [
  ("r1", ["x"]),
  ("r2", ["x", "y", "z"]),
  ("r3", ["w"]),
  ("r4", ["v", "z", "y", "x"]),
  ("t1", ["v", "z", "y", "x"]),
  ("r5", ["u", "z", "y", "x"]),
  ("t2", ["u", "z", "y", "x"])
] using eqTestLam in

-- Foldr
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let h = lam z. z in
  let r1 = foldr (lam e1. lam a1. a1) f [g, h] in
  let r2 = foldr (lam e2. lam a2. a2 e2) f [g, h] in
  let r3 = foldr (lam e3. lam a3. a3 e3) (lam w. w) [] in
  let r4 = foldr (lam e4. lam a4. let t1 = a4 in e4) (lam v. v) [f,g,h] in
  let r5 =
    foldl (foldr (lam e5. lam a5. let t2 = a5 in e5)) (lam u. u)
      [[f],[g],[h]] in
  ()
------------------------" in
utest _test false t ["r1", "r2", "r3", "r4", "t1", "r5", "t2"] with [
  ("r1", ["x"]),
  ("r2", ["z", "y", "x"]),
  ("r3", ["w"]),
  ("r4", ["v", "z", "y", "x"]),
  ("t1", ["v", "z", "y", "x"]),
  ("r5", ["u", "z", "y", "x"]),
  ("t2", ["u", "z", "y", "x"])
] using eqTestLam in

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
utest _test false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["x"])
] using eqTestLam in

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
utest _test false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["w"])
] using eqTestLam in

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
utest _test false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["x"])
] using eqTestLam in

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
utest _test false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["x"])
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
utest _test false t ["res", "a", "b"] with [
  ("res", ["y","z"]),
  ("a", ["x"]),
  ("b", ["x"])
] using eqTestLam in

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
utest _test false t ["res", "rhs"] with [
  ("res", ["y","z"]),
  ("rhs", ["x"])
] using eqTestLam in

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
utest _test false t ["res", "res2", "p"] with [
  ("res", ["yy","z"]),
  ("res2", ["k","w"]),
  ("p", ["x"])
] using eqTestLam in

-- References
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let r1 = ref f in
  let r2 = ref g in
  let t1 = deref r1 in
  let t2 = lam z.
    let t3 = deref z in
    t3
  in
  let t4 = t2 r1 in
  let t5 = t2 r2 in
  t5
------------------------" in
utest _test false t ["t1", "t2", "t3", "t4", "t5"] with [
  ("t1", ["x"]),
  ("t2", ["z"]),
  ("t3", ["x","y"]),
  ("t4", ["x","y"]),
  ("t5", ["x","y"])
] using eqTestLam in

-- Tensor
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in

  let t1 = tensorCreateUninitInt [3,3] in
  let t2 = tensorCreateUninitFloat [3,3] in
  let t3 = tensorCreateCArrayInt [3,3] (lam i1. 1) in
  let t4 = tensorCreateCArrayFloat [3,3] (lam f1. 1.0) in
  let t5 = tensorCreateDense [3,3] (lam x1. f) in
  let t6 = tensorGetExn t1 [0,0] in
  let t7 = tensorGetExn t5 [0,0] in
  let t8 = tensorLinearGetExn t2 0 in
  let t9 = tensorLinearGetExn t5 0 in
  let t10 = tensorReshapeExn t5 [1,9] in
  let t11 = tensorCopy t10 in
  let t12 = tensorTransposeExn t11 0 1 in
  let t13 = tensorSliceExn t5 [0] in
  let t14 = tensorSubExn t5 1 1 in
  let t15 = tensorShape t14 in
  let t16 = map (lam x2. g) t15 in
  let t17 = get t16 0 in
  let t18 = tensorLinearGetExn t12 0 in
  let t19 = tensorLinearGetExn t13 0 in
  let t20 = tensorLinearGetExn t14 0 in
  let t21 = tensorIterSlice (lam i. lam e. let t22 = e in ()) t5 in
  ()
------------------------" in
utest _test false t
  ["t1","t2","t3","t4","t5","t6","t7","t8","t9","t10",
   "t11","t12","t13","t14","t15","t16","t17","t18","t19","t20", "t21", "t22"]
with [
  ("t1",  []),
  ("t2",  []),
  ("t3",  []),
  ("t4",  []),
  ("t5",  []),
  ("t6",  []),
  ("t7",  ["x"]),
  ("t8",  []),
  ("t9",  ["x"]),
  ("t10", []),
  ("t11", []),
  ("t12", []),
  ("t13", []),
  ("t14", []),
  ("t15", []),
  ("t16", []),
  ("t17", ["y"]),
  ("t18", ["x"]),
  ("t19", ["x"]),
  ("t20", ["x"]),
  ("t21", []),
  ("t22", ["x"])
] using eqTestLam in

()
