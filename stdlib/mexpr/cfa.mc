-- CFA framework for MExpr. Currently, only 0-CFA (0 = context insensitive) is
-- supported. The algorithm is loosely based on Table 3.7 in the book
-- "Principles of Program Analysis" (Nielson et al.).
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

include "pprint.mc"
include "boot-parser.mc"
include "ast.mc"
include "anf.mc"
include "ast-builder.mc"
include "cmp.mc"
include "const-arity.mc"
include "index.mc"

type IName = Int
type GenFun = Expr -> [Constraint]
type MatchGenFun = IName -> IName -> Pat -> [Constraint]

-------------------
-- BASE FRAGMENT --
-------------------

lang CFA = Ast + LetAst + MExprIndex + MExprPrettyPrint

  type CFAGraph = {

    -- Contains updates that needs to be processed in the main CFA loop
    worklist: [(IName,AbsVal)],

    -- Contains abstract values currently associated with each name in the program.
    data: [Set AbsVal],

    -- For each name in the program, gives constraints which needs to be
    -- repropagated upon updates to the abstract values for the name.
    edges: [[Constraint]],

    -- Contains a list of functions used for generating match constraints
    -- TODO(dlunde,2021-11-17): Should be added as a product extension
    -- in the MatchCFA fragment instead, when possible.
    mcgfs: [MatchGenFun],

    -- Bidirectional mapping between names and integers.
    im: IndexMap,

    -- NOTE(dlunde,2021-11-18): Data needed for analyses based on this framework
    -- must be put below directly, since we do not yet have product extensions.

    -- Used to store any custom data in the graph
    graphData: Option GraphData

  }

  sem emptyCFAGraph: Expr -> CFAGraph
  sem emptyCFAGraph =
  | t ->
    let im = indexGen t in
    { worklist = [],
      data = map (lam. setEmpty cmpAbsVal) im.int2name,
      edges = map (lam. []) im.int2name,
      mcgfs = [],
      im = im,
      graphData = None () }

  sem name2int: IndexMap -> Info -> Name -> IName
  sem name2int im info =
  | name ->
    mapLookupOrElse (lam.
        errorSingle [info] (concat "name2int failed: " (nameGetStr name)))
      name im.name2int

  sem int2name: IndexMap -> IName -> Name
  sem int2name im =
  | i -> get im.int2name i

  sem pprintVarIName: IndexMap -> PprintEnv -> IName -> (PprintEnv, String)
  sem pprintVarIName im env =
  | n -> pprintVarName env (int2name im n)

  -- This function converts the data-flow result into a map, which might be more
  -- convenient to operate on for later analysis steps.
  sem cfaGraphData: CFAGraph -> Map Name (Set AbsVal)
  sem cfaGraphData =
  | graph ->
    foldl (lam acc. lam b: (IName, Set AbsVal).
        match b with (id,vals) in
        mapInsert (int2name graph.im id) vals acc
      ) (mapEmpty nameCmp) (mapi (lam i. lam x. (i, x)) graph.data)

  syn Constraint =
  -- Intentionally left blank

  syn AbsVal =
  -- Intentionally left blank

  syn GraphData =
  -- Intentionally left blank

  sem cfa: Expr -> CFAGraph
  sem cfa =
  | t -> match cfaDebug (None ()) (None ()) t with (_,graph) in graph

  sem cfaData: GraphData -> Expr -> CFAGraph
  sem cfaData (graphData: GraphData) =
  | t -> match cfaDebug (Some graphData) (None ()) t with (_,graph) in graph

  -- Main algorithm
  sem cfaDebug : Option GraphData -> Option PprintEnv -> Expr
               -> (Option PprintEnv, CFAGraph)
  sem cfaDebug graphData env =
  | t ->

    let printGraph = lam env. lam graph. lam str.
      match env with Some env then
        match cfaGraphToString env graph with (env, graph) in
        printLn (join ["\n--- ", str, " ---"]);
        printLn graph;
        Some env
      else None ()
    in

    let graph = initGraph graphData t in

    -- Iteration
    recursive let iter = lam env: Option PprintEnv. lam graph: CFAGraph.
      if null graph.worklist then (env,graph)
      else
        match printGraph env graph "INTERMEDIATE CFA GRAPH" with env in
        match head graph.worklist with (q,d) & h in
        let graph = { graph with worklist = tail graph.worklist } in
        match edgesLookup q graph with cc in
        let graph = foldl (propagateConstraint h) graph cc in
        iter env graph
    in
    iter env graph

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

  -- Base constraint generation function (must still be included manually in
  -- constraintGenFuns)
  sem generateConstraints: IndexMap -> Expr -> [Constraint]
  sem generateConstraints im =
  | t -> []

  -- This function is responsible for setting up the initial CFAGraph given the
  -- program to analyze.
  sem initGraph: Option GraphData -> Expr -> CFAGraph

  -- Call a set of constraint generation functions on each term in program.
  -- Useful when defining initGraph.
  sem collectConstraints: [GenFun] -> [Constraint] -> Expr -> [Constraint]
  sem collectConstraints (cgfs: [GenFun]) (acc: [Constraint]) =
  | t ->
    let acc = foldl (lam acc. lam f. concat (f t) acc) acc cgfs in
    sfold_Expr_Expr (collectConstraints cgfs) acc t

  sem initConstraint: CFAGraph -> Constraint -> CFAGraph

  sem propagateConstraint: (IName,AbsVal) -> CFAGraph -> Constraint -> CFAGraph

  sem addEdge: CFAGraph -> IName -> Constraint -> CFAGraph
  sem addEdge (graph: CFAGraph) (q: IName) =
  | cstr ->
    let cstrsq = edgesLookup q graph in
    { graph with edges = set graph.edges q (cons cstr cstrsq) }

  -- Helper function for initializing a constraint for a given name (mainly
  -- used for convenience in initConstraint)
  sem initConstraintName: IName -> CFAGraph -> Constraint -> CFAGraph
  sem initConstraintName (name: IName) (graph: CFAGraph) =
  | cstr ->
    let graph = addEdge graph name cstr in
    let avs = dataLookup name graph in
    setFold (lam graph. lam av. propagateConstraint (name,av) graph cstr)
      graph avs

  sem dataLookup: IName -> CFAGraph -> Set AbsVal
  sem dataLookup (key: IName) =
  | graph -> get graph.data key

  sem edgesLookup (key: IName) =
  | graph -> get graph.edges key

  sem addData: CFAGraph -> AbsVal -> IName -> CFAGraph
  sem addData (graph: CFAGraph) (d: AbsVal) =
  | q ->
    let dq = dataLookup q graph in
    if setMem d dq then graph else
      {{ graph with
           data = set graph.data q (setInsert d dq) } with
           worklist = cons (q,d) graph.worklist }

  ---------------------
  -- PRETTY PRINTING --
  ---------------------

  sem constraintToString
  : CFAGraph -> PprintEnv -> Constraint -> (PprintEnv, String)

  sem absValToString: CFAGraph -> PprintEnv -> AbsVal -> (PprintEnv, String)

  -- Prints a CFA graph
  sem cfaGraphToString (env: PprintEnv) =
  | graph ->
    let graph: CFAGraph = graph in
    let f = lam env. lam e: (IName,AbsVal).
      match pprintVarIName graph.im env e.0 with (env,n) in
      match absValToString graph env e.1 with (env,av) in
      (env,join ["(", n, ", ", av, ")"]) in
    match mapAccumL f env graph.worklist with (env,worklist) in
    match mapAccumL (lam env: PprintEnv. lam b:(IName,Set AbsVal).
        match pprintVarIName graph.im env b.0 with (env,b0) in
        match mapAccumL (absValToString graph) env (setToSeq b.1) with (env,b1)
        in (env,(b0,b1))
      ) env (mapi (lam i. lam x. (i,x)) graph.data)
    with (env, data) in
    match mapAccumL (lam env: PprintEnv. lam b:(IName,[Constraint]).
        match pprintVarIName graph.im env b.0 with (env,b0) in
        match mapAccumL (constraintToString graph) env b.1 with (env,b1) in
        (env,(b0,b1))
      ) env (mapi (lam i. lam x. (i,x)) graph.edges)
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

  sem initConstraint (graph: CFAGraph) =
  | CstrInit r -> addData graph r.lhs r.rhs
  | CstrDirect r & cstr -> initConstraintName r.lhs graph cstr
  | CstrDirectAv r & cstr -> initConstraintName r.lhs graph cstr
  | CstrDirectAvCstrs r & cstr -> initConstraintName r.lhs graph cstr

  sem constraintToString graph (env: PprintEnv) =
  | CstrInit { lhs = lhs, rhs = rhs } ->
    match absValToString graph env lhs with (env,lhs) in
    match pprintVarIName graph.im env rhs with (env,rhs) in
    (env, join ["{", lhs, "}", " ⊆ ", rhs])
  | CstrDirect { lhs = lhs, rhs = rhs } ->
    match pprintVarIName graph.im env lhs with (env,lhs) in
    match pprintVarIName graph.im env rhs with (env,rhs) in
    (env, join [lhs, " ⊆ ", rhs])
  | CstrDirectAv { lhs = lhs, lhsav = lhsav, rhs = rhs, rhsav = rhsav } ->
    match pprintVarIName graph.im env lhs with (env,lhs) in
    match absValToString graph env lhsav with (env,lhsav) in
    match pprintVarIName graph.im env rhs with (env,rhs) in
    match absValToString graph env rhsav with (env,rhsav) in
    (env, join ["{", lhsav ,"} ⊆ ", lhs, " ⇒ {", rhsav ,"} ⊆ ", rhs])
  | CstrDirectAvCstrs { lhs = lhs, lhsav = lhsav, rhs = rhs } ->
    match mapAccumL (constraintToString graph) env rhs with (env,rhs) in
    let rhs = strJoin " AND " rhs in
    match pprintVarIName graph.im env lhs with (env,lhs) in
    match absValToString graph env lhsav with (env,lhsav) in
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

  sem generateConstraints im =
  | TmLet { ident = ident, body = TmVar t, info = info } ->
    [ CstrDirect {
        lhs = name2int im t.info t.ident,
        rhs = name2int im info ident
      } ]

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

  sem generateConstraints im =
  | TmLet { ident = ident, body = TmLam t, info = info } ->
    let av: AbsVal = AVLam {
      ident = name2int im t.info t.ident,
      body = name2int im (infoTm t.body) (exprName t.body)
    } in
    [ CstrInit { lhs = av, rhs = name2int im info ident } ]

  sem absValToString graph (env: PprintEnv) =
  | AVLam { ident = ident, body = body } ->
    match pprintVarIName graph.im env ident with (env,ident) in
    match pprintVarIName graph.im env body with (env,body) in
    (env, join ["lam ", ident, ". ", body])

end

lang LetCFA = CFA + LetAst
  sem exprName =
  | TmLet t -> exprName t.inexpr
end

lang RecLetsCFA = CFA + LamCFA + RecLetsAst
  sem exprName =
  | TmRecLets t -> exprName t.inexpr

  sem generateConstraints im =
  | TmRecLets { bindings = bindings } ->
    map (lam b: RecLetBinding.
      match b.body with TmLam t then
        let av: AbsVal = AVLam {
          ident = name2int im t.info t.ident,
          body = name2int im (infoTm t.body) (exprName t.body)
        } in
        CstrInit { lhs = av, rhs = name2int im b.info b.ident }
      else errorSingle [infoTm b.body] "Not a lambda in recursive let body"
    ) bindings

end

lang ConstCFA = CFA + ConstAst + BaseConstraint + Cmp

  syn AbsVal =
  -- Abstract representation of constants. Contains the constant and the
  -- arguments applied to it. It also includes the `let` name that binds the
  -- constant and syntactically distinguishes it from other of its kind in the
  -- program.
  | AVConst { id: IName, const: Const, args: [IName] }

  sem absValToString graph (env: PprintEnv) =
  | AVConst { id = id, const = const, args = args } ->
    let const = getConstStringCode 0 const in
    match mapAccumL (pprintVarIName graph.im) env args with (env,args) in
    let args = strJoin ", " args in
    match pprintVarIName graph.im env id with (env,id) in
    (env, join [const,"<", id, ">", "(", args, ")"])

  sem cmpAbsValH =
  | (AVConst lhs, AVConst rhs) ->
    let cmp = cmpConst lhs.const rhs.const in
    if eqi 0 cmp then
      let ncmp = subi lhs.id rhs.id in
      if eqi 0 ncmp then seqCmp subi lhs.args rhs.args
      else ncmp
    else cmp

  sem generateConstraints im =
  | TmLet { ident = ident, body = TmConst t, info = info } ->
    generateConstraintsConst t.info (name2int im info ident) t.val

  sem generateConstraintsConst: Info -> IName -> Const -> [Constraint]
  sem generateConstraintsConst info ident =
  | _ -> errorSingle [info] "Constant not supported in CFA"
end

lang AppCFA = CFA + ConstCFA + BaseConstraint + LamCFA + AppAst + MExprArity

  syn Constraint =
  -- {lam x. b} ⊆ lhs ⇒ (rhs ⊆ x and b ⊆ res)
  | CstrLamApp { lhs: IName, rhs: IName, res: IName }
  -- {const args} ⊆ lhs ⇒ {const args lhs} ⊆ res
  | CstrConstApp { lhs: IName, rhs: IName, res: IName }

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
    match update.1 with AVConst ({ const = const, args = args } & avc) then
      let arity = constArity const in
      let args = snoc args rhs in
      if eqi arity (length args) then
        -- Last application
        propagateConstraintConst res args graph const
      else
        -- Curried application, add the new argument
        addData graph (AVConst { avc with args = args }) res
    else graph

  sem constraintToString graph (env: PprintEnv) =
  | CstrLamApp { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarIName graph.im env lhs with (env,lhs) in
    match pprintVarIName graph.im env rhs with (env,rhs) in
    match pprintVarIName graph.im env res with (env,res) in
    (env, join [ "{lam >x<. >b<} ⊆ ", lhs, " ⇒ ", rhs, " ⊆ >x< AND >b< ⊆ ", res ])
  | CstrConstApp { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarIName graph.im env lhs with (env,lhs) in
    match pprintVarIName graph.im env rhs with (env,rhs) in
    match pprintVarIName graph.im env res with (env,res) in
    (env, join [
        ">const< >args< ⊆ ", lhs, " ⇒ ", ">const< >args< ", rhs, " ⊆ ", res
      ])

  sem generateConstraints im =
  | TmLet { ident = ident, body = TmApp app, info = info} ->
    match app.lhs with TmVar l then
      match app.rhs with TmVar r then
        let lhs = name2int im l.info l.ident in
        let rhs = name2int im r.info r.ident in
        let res = name2int im info ident in
        [ CstrLamApp {lhs = lhs, rhs = rhs,res = res},
          CstrConstApp {lhs = lhs, rhs = rhs,res = res}
        ]
      else errorSingle [infoTm app.rhs] "Not a TmVar in application"
    else errorSingle [infoTm app.lhs] "Not a TmVar in application"

  sem propagateConstraintConst : IName -> [IName] -> CFAGraph -> Const -> CFAGraph
end

lang RecordCFA = CFA + BaseConstraint + RecordAst
  -- NOTE(dlunde,2021-11-10) TmRecordUpdate is currently not supported.

  syn AbsVal =
  -- Abstract representation of records. The bindings are from SIDs to names,
  -- rather than expressions.
  | AVRec { bindings: Map SID IName }

  sem cmpAbsValH =
  | (AVRec { bindings = lhs }, AVRec { bindings = rhs }) ->
    mapCmp subi lhs rhs

  sem generateConstraints im =
  | TmLet { ident = ident, body = TmRecord t, info = info } ->
    let bindings = mapMap (lam v: Expr.
        match v with TmVar t then name2int im t.info t.ident
        else errorSingle [infoTm v] "Not a TmVar in record"
      ) t.bindings
    in
    let av: AbsVal = AVRec { bindings = bindings } in
    [ CstrInit { lhs = av, rhs = name2int im info ident } ]

  sem absValToString graph (env: PprintEnv) =
  | AVRec { bindings = bindings } ->
    match mapMapAccum (lam env. lam k. lam v.
        match pprintVarIName graph.im env v with (env, v) in
        (env, join [pprintLabelString k, " = ", v])
      ) env bindings
    with (env, bindings) in
    let binds = mapValues bindings in
    let merged = strJoin ", " binds in
    (env, join ["{ ", merged, " }"])

end

lang SeqCFA = CFA + BaseConstraint + SeqAst

  syn AbsVal =
  -- Abstract representation of sequences. Contains a set of names that may
  -- flow to the sequence.
  | AVSeq { names: Set IName }

  sem cmpAbsValH =
  | (AVSeq { names = lhs }, AVSeq { names = rhs }) -> setCmp lhs rhs

  sem generateConstraints im =
  | TmLet { ident = ident, body = TmSeq t, info = info } ->
    let names = foldl (lam acc: [IName]. lam t: Expr.
      match t with TmVar t then
        cons (name2int im t.info t.ident) acc
      else acc) [] t.tms
    in
    let av: AbsVal = AVSeq { names = setOfSeq subi names } in
    [ CstrInit { lhs = av, rhs = name2int im info ident } ]

  sem absValToString graph (env: PprintEnv) =
  | AVSeq { names = names } ->
    match mapAccumL (pprintVarIName graph.im) env (setToSeq names)
    with (env,names) in
    let names = strJoin ", " names in
    (env, join ["[{", names, "}]"])
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

  sem generateConstraints im =
  | TmLet { ident = ident, body = TmConApp t, info = info } ->
    let body =
      match t.body with TmVar v then name2int im v.info v.ident
      else errorSingle [infoTm t.body] "Not a TmVar in con app" in
    let av: AbsVal = AVCon { ident = name2int im t.info t.ident, body = body } in
    [ CstrInit { lhs = av, rhs = name2int im info ident } ]

  sem absValToString graph (env: PprintEnv) =
  | AVCon { ident = ident, body = body } ->
    match pprintConName env (int2name graph.im ident) with (env,ident) in
    match pprintVarIName graph.im env body with (env,body) in
    (env, join [ident, " ", body])

  sem exprName =
  | TmConDef t -> exprName t.inexpr

end

lang MatchCFA = CFA + BaseConstraint + MatchAst

  syn Constraint =
  | CstrMatch { id: IName, pat: Pat, target: IName }

  sem initConstraint (graph: CFAGraph) =
  | CstrMatch r & cstr -> initConstraintName r.target graph cstr

  sem propagateConstraint (update: (IName,AbsVal)) (graph: CFAGraph) =
  | CstrMatch r ->
    propagateMatchConstraint graph r.id (r.pat,update.1)

  sem propagateMatchConstraint: CFAGraph -> IName -> (Pat, AbsVal) -> CFAGraph
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | _ -> graph -- Default: do nothing

  sem constraintToString graph (env: PprintEnv) =
  | CstrMatch { id = id, pat = pat, target = target } ->
    match pprintVarIName graph.im env id with (env, id) in
    match getPatStringCode 0 env pat with (env, pat) in
    match pprintVarIName graph.im env target with (env, target) in
    (env, join [id, ": match ", target, " with ", pat])

  sem generateConstraintsMatch: IndexMap -> [MatchGenFun] -> Expr -> [Constraint]
  sem generateConstraintsMatch im (mcgfs: [MatchGenFun]) =
  | _ -> []
  | TmLet { ident = ident, body = TmMatch t, info = info } ->
    let thn = name2int im (infoTm t.thn) (exprName t.thn) in
    let els = name2int im (infoTm t.els) (exprName t.els) in
    let ident = name2int im info ident in
    let cstrs = [
      CstrDirect { lhs = thn, rhs = ident },
      CstrDirect { lhs = els, rhs = ident }
    ] in
    match t.target with TmVar tv then
      foldl (lam acc. lam f.
          concat (f ident (name2int im tv.info tv.ident) t.pat) acc
        ) cstrs mcgfs
    else errorSingle [infoTm t.target] "Not a TmVar in match target"

  sem generateMatchConstraints: IName -> IName -> Pat -> [Constraint]
  sem generateMatchConstraints (id: IName) (target: IName) =
  | pat -> [ CstrMatch { id = id, pat = pat, target = target } ]

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
  | AVExt { ext: IName, arity: Int, args: [IName] }

  sem absValToString graph (env: PprintEnv) =
  | AVExt { ext = ext, args = args } ->
    -- We ignore the arity (one can simply look up the ext to get the arity)
    match mapAccumL (pprintVarIName graph.im) env args with (env,args) in
    let args = strJoin ", " args in
    match pprintVarIName graph.im env ext with (env,ext) in
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
  sem collectConstraints cgfs acc =
  | TmExt { inexpr = TmLet { ident = ident, inexpr = inexpr } } & t ->
    let acc = foldl (lam acc. lam f. concat (f t) acc) acc cgfs in
    sfold_Expr_Expr (collectConstraints cgfs) acc inexpr

  sem generateConstraints im =
  | TmExt { inexpr = TmLet { ident = ident, inexpr = inexpr } } ->
    -- NOTE(dlunde,2022-06-15): Currently, we do not generate any constraints
    -- for externals. Similarly to constants, we probably want to delegate to
    -- `generateConstraintsExts` here. As with `propagateConstraintExt`, it is
    -- not clear where the `generateConstraintsExts` function should be defined.
    --
    []

  sem exprName =
  | TmExt t -> exprName t.inexpr

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
  sem generateConstraintsConst info ident =
  | CInt _ -> []
end

lang ArithIntCFA = CFA + ConstCFA + ArithIntAst
  sem generateConstraintsConst info ident =
  | CAddi _ -> []
  | CSubi _ -> []
  | CMuli _ -> []
  | CDivi _ -> []
  | CNegi _ -> []
  | CModi _ -> []
end

lang ShiftIntCFA = CFA + ConstCFA + ShiftIntAst
  sem generateConstraintsConst info ident =
  | CSlli _ -> []
  | CSrli _ -> []
  | CSrai _ -> []
end

lang FloatCFA = CFA + ConstCFA + FloatAst
  sem generateConstraintsConst info ident =
  | CFloat _ -> []
end

lang ArithFloatCFA = CFA + ConstCFA + ArithFloatAst
  sem generateConstraintsConst info ident =
  | CAddf _ -> []
  | CSubf _ -> []
  | CMulf _ -> []
  | CDivf _ -> []
  | CNegf _ -> []
end

lang FloatIntConversionCFA = CFA + ConstCFA + FloatIntConversionAst
  sem generateConstraintsConst info ident =
  | CFloorfi _ -> []
  | CCeilfi _ -> []
  | CRoundfi _ -> []
  | CInt2float _ -> []
end

lang BoolCFA = CFA + ConstCFA + BoolAst
  sem generateConstraintsConst info ident =
  | CBool _ -> []
end

lang CmpIntCFA = CFA + ConstCFA + CmpIntAst
  sem generateConstraintsConst info ident =
  | CEqi _ -> []
  | CNeqi _ -> []
  | CLti _ -> []
  | CGti _ -> []
  | CLeqi _ -> []
  | CGeqi _ -> []
end

lang CmpFloatCFA = CFA + ConstCFA + CmpFloatAst
  sem generateConstraintsConst info ident =
  | CEqf _ -> []
  | CLtf _ -> []
  | CLeqf _ -> []
  | CGtf _ -> []
  | CGeqf _ -> []
  | CNeqf _ -> []
end

lang CharCFA = CFA + ConstCFA + CharAst
  sem generateConstraintsConst info ident =
  | CChar _ -> []
end

lang CmpCharCFA = CFA + ConstCFA + CmpCharAst
  sem generateConstraintsConst info ident =
  | CEqc _ -> []
end

lang IntCharConversionCFA = CFA + ConstCFA + IntCharConversionAst
  sem generateConstraintsConst info ident =
  | CInt2Char _ -> []
  | CChar2Int _ -> []
end

lang FloatStringConversionCFA = CFA + ConstCFA + FloatStringConversionAst
  sem generateConstraintsConst info ident =
  | CStringIsFloat _ -> []
  | CString2float _ -> []
  | CFloat2string _ -> []
end

lang SymbCFA = CFA + ConstCFA + SymbAst
  sem generateConstraintsConst info ident =
  | CSymb _ -> []
  | CGensym _ -> []
  | CSym2hash _ -> []
end

lang CmpSymbCFA = CFA + ConstCFA + CmpSymbAst
  sem generateConstraintsConst info ident =
  | CEqsym _ -> []
end

lang SeqOpCFA = CFA + ConstCFA + SeqCFA + SeqOpAst + BaseConstraint

  syn Constraint =
  -- [{names}] ⊆ lhs ⇒ ∀n ∈ names: {n} ⊆ rhs
  | CstrSeq {lhs : IName, rhs : IName}
  -- [{names}] ⊆ lhs ⇒ [{names} ∪ {rhs}] ⊆ res
  | CstrSeqUnion {lhs : IName, rhs : IName, res : IName}

  sem initConstraint (graph: CFAGraph) =
  | CstrSeq r & cstr -> initConstraintName r.lhs graph cstr
  | CstrSeqUnion r & cstr -> initConstraintName r.lhs graph cstr

  sem constraintToString graph (env: PprintEnv) =
  | CstrSeq { lhs = lhs, rhs = rhs } ->
    match pprintVarIName graph.im env lhs with (env,lhs) in
    match pprintVarIName graph.im env rhs with (env,rhs) in
    (env, join [ "[{names}] ⊆ ", lhs, " ⇒ ∀n ∈ names: {n} ⊆ ", rhs ])
  | CstrSeqUnion { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarIName graph.im env lhs with (env,lhs) in
    match pprintVarIName graph.im env rhs with (env,rhs) in
    match pprintVarIName graph.im env res with (env,res) in
    (env, join [
        "[{names}] ⊆ ", lhs, " ⇒ [{names} ∪ { ", rhs," }] ⊆ ", res
      ])

  sem propagateConstraint (update: (IName,AbsVal)) (graph: CFAGraph) =
  | CstrSeq { lhs = lhs, rhs = rhs } ->
    match update.1 with AVSeq { names = names } then
      setFold (lam graph. lam name.
          initConstraint graph (CstrDirect {lhs = name, rhs = rhs})
        ) graph names
    else graph
  | CstrSeqUnion { lhs = lhs, rhs = rhs, res = res } ->
    match update.1 with AVSeq { names = names } then
      addData graph (AVSeq {names = setInsert rhs names}) res
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
  -- | ( CMap _
  --   | CMapi _
  --   | CIter _
  --   | CIteri _
  --   | CFoldl _
  --   | CFoldr _
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
end

lang FileOpCFA = CFA + ConstCFA + FileOpAst
  sem generateConstraintsConst info ident =
  | CFileRead _ -> []
  | CFileWrite _ -> []
  | CFileExists _ -> []
  | CFileDelete _ -> []
end

lang IOCFA = CFA + ConstCFA + IOAst
  sem generateConstraintsConst info ident =
  | CPrint _ -> []
  | CPrintError _ -> []
  | CDPrint _ -> []
  | CFlushStdout _ -> []
  | CFlushStderr _ -> []
  | CReadLine _ -> []
  | CReadBytesAsString _ -> []
end

lang RandomNumberGeneratorCFA = CFA + ConstCFA + RandomNumberGeneratorAst
  sem generateConstraintsConst info ident =
  | CRandIntU _ -> []
  | CRandSetSeed _ -> []
end

lang SysCFA = CFA + ConstCFA + SysAst
  sem generateConstraintsConst info ident =
  | CExit _ -> []
  | CError _ -> []
  | CArgv _ -> []
  | CCommand _ -> []
end

lang TimeCFA = CFA + ConstCFA + TimeAst
  sem generateConstraintsConst info ident =
  | CWallTimeMs _ -> []
  | CSleepMs _ -> []
end

lang ConTagCFA = CFA + ConstCFA + ConTagAst
  sem generateConstraintsConst info ident =
  | CConstructorTag _ -> []
end

-- TODO(dlunde,2021-11-11): Mutability complicates the analysis, but could
-- probably be added.
lang RefOpCFA = CFA + ConstCFA + RefOpAst
  sem generateConstraintsConst info ident =
  -- | CRef _ -> []
  -- | CModRef _ -> []
  -- | CDeRef _ -> []
end

-- TODO(dlunde,2021-11-11): Add flow constraints for maps and map operations?
lang MapCFA = CFA + ConstCFA + MapAst
  sem generateConstraintsConst info ident =
  -- | CMapEmpty _ -> []
  -- | CMapInsert _ -> []
  -- | CMapRemove _ -> []
  -- | CMapFindExn _ -> []
  -- | CMapFindOrElse _ -> []
  -- | CMapFindApplyOrElse _ -> []
  -- | CMapBindings _ -> []
  -- | CMapChooseExn _ -> []
  -- | CMapChooseOrElse _ -> []
  -- | CMapSize _ -> []
  -- | CMapMem _ -> []
  -- | CMapAny _ -> []
  -- | CMapMap _ -> []
  -- | CMapMapWithKey _ -> []
  -- | CMapFoldWithKey _ -> []
  -- | CMapEq _ -> []
  -- | CMapCmp _ -> []
  -- | CMapGetCmpFun _ -> []
end

-- TODO(dlunde,2021-11-11): Mutability complicates the analysis, but could
-- probably be added.
lang TensorOpCFA = CFA + ConstCFA + TensorOpAst
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

lang BootParserCFA = CFA + ConstCFA + BootParserAst
  sem generateConstraintsConst info ident =
  | CBootParserParseMExprString _ -> []
  | CBootParserParseMCoreFile _ -> []
  | CBootParserGetId _ -> []
  | CBootParserGetTerm _ -> []
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

lang NamedPatCFA = MatchCFA + NamedPat + BaseConstraint
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatNamed { ident = PName n, info = info }, av) ->
    propagateDirectConstraint (name2int graph.im info n) graph av
  | (PatNamed { ident = PWildcard _ }, _) -> graph
end

lang SeqTotPatCFA = MatchCFA + SeqCFA + SeqTotPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: IName) =
  | (PatSeqTot p, AVSeq { names = names }) ->
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
  | (PatSeqEdge p, AVSeq { names = names } & av) ->
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

---------------
-- MEXPR CFA --
---------------

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
  SysCFA + TimeCFA + ConTagCFA + RefOpCFA + MapCFA + TensorOpCFA +
  BootParserCFA +

  -- Patterns
  NamedPatCFA + SeqTotPatCFA + SeqEdgePatCFA + RecordPatCFA + DataPatCFA +
  IntPatCFA + CharPatCFA + BoolPatCFA + AndPatCFA + OrPatCFA + NotPatCFA
end

-----------
-- TESTS --
-----------

lang Test = MExprCFA + MExprANFAll + BootParser + MExprPrettyPrint

  -- Type: Expr -> CFAGraph
  sem initGraph (graphData : Option GraphData) =
  | t ->

    -- Initial graph
    let graph = emptyCFAGraph t in

    -- Initialize match constraint generating functions
    let graph = { graph with mcgfs = [generateMatchConstraints] } in

    -- Initialize constraint generating functions
    let cgfs = [ generateConstraints graph.im,
                 generateConstraintsMatch graph.im graph.mcgfs ] in

    -- Recurse over program and generate constraints
    let cstrs: [Constraint] = collectConstraints cgfs [] t in

    -- Initialize all collected constraints
    let graph = foldl initConstraint graph cstrs in

    -- Return graph
    graph

end

mexpr
use Test in

-- Test functions --
let _parse = parseMExprStringKeywords [] in
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
      match cfaDebug (None ()) (Some env) tANF with (Some env,cfaRes) in
      match cfaGraphToString env cfaRes with (env, resStr) in
      printLn "\n--- FINAL CFA GRAPH ---";
      printLn resStr;
      (Some env,cfaRes)

    else
      -- Version without debug printouts
      let tANF = normalizeTerm t in
      let cfaRes = cfa tANF in
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

-- Sequence operations
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

()
