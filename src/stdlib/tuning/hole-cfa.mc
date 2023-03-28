-- Uses 0-CFA analysis for analyzing data-flow of holes in an MExpr program. The
-- final output is the set of holes that (may) affect the execution time, for
-- each labelled subexpression.
--
-- There are currently three ways in which execution time dependency is inferred:
-- 1. In a match, if the _condition is data-dependent_ on hole `h`, then the
--    _execution time_ of the match is dependent on `h`.
-- 2. In an application, if the lhs has a data-dependency on `h`, then the
--    execution time of the application is dependent on `h`.
-- 3. In the result of applying some intrinsic functions. For example, in
--    `sleepMs x`, if `x` is data-dependent, then the the application
--    is execution time dependent. The behaviour for each intrinsic function is
--    encoded in `const-dep.mc`.
--
-- Limitations:
-- * Some side-effects are not handled, e.g. parallelism and mutable data.
-- * Context depth of holes is not considered.

-- NOTE(Linnea, 2021-11-25): Currently, execution time dependency is not
-- propagated from a subexpression into its enclosing expression. For example:
-- ```
-- let h = hole (IntRange {default = 1, min = 1, max = 1}) in
-- let x =  -- { } ⊆ x
--   let y = sleepMs h in  -- { e(h) } ⊆ y
--   2
-- in
-- ()

include "mexpr/cfa.mc"
include "mexpr/const-arity.mc"
include "mexpr/symbolize.mc"
include "mexpr/cmp.mc"

include "name.mc"
include "common.mc"
include "tensor.mc"

include "ast.mc"
include "const-dep.mc"
include "context-expansion.mc"

lang MExprHoleCFA = HoleAst + MExprCFA + MExprArity

  syn AbsVal =
  | AVDHole { id : IName, contexts : Set Int }
  | AVEHole { id : IName, contexts : Set Int }
  | AVConstHole { const : Const, args : [IName] }

  syn GraphData =
  | HoleCtxEnv { env: CallCtxEnv }
  | HoleCtxInfo { contextMap : Map IName (Set Int),
                  prefixMap : Map IName (Map IName (Set Int)) }

  sem absValToStringH =
  | AVDHole _ -> "d"
  | AVEHole _ -> "e"

  sem absValToString im (env : PprintEnv) =
  | ( AVDHole {id = id, contexts = contexts}
    | AVEHole {id = id, contexts = contexts} ) & av ->
    match pprintVarIName im env id with (env,id) in
    (env, join [
        absValToStringH av, "hole", "(", id, ",{",
        strJoin "," (map int2string (setToSeq contexts)), "}", ")"
      ])
  | AVConstHole { const = const, args = args } ->
    let const = getConstStringCode 0 const in
    match mapAccumL (pprintVarIName im) env args with (env, args) in
    (env, join [const, "(", strJoin ", " args, ")"])

  sem isDirect =
  | AVEHole _ -> false

  sem directTransition (graph: CFAGraph) (rhs: Int) =
  | AVDHole ({id = id, contexts = contexts} & av) ->
    match graph with {graphData = graphData} in
    match graphData with Some (HoleCtxInfo c) then
      let labelMap = mapFindExn id c.prefixMap in
      match mapLookup rhs labelMap with Some ids then
        let newContexts = setIntersect contexts ids in
        AVDHole {av with contexts = newContexts}
      else AVDHole av
    else error "Expected context information in CFA graph"

  sem cmpAbsValH =
  | ( (AVDHole {id = id1, contexts = ctxs1},
       AVDHole {id = id2, contexts = ctxs2})
    | (AVEHole {id = id1, contexts = ctxs1},
       AVEHole {id = id2, contexts = ctxs2}) ) ->
    let ncmp = subi id1 id2 in
    if eqi 0 ncmp then setCmp ctxs1 ctxs2 else ncmp
  | (AVConstHole lhs, AVConstHole rhs) ->
    use ConstCmp in
    let cmp = cmpConst lhs.const rhs.const in
    if eqi 0 cmp then seqCmp subi lhs.args rhs.args
    else cmp

  syn Constraint =
    -- {dhole} ⊆ lhs ⇒ {dhole} ⊆ rhs
  | CstrHoleDirectData { lhs: IName, rhs: IName }
    -- {dhole} ⊆ lhs ⇒ {ehole} ⊆ rhs
  | CstrHoleDirectExe { lhs: IName, rhs: IName }
    -- {dhole} ⊆ lhs ⇒ ({dhole} ⊆ res) AND ({ehole} ⊆ res)
  | CstrHoleApp { lhs: IName, res: IName }
    -- ({const with args = args} ⊆ lhs AND |args| = arity(const)-1
    --    ⇒ ∀(a,i): (a,i) in ({args} ∪ {rhs} ⨯ [1,...,arity(const)]):
    --        if const is data dep on position i AND {dhole} ⊆ a ⇒ {dhole} ⊆ res
    --        AND
    --        if const is exe dep on position i AND {dhole} ⊆ a ⇒ {ehole} ⊆ res)
    -- AND
    -- ({const with args = args} ⊆ lhs AND |args| < arity(const)-1
    --    ⇒ {const with args = snoc args rhs } ⊆ res)
  | CstrHoleConstApp { lhs: IName, rhs : IName, res: IName }
    -- {dhole} ⊆ lhs ⇒ {ehole} ⊆ res
  | CstrHoleMatch { lhs: IName, res: IName }
    -- {dhole} ⊆ lhs ⇒ {dhole} ⊄ rhs
    -- lhs \ {dhole : dhole ∈ rhs} ⊆ res
  | CstrHoleIndependent { lhs: IName, rhs: IName, res: IName }

  sem cmpConstraintH =
  | (CstrHoleDirectData l, CstrHoleDirectData r) ->
    let d = subi l.lhs r.lhs in
    if eqi d 0 then subi l.rhs r.rhs
    else d
  | (CstrHoleDirectExe l, CstrHoleDirectExe r) ->
    let d = subi l.lhs r.lhs in
    if eqi d 0 then subi l.rhs r.rhs
    else d
  | (CstrHoleApp l, CstrHoleApp r) ->
    let d = subi l.res r.res in
    if eqi d 0 then subi l.lhs r.lhs
    else d
  | (CstrHoleConstApp l, CstrHoleConstApp r) ->
    let d = subi l.res r.res in
    if eqi d 0 then
      let d = subi l.lhs r.lhs in
      if eqi d 0 then subi l.rhs r.rhs
      else d
    else d
  | (CstrHoleMatch l, CstrHoleMatch r) ->
    let d = subi l.res r.res in
    if eqi d 0 then subi l.lhs r.lhs
    else d
  | (CstrHoleIndependent l, CstrHoleIndependent r) ->
    let d = subi l.res r.res in
    if eqi d 0 then
      let d = subi l.lhs r.lhs in
      if eqi d 0 then subi l.rhs r.rhs
      else d
    else d

  sem initConstraint (graph : CFAGraph) =
  | CstrHoleApp r & cstr -> initConstraintName r.lhs graph cstr
  | CstrHoleDirectData r & cstr -> initConstraintName r.lhs graph cstr
  | CstrHoleDirectExe r & cstr -> initConstraintName r.lhs graph cstr
  | CstrHoleConstApp r & cstr -> initConstraintName r.lhs graph cstr
  | CstrHoleMatch r & cstr -> initConstraintName r.lhs graph cstr
  | CstrHoleIndependent r & cstr -> initConstraintName r.lhs graph cstr

  sem propagateConstraint (update : (IName, AbsVal)) (graph : CFAGraph) =
  | CstrHoleDirectData { lhs = lhs, rhs = rhs } ->
    match update.1 with AVDHole _ & av then addData graph av rhs else graph
  | CstrHoleDirectExe { lhs = lhs, rhs = rhs } ->
    match update.1 with AVDHole a then addData graph (AVEHole a) rhs else graph
  | CstrHoleApp { lhs = lhs, res = res } ->
    match update.1 with AVDHole {id = id, contexts = contexts} & av then
      let graph = addData graph av res in
      addData graph (AVEHole {id = id, contexts = contexts}) res
    else graph
  | CstrHoleMatch { lhs = lhs, res = res } ->
    match update.1 with AVDHole {id = id, contexts = contexts}
    then addData graph (AVEHole {id = id, contexts = contexts}) res
    else graph
  -- OPT(Linnea,20222-05-10): Hook in to propagateConstraint for CstrConstApp in
  -- cfa.mc.
  | CstrHoleConstApp { lhs = lhs, rhs = rhs, res = res } ->
    use MExprConstDep in
    match update.1 with AVConstHole ({ const = const, args = args } & avc) then
      let arity = constArity const in
      let args = snoc args rhs in
      if eqi arity (length args) then
        -- Last application, analyse data and execution time
        let cdeps = constDep const in
        let graph = foldl (lam graph. lam argDep : (IName, (Bool, Bool)).
          let arg = argDep.0 in
          let dep = argDep.1 in
          let isDataDep = dep.0 in
          let isExeDep = dep.1 in
          -- Add data dependencies to the result
          let graph =
            if isDataDep then
              initConstraint graph (CstrHoleDirectData {lhs = arg, rhs = res})
            else graph
          in
          -- Add execution time dependencies the result
          let graph =
            if isExeDep then
              initConstraint graph (CstrHoleDirectExe {lhs = arg, rhs = res})
            else graph
          in
          graph) graph (zip args cdeps) in
        graph
      else
        -- Curried application, just add the new argument
        addData graph (AVConstHole { avc with args = args }) res
    else graph
  | CstrHoleIndependent { lhs = lhs, rhs = rhs, res = res } ->
    match update.1 with AVDHole _ & av then
      -- Only add the dependency if it is not part of rhs
      let d = dataLookup rhs graph in
      if setMem av d then graph
      else propagateDirectConstraint res graph av
    else propagateDirectConstraint res graph update.1

  sem generateHoleConstraints (graph: CFAGraphInit) =
  | _ -> graph
    -- Holes
  | TmLet { ident = ident, body = TmHole _, info = info} ->
    match graph with {graphData = graphData} in
    match graphData with Some (HoleCtxInfo {contextMap = contextMap}) then
      let ident = name2intAcc graph.ia info ident in
      let av = AVDHole {
        id = ident,
        contexts = mapFindExn ident contextMap
      } in
      let cstr = CstrInit {lhs = av, rhs = ident } in
      { graph with cstrs = cons cstr graph.cstrs }
    else errorSingle [info] "Expected context information"
  | TmLet { ident = ident, body = TmConst { val = c }, info = info } ->
    let arity = constArity c in
    let cstrs =
      if eqi arity 0 then []
      else [ CstrInit {
               lhs = AVConstHole { const = c, args = [] },
               rhs = name2intAcc graph.ia info ident } ]
    in
    { graph with cstrs = concat cstrs graph.cstrs }
  | TmLet { ident = ident, body = TmApp app, info = info } ->
    match app.lhs with TmVar l then
      match app.rhs with TmVar r then
        let lhs = name2intAcc graph.ia l.info l.ident in
        let rhs = name2intAcc graph.ia r.info r.ident in
        let ident = name2intAcc graph.ia info ident in
        let cstrs = [
          CstrHoleApp { lhs = lhs, res = ident},
          CstrHoleConstApp { lhs = lhs, rhs = rhs, res = ident }
        ] in
        { graph with cstrs = concat cstrs graph.cstrs }
      else errorSingle [infoTm app.rhs] "Not a TmVar in application"
    else errorSingle [infoTm app.lhs] "Not a TmVar in application"
  | TmLet { ident = ident, body = TmIndependent t, info = info} ->
    match t.lhs with TmVar lhs then
      match t.rhs with TmVar rhs then
        let lhs = name2intAcc graph.ia lhs.info lhs.ident in
        let rhs = name2intAcc graph.ia rhs.info rhs.ident in
        let ident = name2intAcc graph.ia info ident in
        let cstr = CstrHoleIndependent {lhs = lhs, rhs = rhs, res = ident} in
        { graph with cstrs = cons cstr graph.cstrs }
      else errorSingle [infoTm t.rhs] "Not a TmVar in independent annotation"
    else errorSingle [infoTm t.lhs] "Not a TmVar in independent annotation"

  sem constraintToString im (env: PprintEnv) =
  | CstrHoleDirectData { lhs = lhs, rhs = rhs } ->
    match pprintVarIName im env rhs with (env,rhs) in
    match pprintVarIName im env lhs with (env,lhs) in
    (env, join [ "{dhole} ⊆ ", lhs, " ⇒ {dhole} ⊆ ", rhs ])
  | CstrHoleDirectExe { lhs = lhs, rhs = rhs } ->
    match pprintVarIName im env rhs with (env,rhs) in
    match pprintVarIName im env lhs with (env,lhs) in
    (env, join [ "{dhole} ⊆ ", lhs, " ⇒ {ehole} ⊆ ", rhs ])
  | CstrHoleApp { lhs = lhs, res = res } ->
    match pprintVarIName im env lhs with (env,lhs) in
    match pprintVarIName im env res with (env,res) in
    (env, join [
      "{dhole} ⊆ ", lhs, " ⇒ {dhole} ⊆ ", res ])
  | CstrHoleMatch { lhs = lhs, res = res } ->
    match pprintVarIName im env lhs with (env,lhs) in
    match pprintVarIName im env res with (env,res) in
    (env, join [
      "{dhole} ⊆ ", lhs, " ⇒ {ehole} ⊆ ", res ])
  | CstrHoleConstApp { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarIName im env lhs with (env,lhs) in
    match pprintVarIName im env rhs with (env,rhs) in
    match pprintVarIName im env res with (env,res) in
    (env, join [
      "({const with args = args} ⊆ ", lhs, " AND |args| = arity(const)-1\n",
      "  ⇒ ∀(a,i): (a,i) in ({args} ∪ {", rhs, "} ⨯ [1,...,arity(const)]):\n",
      "    if const is data dep. on position i AND {dhole} ⊆ a ⇒ {dhole} ⊆ ", res, "\n",
      "    AND\n",
      "    if const is exe. dep. on position i AND {dhole} ⊆ a ⇒ {ehole} ⊆ ", res, ")\n",
      "AND\n",
      "({const with args = args} ⊆ ", lhs, " AND |args| < arity(const)-1\n",
      "  ⇒ {const with args = snoc args ", rhs, "} ⊆ ", res, ")"
    ])
  | CstrHoleIndependent { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarIName im env lhs with (env,lhs) in
    match pprintVarIName im env rhs with (env,rhs) in
    match pprintVarIName im env res with (env,res) in
    (env, join [lhs, " \\ {dhole : dhole ∈ ", rhs, "} ⊆ ", res])


  sem generateHoleMatchResConstraints (id: Int) (target: Int) =
  | ( PatSeqTot _
    | PatSeqEdge _
    | PatCon _
    | PatInt _
    | PatChar _
    | PatBool _
    | PatRecord _
    ) & pat -> [
      CstrHoleDirectData { lhs = target, rhs = id },
      CstrHoleMatch { lhs = target, res = id }
    ]
  | PatAnd p ->
    let lres = generateHoleMatchResConstraints id target p.lpat in
    let rres = generateHoleMatchResConstraints id target p.rpat in
    concat lres rres
  | PatOr p ->
    let lres = generateHoleMatchResConstraints id target p.lpat in
    let rres = generateHoleMatchResConstraints id target p.rpat in
    concat lres rres
  | PatNot p  -> []
  | _ -> []

  -- NOTE(Linnea, 2021-12-17): We need to handle references, since references
  -- are used in the graph coloring. By construction, these references
  -- operations are free from holes, so it is safe to assume no constraints.
  -- However, the analysis does not support references in the general case.
  sem generateConstraintsConst graph info ident =
  | CModRef _ -> graph

  sem generateHoleMatchConstraints (ia: IndexAcc) (id: Int) (target: Int) =
  | pat ->
    recursive let f = lam acc. lam pat.
      let acc =
        match pat with PatNamed { ident = PName name, info = info }
                     | PatSeqEdge { middle = PName name, info = info }
        then cons (name2intAcc ia info name) acc else acc in
      sfold_Pat_Pat f acc pat
    in
    let pnames = f [] pat in
    foldl (lam acc. lam name: IName.
      cons (CstrHoleDirectData { lhs = target, rhs = name }) acc
    ) [] pnames

  sem addHoleMatchConstraints =
  | graph ->
    -- Initialize match constraint generating functions
    { graph with mcgfs = concat [ generateHoleMatchConstraints graph.ia
                                , generateHoleMatchResConstraints
                                ]
                                graph.mcgfs }

  sem addHoleConstraints (graphData: GraphData) (graph: CFAGraphInit) =
  | t ->
    -- Initialize graph data
    match graphData with (HoleCtxEnv {env = env}) in
    let graph = {graph with graphData = Some (graphDataFromEnv graph.ia env)} in

    -- Initialize constraint generating functions
    let cgfs = [ generateHoleConstraints ] in

    -- Recurse over program and generate constraints
    let graph = collectConstraints cgfs graph t in

    graph

  sem holeCfa : GraphData -> Expr -> CFAGraph
  sem holeCfa gd =
  | t ->
    let graph = emptyCFAGraphInit t in
    let graph = addBaseMatchConstraints graph in
    let graph = addHoleMatchConstraints graph in
    let graph = addBaseConstraints graph t in
    let graph = addHoleConstraints gd graph t in
    solveCfa graph

  sem holeCfaDebug : GraphData -> PprintEnv -> Expr -> (PprintEnv, CFAGraph)
  sem holeCfaDebug gd pprintenv =
  | t ->
    let graph = emptyCFAGraphInit t in
    let graph = addBaseMatchConstraints graph in
    let graph = addHoleMatchConstraints graph in
    let graph = addBaseConstraints graph t in
    let graph = addHoleConstraints gd graph t in
    solveCfaDebug pprintenv graph

  sem graphDataInit: CallCtxEnv -> GraphData
  sem graphDataInit =
  | env -> HoleCtxEnv {env = env}

  sem graphDataFromEnv: IndexAcc -> CallCtxEnv -> GraphData
  sem graphDataFromEnv ia =
  | env ->
    -- Converts a prefix tree for a hole to a mapping from a call site to the
    -- set of contexts that pass through the call site.
    let treeToCallSiteCtxUnion
    : PTree NameInfo -> Map IName (Set Int) = lam tree.
      match tree with Node {children = children} then
        recursive let work = lam acc: Map IName (Set Int). lam children.
          mapFoldWithKey (lam acc. lam root. lam subtree.
            -- NOTE(Linnea, 2022-06-20): If a name is not mapped by an index, it
            -- is not part of the program, but a sentinel in the prefix tree.
            -- Thus, we will never look it up during CFA, and it is safe to not
            -- insert it in the map.
            if mapMem (nameInfoGetName root) ia.map then
              let r = name2intAcc ia (nameInfoGetInfo root) (nameInfoGetName root) in
              let s: Set Int =
                match mapLookup r acc with Some s
                then s else setEmpty subi in
              switch subtree
              case Leaf id then mapInsert r (setInsert id s) acc
              case Node {ids = ids, children = children} then
                let acc = work acc children in
                mapInsert r (
                    foldl (lam acc. lam id. setInsert id acc) s ids
                  ) acc
              end
            else acc) acc children
        in work (mapEmpty subi) children
      else error "Missing sentinel node"
    in

    let env : CallCtxEnv = env in

    -- Maps a hole to its set of contexts.
    let contextMap : Map IName (Set Int) =
      mapFoldWithKey
        (lam acc : Map IName (Set Int). lam n: NameInfo.
         lam vals : Map [NameInfo] Int.
           let n = name2intAcc ia (nameInfoGetInfo n) (nameInfoGetName n) in
           mapInsert n (setOfSeq subi (mapValues vals)) acc
        ) (mapEmpty subi) env.hole2idx
    in
    -- Maps a hole to its call site map.
    let prefixMap : Map IName (Map IName (Set Int)) =
      mapFoldWithKey
        (lam acc : Map IName (Map IName (Set Int)).
         lam n : NameInfo.
         lam tree : PTree NameInfo.
           let n = name2intAcc ia (nameInfoGetInfo n) (nameInfoGetName n) in
           mapInsert n (treeToCallSiteCtxUnion tree) acc
        ) (mapEmpty subi) env.contexts
    in
    HoleCtxInfo { contextMap = contextMap, prefixMap = prefixMap }
end

lang Test = MExprHoleCFA + BootParser + MExprANFAll + MExprSym + GraphColoring
end

lang MExpr
end

mexpr
use Test in

-- Test functions --

let debug = false in
let parse = lam str.
  let ast = parseMExprStringKeywordsExn holeKeywords str in
  let ast = makeKeywords ast in
  symbolize ast
in
let test
: Bool -> Expr -> [String] -> [(String, [AbsVal], Map NameInfo (Map [NameInfo] Int), IndexMap)] =
  lam debug: Bool. lam t: Expr. lam vars: [String].
    -- Use small ANF first, needed for context expansion
    let tANFSmall = use MExprHoles in normalizeTerm t in

    -- Do graph coloring to get context information (throw away the AST).
    match colorCallGraph [] tANFSmall with (env, _) in

    -- Initialize the graph data
    let graphData = graphDataInit env in

    -- Apply full ANF
    let tANF = normalizeTerm tANFSmall in

    if debug then
      -- Version with debug printouts
      match pprintCode 0 pprintEnvEmpty t with (_,tStr) in
      printLn "\n--- ORIGINAL PROGRAM ---";
      printLn tStr;
      match pprintCode 0 pprintEnvEmpty tANF with (pprintEnv,tANFStr) in
      printLn "\n--- ANF ---";
      printLn tANFStr;
      match holeCfaDebug graphData pprintEnv tANF with (pprintEnv,cfaRes) in
      match cfaGraphToString pprintEnv cfaRes with (_, resStr) in
      printLn "\n--- FINAL CFA GRAPH ---";
      printLn resStr;
      let cfaRes : CFAGraph = cfaRes in
      let avs : [(String, [AbsVal], Map NameInfo (Map [NameInfo] Int), IndexMap)] =
        map (lam var: String.
          let binds = mapi (lam i. lam s: Set AbsVal.
            (int2name cfaRes.im i, s)) (tensorToSeqExn cfaRes.data) in
          let res = foldl (lam acc. lam b : (Name, Set AbsVal).
            if eqString var (nameGetStr b.0) then setToSeq b.1 else acc
          ) [] binds in
          (var, res, env.hole2idx, cfaRes.im)
        ) vars
      in avs

    else
      -- Version without debug printouts
      let cfaRes : CFAGraph = holeCfa graphData tANF in
      let avs : [(String, [AbsVal], Map NameInfo (Map [NameInfo] Int), IndexMap)] =
        map (lam var: String.
          let binds = mapi (lam i. lam s: Set AbsVal.
            (int2name cfaRes.im i, s)) (tensorToSeqExn cfaRes.data) in
          let res = foldl (lam acc. lam b : (Name, Set AbsVal).
            if eqString var (nameGetStr b.0) then setToSeq b.1 else acc
          ) [] binds in
          (var, res, env.hole2idx, cfaRes.im)
        ) vars
      in avs
in

-- Custom equality function
type Dep = {d: [(String,[[String]])], e: [(String,[[String]])]} in
let gbl = lam s. (s,[[]]) in
let eqTestHole = eqSeq
  (lam t1:(String,[AbsVal],Map NameInfo (Map [NameInfo] Int),IndexMap).
   lam t2:(String,Dep).
     let index2Path : String -> Int -> [String] = lam str. lam i.
       let pathMap =
         match mapFoldWithKey (lam acc. lam nameInfo. lam bind.
           match acc with Some _ then acc
           else if eqString (nameInfoGetStr nameInfo) str then Some bind
           else acc
         ) (None ()) t1.2
         with Some pathMap then pathMap
         else error "impossible"
       in
       match mapFoldWithKey (lam acc. lam path. lam index.
         if eqi index i then Some (map nameInfoGetStr path)
         else acc
       ) (None ()) pathMap
       with Some path then path
       else error "impossible"
     in

     match t1 with (_,_,_,im) in
     if eqString t1.0 t2.0 then
       let data : [(String,Set Int)] = foldl (lam acc. lam av.
           match av with AVDHole {id = id, contexts = contexts}
           then
             let id = int2name im id in
             cons (nameGetStr id, contexts) acc else acc
         ) [] t1.1
       in
       let exe : [(String,Set Int)] = foldl (lam acc. lam av.
           match av with AVEHole {id = id, contexts = contexts}
           then
             let id = int2name im id in
             cons (nameGetStr id, contexts) acc else acc
         ) [] t1.1
       in
       let deps : Dep = t2.1 in
       -- Comparison of names
       let namesEq =
         let dataStrs = map (lam e : (String,Set Int). e.0) data in
         let exeStrs = map (lam e : (String,Set Int). e.0) exe in
         let depDataStrs = map (lam e : (String,[[String]]). e.0) deps.d in
         let depExeStrs = map (lam e : (String,[[String]]). e.0) deps.e in
         if setEq (setOfSeq cmpString dataStrs) (setOfSeq cmpString depDataStrs) then
           setEq (setOfSeq cmpString exeStrs) (setOfSeq cmpString depExeStrs)
         else false
       in
       -- Comparison of contexts
       if namesEq then
         let dataCtxs: [(String,[Int])] = map (lam e : (String,Set Int). (e.0, setToSeq e.1)) data in
         let dataCtxPaths = map (lam e : (String, [Int]). map (index2Path e.0) e.1) dataCtxs in
         let dataCtxPaths = map (setOfSeq (seqCmp cmpString)) dataCtxPaths in

         let exeCtxs = map (lam e : (String,Set Int). (e.0, setToSeq e.1)) exe in
         let exeCtxPaths = map (lam e : (String, [Int]). map (index2Path e.0) e.1) exeCtxs in
         let exeCtxPaths = map (setOfSeq (seqCmp cmpString)) exeCtxPaths in

         let depDataCtxs: [Set [String]] = map (lam e : (String,[[String]]). setOfSeq (seqCmp cmpString) e.1) deps.d in
         let depExeCtxs: [Set [String]] = map (lam e : (String,[[String]]). setOfSeq (seqCmp cmpString) e.1) deps.e in

         if setEq (setOfSeq setCmp dataCtxPaths) (setOfSeq setCmp depDataCtxs) then
           setEq (setOfSeq setCmp exeCtxPaths) (setOfSeq setCmp depExeCtxs)
         else false
       else false
     else false
) in
--------------------

let t = parse
"
let h1 = hole (Boolean {default = true}) in
let h2 = hole (Boolean {default = true}) in
let x = h1 in
let y = h2 in
x
"
in

utest test debug t ["h1", "h2", "x", "y"]
with [ ("h1", {d=[gbl "h1"], e=[]})
     , ("h2", {d=[gbl "h2"], e=[]})
     , ("x", {d=[gbl "h1"], e=[]})
     , ("y", {d=[gbl "h2"], e=[]})]
using eqTestHole in


let t = parse
"
let foo = lam.
  let h = hole (Boolean {default = true}) in
  h
in
let x = foo () in x
"
in

utest test debug t ["x"]
with [("x", {d=[gbl "h"], e=[]})]
using eqTestHole in


let t = parse
"
let foo = lam x.
  x
in
let h = hole (Boolean {default = true}) in
let y = foo h in y
"
in

utest test debug t ["x", "y"]
with [("x", {d=[gbl "h"], e=[]}), ("y", {d=[gbl "h"], e=[]})]
using eqTestHole in


let t = parse
"
let foo = lam x.
  let h = hole (Boolean {default = true}) in
  2
in
let h1 = hole (Boolean {default = true}) in
let y = foo 3 in
let z = foo h1 in
y
"
in

utest test debug t ["y", "z"]
with [("y", {d=[], e=[]}), ("z", {d=[], e=[]})]
using eqTestHole in


let t = parse
"
let h = hole (Boolean {default = true}) in
let x = if h then 1 else 2 in  -- rule 1
let y = if true then 1 else 2 in
let z = if true then h else 2 in
let a = match h with h1 then true else false in
let b = match h with h1 then h1 else false in
x
"
in

utest test debug t ["x", "y", "z", "a", "b", "h"]
with [ ("x", {d=[gbl "h"],e=[gbl "h"]})
     , ("y", {d=[],e=[]})
     , ("z", {d=[gbl "h"],e=[]})
     , ("a", {d=[], e=[]})
     , ("b", {d=[gbl "h"],e=[]})
     , ("h", {d=[gbl "h"],e=[]})
     ]
using eqTestHole in


let t = parse
"
let h = hole (Boolean {default = true}) in
let f = if h then lam x. x else lam x. x in
let a = f 1 in  -- rule 2
a
"
in

utest test debug t ["f", "a"]
with [ ("f", {d=[gbl "h"],e=[gbl "h"]})
     , ("a", {d=[gbl "h"],e=[gbl "h"]})
     ]
using eqTestHole in


let t = parse
"
let h1 = hole (IntRange {default = 1, min = 0, max = 1}) in
let h2 = hole (IntRange {default = 1, min = 0, max = 1}) in
let x = negi h1 in
let y = addi 3 x in
let y2 = addi h1 h2 in
let z = sleepMs y in
x
"
in

utest test false t ["x", "y", "z", "y2"]
with [ ("x", {d=[gbl "h1"],e=[]})
     , ("y", {d=[gbl "h1"],e=[]})
     , ("z", {d=[],e=[gbl "h1"]})
     , ("y2",{d=[gbl "h1", gbl "h2"],e=[]})
     ]
using eqTestHole in


let t = parse
"
let h = hole (Boolean {default = true}) in
let r = {x = h, y = 2} in
let a = r.x in
let b = if r.x then true else false in
let c = match r with {x = x, y = 2} then 2 else 42 in
let d = match r with {x = true} then 2 else 42 in
let e = r.y in
()
"
in

utest test debug t ["a", "b", "c", "d", "e"]
with [ ("a", {d=[gbl "h"],e=[]})
     , ("b", {d=[gbl "h"],e=[gbl "h"]})
     , ("c", {d=[],e=[]})
     , ("d", {d=[gbl "h"],e=[gbl "h"]})
     , ("e", {d=[],e=[]})
     ]
using eqTestHole in


let t = parse
"
let f = lam y. let z = if y then 1 else 2 in z in
let h = hole (Boolean {default = true}) in
let x = f h in
x
"
in

utest test debug t ["x", "z"]
with [ ("x", {d=[gbl "h"],e=[]})
     , ("z", {d=[gbl "h"],e=[gbl "h"]})
     ]
using eqTestHole in


let t = parse
"
let h = hole (Boolean {default = true}) in
let res = match h with a & b then 1 else 2 in
let res2 = match h with c & true then 1 else 2 in
()
"
in

utest test debug t ["a", "b", "c", "res", "res2"]
with [ ("a", {d=[gbl "h"],e=[]})
     , ("b", {d=[gbl "h"],e=[]})
     , ("c", {d=[gbl "h"],e=[]})
     , ("res", {d=[],e=[]})
     , ("res2", {d=[gbl "h"],e=[gbl "h"]})
     ]
using eqTestHole in


let t = parse
"
type T in
con C: Bool -> T in
let h = hole (Boolean {default = true}) in
let p = C h in
let res = match h with a | true then 1 else 2 in
let res2 = match p with C true | C false then 1 else 2 in
let res3 = match p with C aa | (C true & aa) then 1 else 2 in
()
"
in

utest test debug t ["res", "res2", "res3", "aa"]
with [ ("res", {d=[gbl "h"],e=[gbl "h"]})
     , ("res2", {d=[gbl "h"],e=[gbl "h"]})
     , ("res3", {d=[gbl "h"],e=[gbl "h"]})
     , ("aa", {d=[gbl "h"],e=[]})
     ]
using eqTestHole in


let t = parse
"
let h1 = hole (IntRange {default = 1, min = 1, max = 2}) in
let h2 = hole (IntRange {default = 1, min = 1, max = 2}) in
let h3 = hole (IntRange {default = 1, min = 1, max = 2}) in

let f = lam x. lam y.
  addi x y
in
let a = f h1 1 in
let b = f 1 h2 in
let c = f h1 h2 in
let d = f h2 h3 in
()
" in

utest test debug t ["a", "b", "c", "d"]
with [ ("a",{d=map gbl ["h1","h2","h3"],e=[]})
     , ("b",{d=map gbl ["h1","h2","h3"],e=[]})
     , ("c",{d=map gbl ["h1","h2","h3"],e=[]})
     , ("d",{d=map gbl ["h1","h2","h3"],e=[]})
     ]
using eqTestHole in


let t = parse
"
-- Direct data-flow --
let h = hole (Boolean {default = true}) in
let x1 = h in -- { d(h) } ⊆ x1

-- Applications --
let f1 = lam x. x in
let x2 = f1 h in -- { d(h) } ⊆ x2
-- Limitation of 0-CFA: x22 gets d(h) because of above application
let x22 = f1 3 in -- { d(h) } ⊆ x22

let f2 = lam x. 3 in
let x3 = f2 h in -- { } ⊆ x3

-- Matches --
let r = {a = h, b = false} in
-- x4 is both data and execution time dependent. In a more exact analysis,
-- it should only be data dependent since the two branches have equal execution time.
let x4 = match r with {a = true} then 1 else 2 in -- { d(h), e(h) ⊆ x4 }
-- x5 is not dependent on h since the match can never fail
let x5 = match r with {a = a, b = false} then 1 else 2 in -- { } ⊆ x5

let f = lam x. let x111 = if x then 1 else 2 in x111 in -- { d(h), e(h) } ⊆ x10
let g = lam f. f h in
let x6 = g f in -- { d(h) } ⊆ x6

let f = if h then lam x. x else lam y. y in
-- Similar for x4, x0 should not have e(h).
-- Possibly, we could detect that it shouldn't have d(h) either.
let x0 = f 1 in  -- { d(h), e(h) } ⊆ x0

-- Constants --
let h1 = hole (IntRange {default = 1, min = 1, max = 2}) in
let h2 = hole (IntRange {default = 1, min = 1, max = 2}) in

let x7 = addi 1 h1 in  -- { d(h1) } ⊆ x7
let x8 = addi 1 h2 in -- { d(h2) } ⊆ x8
let x9 = addi h1 h2 in  -- { d(h1), d(h2) } ⊆ x9

()
" in
utest test debug t ["x1", "x2", "x22", "x3", "x4", "x5", "x6", "x0", "x7", "x8", "x9", "x111"]
with [ ("x1", {d=[gbl "h"],e=[]})
     , ("x2", {d=[gbl "h"],e=[]})
     , ("x22", {d=[gbl "h"],e=[]})
     , ("x3", {d=[],e=[]})
     , ("x4", {d=[gbl "h"],e=[gbl "h"]})
     , ("x5", {d=[],e=[]})
     , ("x6", {d=[gbl "h"],e=[]})
     , ("x0", {d=[gbl "h"],e=[gbl "h"]})
     , ("x7", {d=[gbl "h1"],e=[]})
     , ("x8", {d=[gbl "h2"],e=[]})
     , ("x9", {d=[gbl "h1", gbl "h2"],e=[]})
     , ("x111", {d=[gbl "h"],e=[gbl "h"]})
     ]
using eqTestHole
in


let t = parse
"
let h = hole (IntRange {default = 1, min = 1, max = 1}) in
let x =
  let y = sleepMs h in  -- rule 3
  2
in
x
" in

utest test debug t ["x", "y"]
with [ ("x", {d=[], e=[]})
     , ("y", {d=[], e=[gbl "h"]})
     ]
using eqTestHole
in


-- Tests that NamedPatCFA does not transfer e-dep to wild cards
let t = parse
"
let h = hole (Boolean {default = true}) in
let a = sleepMs h in
let b = match a with c in c in
()
" in

utest test debug t ["a", "b", "c"]
with [ ("a", {d=[],e=[gbl "h"]})
     , ("b", {d=[],e=[]})
     , ("c", {d=[],e=[]})
     ]
using eqTestHole
in


-- Match on records
let t = parse
"
let r =
  let h = hole (Boolean {default = true}) in
  if h then
    { a = 1, b = 2 }
  else
    { a = 2, b = 1 }
in
let res =
  match r with { a = 1, b = 2 } then
    let t1 = 1 in
    t1
  else
    let t2 = 1 in
    t2
in
res
" in

utest test debug t ["t1", "t2", "res"]
with
[ ("t1", {d=[],e=[]})
, ("t2", {d=[],e=[]})
, ("res", {d=[gbl "h"],e=[gbl "h"]})
]
using eqTestHole
in

-- TODO(Linnea,2021-11-22): test sequences, maps

-- Context-sensitivity
let t = parse
"
let f1 = lam x.
  let h = hole (Boolean {default = true, depth = 2}) in
  h
in
let f2 = lam x.
  let a = f1 x in
  let b = f1 x in
  let c = addi a b in
  c
in
let f3 = lam f.
  f 1
in
let d = f2 1 in
let e = f2 1 in
let f = addi d e in
let g = sleepMs f in
let i = f3 f2 in
()
" in

utest test debug t
[ "a"
, "b"
, "c"
, "d"
, "e"
, "f"
, "g"
, "i"
]
with
[ ("a", {d=[ ("h", [["d","a"], ["e","a"]]) ],e=[]})
, ("b", {d=[ ("h", [["d","b"], ["e","b"]]) ],e=[]})
, ("c", {d=[ ("h", [["d","a"], ["e","a"]])
           , ("h", [["d","b"], ["e","b"]])
           ],
         e=[]})
, ("d", {d=[ ("h", [["d","a"]])
           , ("h", [["d","b"]])
           ],
         e=[]})
, ("e", {d=[ ("h", [["e","a"]])
           , ("h", [["e","b"]])
           ],
         e=[]})
, ("f", {d=[ ("h", [["d","a"]])
           , ("h", [["d","b"]])
           , ("h", [["e","a"]])
           , ("h", [["e","b"]])
           ],
         e=[]})
, ("g", {e=[ ("h", [["d","a"]])
           , ("h", [["d","b"]])
           , ("h", [["e","a"]])
           , ("h", [["e","b"]])
           ],
         d=[]})
-- 'i' gets the same as 'e'
, ("i", {d=[ ("h", [["d","a"], ["e","a"]])
           , ("h", [["d","b"], ["e","b"]])
           ],
         e=[]})
]
using eqTestHole
in

-- Tests for independency annotation
let t = parse
"
let x = hole (Boolean {default = true}) in
let y = if x then 1 else 2 in
let z = independent y x in
()
"
in

utest test debug t ["x","y","z"] with
[ ("x", {d=[gbl "x"],e=[]})
, ("y", {d=[gbl "x"],e=[gbl "x"]})
, ("z", {d=[],e=[]})
]
using eqTestHole in


let t = parse
"
let and: Bool -> Bool -> Bool =
  lam a. lam b. if a then b else false
in

let x1 = hole (Boolean {default = true}) in
let x2 = hole (Boolean {default = true}) in
let y = if and x1 x2 then 1 else 2 in
let z1 = independent y x1 in
let z2 = independent y x2 in
let z3 = independent z1 x2 in
let z4 = independent z1 x1 in
()
"
in

utest test debug t ["x1", "x2", "y", "z1", "z2", "z3", "z4"] with
[ ("x1", {d=[gbl "x1"],e=[]})
, ("x2", {d=[gbl "x2"],e=[]})
, ("y", {d=[gbl "x1", gbl "x2"],e=[gbl "x1", gbl "x2"]})
, ("z1", {d=[gbl "x2"],e=[]})
, ("z2", {d=[gbl "x1"],e=[]})
, ("z3", {d=[],e=[]})
, ("z4", {d=[gbl "x2"],e=[]})
]
using eqTestHole in


let t = parse
"
let x = hole (Boolean {default = true}) in
let f = lam y. x in
let i = independent f x in
let r = i 1 in
()
"
in

utest test debug t ["i", "r"] with
[ ("i", {d=[],e=[]})
, ("r", {d=[gbl "x"],e=[]})
]
using eqTestHole in

()
