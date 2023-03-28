-- Dependency analysis of a program with holes. The input is the result from
-- 0-CFA, and the output is a bipartite dependency graph (H,M,E), where H is the
-- set of context-sensitive holes, M is the set of context-sensitive measuring
-- points, and E are the set of edges. There is an edge (h,m)∈E if h affects m.

include "hole-cfa.mc"
include "prefix-tree.mc"
include "nested.mc"

include "graph.mc"
include "set.mc"
include "name.mc"

type DependencyGraph = {
  -- A bipartite graph from context-expanded holes to measuring points (labels
  -- unused)
  graph : Graph Int Int,

  -- Maps a context-sensitive measuring point to its prefix tree, which gives a
  -- compact representation of the context strings
  measuringPoints : Map Name (PTree NameInfo),

  -- Maps a base measuring point to the closest enclosing function in the call
  -- graph in which it occurs
  meas2fun: Map Name Name,

  -- The offset (from zero) of the indices of the measuring points
  offset: Int,

  -- The total number of context-sensitive measuring points
  nbrMeas: Int,

  -- The currently 'alive' measuring points are those that are considered to
  -- affect the total execution time of the program
  alive: Set Int
}

let _dependencyGraphEmpty =
  { graph = graphEmpty subi eqi
  , measuringPoints = mapEmpty nameCmp
  , meas2fun = mapEmpty nameCmp
  , offset = 0
  , nbrMeas = 0
  , alive = setEmpty subi
  }

lang DependencyAnalysis = MExprHoleCFA
  sem analyzeDependency (env : CallCtxEnv) (cfaGraph : CFAGraph) =
  | t ->
    -- Start the indexing of measuring points from the number of
    -- context-sensitive holes, to guarantee no collision in indices (to be able
    -- to store both sets as vertices in a graph).
    let nHoles = length env.idx2hole in
    match
      buildDependencies callGraphTop env (cfaGraphData cfaGraph)
        (_dependencyGraphEmpty, nHoles) t
    with ((graph, _), _) in
    let graph : DependencyGraph = graph in
    let nMeas = mapFoldWithKey (
      lam acc: Int. lam. lam tree: PTree NameInfo.
        addi acc (length (prefixTreeGetIds tree []))
      ) 0 graph.measuringPoints
    in
    let alive = setOfSeq subi (map (addi nHoles) (create nMeas (lam i. i))) in
    { { { graph with offset = nHoles }
                with nbrMeas = nMeas }
                with alive = alive }

  sem buildDependencies (cur : NameInfo) (env : CallCtxEnv)
                        (data : Map Name (Set AbsVal))
                        (acc : (DependencyGraph, Int)) =
  | TmLet ({ident = ident} & t) ->
    match acc with (graph, measCount) in
    let graph : DependencyGraph = graph in

    -- Function to keep the part of a path that happened before the current node
    -- in the call history
    recursive let shortenPath = lam path. lam acc.
      match path with [] then [] else
      match path with [(from,to,lbl)] ++ path in
        if nameInfoEq cur to then snoc acc (from,to,lbl)
        else shortenPath path (snoc acc (from,to,lbl))
    in

    -- Update 'cur' when recursing in body if defining a function that is part
    -- of the call graph.
    let curBody =
      match t.body with TmLam lm then
        if graphHasVertex (ident, t.info) env.callGraph then (ident, t.info)
        else cur
      else cur
    in

    -- Update dependency graph from CFA dependencies
    let acc =
      match mapLookup ident data with Some deps then
        match
          setFold (lam acc : (DependencyGraph, Map Int [NameInfo]). lam av.
            match av with AVEHole {id = id, contexts = contexts} then
              setFold (lam acc. lam c.
                match acc with (graph, shortContexts) in
                let graph : DependencyGraph = graph in

                -- Assert contexts are unique
                utest mapMem c shortContexts with false in

                -- The part of the context string that happened before the
                -- current node in the call graph.
                let shortPath : Path = shortenPath (mapFindExn c env.verbosePath) [] in
                let lblPath : [NameInfo] = map (lam e : Edge. e.2) shortPath in

                -- Insert base hole in the graph, and accumulate context
                ( graph,
                  mapInsert c lblPath shortContexts )
              ) acc contexts
            else acc
          ) (graph, mapEmpty subi) deps
        with (graph, shortContexts) in
        let graph : DependencyGraph = graph in

        -- Compute measuring contexts and dependency graph
        if mapIsEmpty shortContexts then (graph, measCount)
        else
          -- Build a prefix tree with measuring contexts
          match mapFoldWithKey (lam treeId. lam. lam path.
              match treeId with (tree,id) in
              switch prefixTreeMaybeInsert nameInfoCmp tree id (reverse path)
              case (true,tree) then (tree, addi id 1)
              case (false,_) then (tree, id)
              end
            ) ( prefixTreeEmpty nameInfoCmp (nameSym "", NoInfo ()),
                 measCount ) shortContexts
          with (tree, newMeasCount) in
          -- For each context-sensitive hole, add an edge to the set of
          -- measuring id's it affects
          let graphGraph = mapFoldWithKey (
            lam acc: Graph Int Int. lam id: Int. lam path: [NameInfo].
              -- Set of measuring points that this context string affects.
              let measPoints : [Int] = prefixTreeGetIds tree (reverse path) in
              -- Add context-expanded hole to dependency graph
              let acc = graphMaybeAddVertex id acc in
              -- Add corresponding edges to dependency graph
              foldl (lam acc : Graph Int Int. lam mp: Int.
                let acc = graphMaybeAddVertex mp acc in
                graphAddEdge id mp 0 acc
              ) acc measPoints
            ) graph.graph shortContexts
          in
          let measContexts = mapInsert ident tree graph.measuringPoints in
          ( { { { graph with measuringPoints = measContexts }
                        with graph = graphGraph }
                        with meas2fun = mapInsert ident (nameInfoGetName curBody) graph.meas2fun},
            newMeasCount )

      else (graph, measCount)
    in

    match buildDependencies curBody env data acc t.body with (acc, body) in
    match buildDependencies cur env data acc t.inexpr with (acc, inexpr) in
    (acc, TmLet {{t with body = body} with inexpr = inexpr})

  -- Possibly update cur inside bodies of bindings
  | TmRecLets ({ bindings = bindings, inexpr = inexpr } & t) ->
    match
      mapAccumL (lam acc : (DependencyGraph, Int). lam bind : RecLetBinding.
        let curBody =
          match bind with {body = TmLam lm, ident = ident} then
            if graphHasVertex (ident, t.info) env.callGraph then
              (ident, t.info)
            else cur
          else cur
        in
        match buildDependencies curBody env data acc bind.body
        with (acc, body) in
        (acc, { bind with body = body })
      ) acc bindings
    with (acc, newBinds) in
    match buildDependencies cur env data acc inexpr with (acc, inexpr) in
    ( acc,
      TmRecLets {{t with bindings = newBinds}
                    with inexpr = inexpr})

  | t ->
    smapAccumL_Expr_Expr (buildDependencies cur env data) acc t

  -- Compute the dependency graph as if all holes are dependent on each other,
  -- without actually analyzing dependency. The whole AST becomes one single
  -- measuring point, which is dependent on all holes. Returns both the graph
  -- and the modified AST.
  sem assumeFullDependency (env : CallCtxEnv) =
  | t ->
    -- Put the entire AST in the body of a let-expression: the measuring point
    let m = nameSym "m" in
    let t = nulet_ m t in
    let t = bind_ t (nvar_ m) in

    -- Build the dependency graph
    let dep = _dependencyGraphEmpty in
    let nHoles = length env.idx2hole in
    -- Identifier of measuring point
    let mId = nHoles in
    let holeIds = create nHoles (lam i. i) in
    -- Build bipartite graph
    let vertices = cons mId holeIds in
    let edges = map (lam h. (h,mId,0)) holeIds in
    let graphGraph = graphAddEdges edges (
      graphAddVertices vertices dep.graph)
    in
    -- Create empty context tree (measuring point has no context)
    let tree = prefixTreeEmpty nameInfoCmp (nameSym "", NoInfo ()) in
    let tree = prefixTreeInsert nameInfoCmp tree mId [] in
    let measuringPoints = mapInsert m tree dep.measuringPoints in
    -- Closest enclosing call graph function is top-level
    let meas2fun = mapInsert m (nameInfoGetName callGraphTop) dep.meas2fun in
    let dep = {{{{{{dep with graph = graphGraph}
                        with measuringPoints = measuringPoints}
                        with meas2fun = meas2fun}
                        with offset = nHoles}
                        with nbrMeas = 1}
                        with alive = setOfSeq subi [nHoles]} in
    (dep, t)

end

lang TestLang = DependencyAnalysis + MExprHoleCFA + GraphColoring +
                NestedMeasuringPoints +
                BootParser + MExprPrettyPrint + MExprANFAll + MExprSym
end

mexpr
use TestLang in

let debug = false in
let parse = lam str.
  let ast = parseMExprStringKeywordsExn holeKeywords str in
  let ast = makeKeywords ast in
  symbolize ast
in

let test : Bool -> Bool -> Expr -> (DependencyGraph, CallCtxEnv) =
  lam debug: Bool. lam full: Bool. lam t: Expr.
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
      let cfaRes : CFAGraph = analyzeNested env cfaRes tANF in
      match
        if full then assumeFullDependency env tANF
        else (analyzeDependency env cfaRes tANF, tANF)
      with (dep, ast)
      in
      printLn "\n--- DEPENDENCY GRAPH ---";
      printLn (digraphToDot int2string int2string dep.graph);
      let dep : DependencyGraph = dep in
      (dep, env)

    else
      -- Version without debug printouts
      let cfaRes : CFAGraph = holeCfa graphData tANF in
      let cfaRes : CFAGraph = analyzeNested env cfaRes tANF in
      match
        if full then assumeFullDependency env tANF
        else (analyzeDependency env cfaRes tANF, tANF)
      with (dep, ast)
      in
      let dep : DependencyGraph = dep in
      (dep, env)
in

type TestResult = {
  measuringPoints : [(String,[[String]])],
  -- Edges in the bipartite graph
  deps : [((String,[String]), (String,[String]))],
  meas2fun : [(String,String)],
  offset : Int,
  nbrMeas : Int
} in

-- Helper for eqTest, to check that provided measuring contexts match.
let eqMeasContexts = lam tree : PTree NameInfo. lam contexts : [[String]].
  let ids = prefixTreeGetIds tree [] in
  let paths = foldl (lam acc. lam id.
    let path = prefixTreeGetPathExn tree id in
    cons path acc) [] ids
  in
  -- Paths are stored in reverse order in tree
  let paths : [[String]] = map (
      lam path : [NameInfo].
        reverse (
          map (lam e : NameInfo. nameInfoGetStr e) path)
    ) paths
  in
  let s1 : Set [String] = setOfSeq (seqCmp cmpString) paths in
  let s2 : Set [String] = setOfSeq (seqCmp cmpString) contexts in
  setEq s1 s2
in

-- Helper for eqTest, to check that a given dependency edge exists.
let depExists = lam holeTree : PTree NameInfo. lam measTree : PTree NameInfo.
                lam graph : Graph Int Int.
                lam edge : ([String], [String]).
  -- Convert name info paths to string paths
  let holeIdPath : [(Int,[NameInfo])] = prefixTreeBindings holeTree in
  let holePathId : [([String],Int)] = map (
    lam b : (Int,[NameInfo]). (map nameInfoGetStr b.1, b.0)
  ) holeIdPath in

  let measIdPath : [(Int,[NameInfo])] = prefixTreeBindings measTree in
  let measPathId : [([String],Int)] = map (
    lam b : (Int,[NameInfo]). (map nameInfoGetStr b.1, b.0)
  ) measIdPath in

  -- Reverse edge paths
  let from = reverse edge.0 in
  let to = reverse edge.1 in

  -- Translate string edges to integer id's
  let fromId : Int = assocLookupOrElse {eq=eqSeq eqString}
    (lam. error (concat "Hole path missing: " (strJoin " " from)))
    from holePathId
  in
  let toId : Int = assocLookupOrElse {eq=eqSeq eqString}
    (lam. error (concat "Measuring path missing: " (strJoin " " to)))
    to measPathId
  in

  -- Edge lookup ignoring label
  let edgeExists = lam from. lam to.
    graphIsAdjacent from to graph
  in

  -- Check whether the bipartite graph contains the edge.
  edgeExists fromId toId
in

-- Test equality function
let eqTest = lam lhs : (DependencyGraph, CallCtxEnv). lam rhs : TestResult.
  match lhs with (dep, env) in
  -- Convert from name info to string
  let measTreeBinds : [(Name,PTree NameInfo)] = mapBindings dep.measuringPoints in
  let measTrees : Map String (PTree NameInfo) = foldl (
    lam acc. lam b : (Name,PTree NameInfo).
      mapInsert (nameGetStr b.0) b.1 acc
    ) (mapEmpty cmpString) measTreeBinds
  in

  let holeTrees : Map String (PTree NameInfo) = mapFoldWithKey (
    lam acc. lam k : NameInfo. lam v : PTree NameInfo.
      mapInsert (nameInfoGetStr k) v acc
    ) (mapEmpty cmpString) env.contexts
  in

  -- Measuring contexts match
  let measCtxs = map (
    lam strCtxs.
      match strCtxs with (str, ctxs) in
      let tree = mapFindExn str measTrees in
      eqMeasContexts tree ctxs
    ) rhs.measuringPoints in
  let measCtxsMatch = forAll (lam x. x) measCtxs in

  -- Number of measuring contexts match
  let nbrCtxs1 = foldl (
    lam acc. lam ctx : (String,[[String]]). addi acc (length ctx.1)
    ) 0 rhs.measuringPoints in
  let nbrCtxs2 = mapFoldWithKey (
    lam acc. lam k : String. lam v : PTree NameInfo.
      addi acc (length (prefixTreeGetIds v []))
    ) 0 measTrees in
  let nbrCtxsMatch = eqi nbrCtxs1 nbrCtxs2 in

  -- Dependency edges exist
  let edgesExist = map (
    lam e : ((String,[String]),(String,[String])).
      match e with ((h,hPath),(m,mPath)) in
      depExists (mapFindExn h holeTrees) (mapFindExn m measTrees)
        dep.graph (hPath,mPath)
    ) rhs.deps
  in
  let edgesExist = forAll (lam x. x) edgesExist in

  -- Number of dependency edges match
  let nbrEdges1 = length rhs.deps in
  let nbrEdges2 = graphCountEdges dep.graph in
  let nbrEdgesMatch = eqi nbrEdges1 nbrEdges2 in

  -- meas2fun match
  let meas2funStr : [(String, String)] = map (
    lam nn : (Name, Name). (nameGetStr nn.0, nameGetStr nn.1)
    ) (mapBindings dep.meas2fun) in
  let mapLhs = mapFromSeq cmpString meas2funStr in
  let mapRhs = mapFromSeq cmpString rhs.meas2fun in
  let meas2funEq = mapEq eqString mapLhs mapRhs in

  -- Offset matches
  let offsetEq = eqi dep.offset rhs.offset in

  -- nbrMeas matches
  let nbrMeasEq = eqi dep.nbrMeas rhs.nbrMeas in

  let failPrint = lam.
    printLn "Measuring contexts";
    mapMapWithKey (lam k. lam v.
      printLn "-------";
      printLn k;
      let binds = prefixTreeBindings v in
      iter (lam b: (Int, [NameInfo]).
        printLn (strJoin " " [int2string b.0,
          strJoin " " (map nameInfoGetStr b.1)
          ])) binds;
      printLn "-------"
      ) measTrees;

   printLn "Hole contexts";
   mapMapWithKey (lam k. lam v.
     printLn "-------";
     printLn k;
     let binds = prefixTreeBindings v in
     iter (lam b: (Int, [NameInfo]).
       printLn (strJoin " " [int2string b.0,
         strJoin " " (map nameInfoGetStr b.1)
         ])) binds;
     printLn "-------"
   ) holeTrees;

   printLn "Dependency graph";
   printLn (digraphToDot int2string int2string dep.graph);

   printLn "meas2fun";
   mapMapWithKey (lam k. lam v.
     printLn (join [nameGetStr k, " ", nameGetStr v])
   ) dep.meas2fun;

   printLn "offset";
   printLn (int2string dep.offset);

   printLn "nbrMeas";
   printLn (int2string dep.nbrMeas)
  in


  let result : [(Bool, String)] =
  [ (measCtxsMatch, "\nFAIL: Measuring context mismatch")
  , (nbrCtxsMatch, "\nFAIL: Number of measuring context mismatch")
  , (edgesExist, "\nFAIL: Some edge does not exist")
  , (nbrEdgesMatch, "\nFAIL: Number of edges mismatch")
  , (meas2funEq, "\nFAIL: Mismatch in meas2fun")
  , (offsetEq, "\nFAIL: Mismatch in offset")
  , (nbrMeasEq, "\nFAIL: Mismatch in nbrMeas")
  ] in

  iter (lam b: (Bool, String).
    if b.0 then ()
    else printLn b.1; failPrint ()
  ) result;

  forAll (lam b : (Bool, String). b.0) result
in

let t = parse
"
let foo = lam x.
  let h = hole (Boolean {default = true}) in
  let a = sleepMs h in
  let b = sleepMs h in
  (a,b)
in
let bar = lam x. lam y.
  let h1 = hole (Boolean {default = true}) in
  let c = if h1 then 1 else 2 in
  c
in
foo ()
" in

utest test debug false t with {
  measuringPoints = [ ("a",[[]]), ("b",[[]]), ("c",[[]])],
  deps =
  [ ( ("h", []), ("a", []) )
  , ( ("h", []), ("b", []) )
  , ( ("h1", []), ("c", []) )
  ],
  meas2fun = [("a","top"), ("b","top"), ("c","top")],
  offset = 2,
  nbrMeas = 3
} using eqTest in

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
  let cc = sleepMs c in
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

utest test debug false t with {
  measuringPoints =
  [ ("g", [[]])
  , ("cc", [["d"],["e"]])
  ],
  deps =
  [ ( ("h", ["d","a"]), ("g", []) )
  , ( ("h", ["d","b"]), ("g", []) )
  , ( ("h", ["e","a"]), ("g", []) )
  , ( ("h", ["e","b"]), ("g", []) )

  , ( ("h", ["d","a"]), ("cc", ["d"]) )
  , ( ("h", ["d","b"]), ("cc", ["d"]) )
  , ( ("h", ["e","a"]), ("cc", ["e"]) )
  , ( ("h", ["e","b"]), ("cc", ["e"]) )
  ],
  meas2fun = [("g","top"), ("cc","f2")],
  offset = 4,
  nbrMeas = 3
} using eqTest in

let t = parse
"
let f1 = lam x.
  let h = hole (Boolean {default = true, depth = 3}) in
  let m = sleepMs h in
  m
in
let f2 = lam x.
  let a = f1 x in
  a
in
let f3 = lam x. lam y.
  let c = f2 x in
  c
in
let f4 = lam x.
  let d = f3 x 2 in
  d
in
f4 ()
" in

utest test debug false t with {
  measuringPoints = [ ("m", [["d","c","a"]]) ],
  deps = [ (("h", ["d","c","a"]), ("m", ["d","c","a"])) ],
  meas2fun = [("m","f1")],
  offset = 1,
  nbrMeas = 1
} using eqTest in

-- Recursive lets
let t = parse
"
let f1 = lam x.
  let h = hole (Boolean {default = true, depth = 2}) in
  h
in
recursive let f2 = lam x. lam y.
  let a = f1 x in
  let b = sleepMs a in
  b
in
let c = f2 1 2 in
c
" in

utest test debug false t with {
  measuringPoints = [ ("b", [["c"]]) ],
  deps = [ (("h", ["c","a"]), ("b", ["c"])) ],
  meas2fun = [("b","f2")],
  offset = 1,
  nbrMeas = 1
} using eqTest in

-- Tests with full dependency
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
  let cc = sleepMs c in
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

utest test debug true t with {
  measuringPoints =
  [ ("m", [[]]) ],
  deps =
  [ ( ("h", ["d","a"]), ("m", []) )
  , ( ("h", ["d","b"]), ("m", []) )
  , ( ("h", ["e","a"]), ("m", []) )
  , ( ("h", ["e","b"]), ("m", []) )
  ],
  meas2fun = [("m","top")],
  offset = 4,
  nbrMeas = 1
} using eqTest in


let t = parse
"
let f1 = lam x.
  let h1 = hole (IntRange{min=100,max=200,default=200}) in
  let m1 = sleepMs h1 in
  ()
in
recursive let f2 = lam x.
  let c = f1 x in c
in
recursive let f3 = lam x.
  ()
in
let h2 = hole (IntRange{min=100,max=200,default=200}) in
let m2 = if h2 then let a = f2 () in a else () in
let m3 = if h2 then () else let b = f1 () in b in
let m4 = if h2 then f3 () else () in
()
"
in

utest test debug false t with {
  measuringPoints =
  [ ("m1", [[]])
  , ("m2", [[]])
  , ("m3", [[]])
  , ("m4", [[]])
  ],
  deps =
  [ ( ("h1", []), ("m1", []) )
  , ( ("h1", []), ("m2", []) )
  , ( ("h1", []), ("m3", []) )
  , ( ("h2", []), ("m2", []) )
  , ( ("h2", []), ("m3", []) )
  , ( ("h2", []), ("m4", []) )
  ],
  meas2fun = [("m1","top"),("m2","top"),("m3","top"),("m4","top")],
  offset = 2,
  nbrMeas = 4
} using eqTest in


-- Syntactically scoped points
let t = parse
"
let h1 = hole (Boolean {default = true}) in
let h2 = hole (IntRange {default = 1, min = 0, max = 10}) in
let m1 =
  if h1 then
    let a = sleepMs h2 in
    ()
  else ()
in
()
"
in

utest test debug false t with {
  measuringPoints =
  [ ("m1", [[]])
  ],
  deps =
  [ ( ("h1", []), ("m1", []) )
  , ( ("h2", []), ("m1", []) )
  ],
  meas2fun = [("m1","top")],
  offset = 2,
  nbrMeas = 1
} using eqTest in


-- Nested measuring points with several contexts
let t = parse
"
let f = lam x.
  let h = hole (Boolean {default = true, depth = 1}) in
  let m1 = if h then 1 else 2 in
  h
in

let g = lam x.
  let v1 = f () in
  let m =
    if v1 then
      let v2 = f () in
      v2
    else false
  in m
in

let v3 = f () in

g ()
"
in

utest test debug false t with {
  measuringPoints =
  [ ("m", [[]])
  , ("m1", [["v1"],["v2"],["v3"]])
  ],
  deps =
  [ ( ("h", ["v1"]), ("m", []) )
  , ( ("h", ["v2"]), ("m", []) )
  , ( ("h", ["v1"]), ("m1", ["v1"]) )
  , ( ("h", ["v2"]), ("m1", ["v2"]) )
  , ( ("h", ["v3"]), ("m1", ["v3"]) )
  ],
  meas2fun = [("m","g"),("m1","f")],
  offset = 3,
  nbrMeas = 4
}
using eqTest in


()
