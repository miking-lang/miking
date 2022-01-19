
-- Run CFA, give back as result:
-- Bipartite graph

include "hole-cfa.mc"
include "prefix-tree.mc"

include "digraph.mc"
include "set.mc"
include "name.mc"

type DependencyGraph = {
  -- A bipartite graph from context-expanded holes to measuring points (labels
  -- unused)
  graph : Digraph Int Int,

  -- The set of base holes in the graph
  holes : Set Name,

  -- The set of base measuring points in the graph
  measuringPoints : Set Name,

  -- Maps a context-sensitive measuring point to its prefix tree, which gives a
  -- compact representation of the context strings
  measuringContexts : Map Name (PTree NameInfo)
}

let _dependencyGraphEmpty =
  { graph = digraphEmpty subi (lam. lam. false) -- disable graph labels
  , holes = setEmpty nameCmp
  , measuringPoints = setEmpty nameCmp
  , measuringContexts = mapEmpty nameCmp
  }

lang DependencyAnalysis = MExprHoleCFA
  sem analyzeDependency (env : CallCtxEnv) (cfaGraph : CFAGraph) =
  | t ->
    -- Start the indexing of measuring points from the number of
    -- context-sensitive holes, to guarantee no collision in indices (to be able
    -- to store both sets as vertices in a graph).
    let nHoles = mapSize env.contexts in
    match
      buildDependencies callGraphTop env cfaGraph.data
        (_dependencyGraphEmpty, nHoles) t
    with ((graph, _), _) in
    graph

  sem buildDependencies (cur : NameInfo) (env : CallCtxEnv)
                        (data : Map Name (Set AbsVal))
                        (acc : (DependencyGraph, Int)) =
  | TmLet ({ident = ident} & t) ->
    match acc with (graph, measCount) in
    -- Add base measuring point to dependency graph
    let graph : DependencyGraph = {
      graph with measuringPoints = setInsert ident graph.measuringPoints
    } in

    -- Function to keep the part of a path that happened before the current node
    -- in the call history
    recursive let shortenPath = lam path.
      match path with [] then []
      else match path with [(from,to,lbl)] ++ path in
        if nameInfoEq cur from then []
        else cons (from,to,lbl) (shortenPath path)
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
                let shortPath : Path = shortenPath (mapFindExn c env.verbosePath) in
                let lblPath : [NameInfo] = map (lam e : Edge. e.2) shortPath in

                -- Insert base hole in the graph, and accumulate context
                ( { graph with holes = setInsert id graph.holes },
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
            lam acc: Digraph Int Int. lam id: Int. lam path: [NameInfo].
              -- Set of measuring points that this context string affects.
              let measPoints : [Int] = prefixTreeGetIds tree (reverse path) in
              -- Add context-expanded hole to dependency graph
              let acc = digraphMaybeAddVertex id acc in
              -- Add corresponding edges to dependency graph
              foldl (lam acc : Digraph Int Int. lam mp: Int.
                let acc = digraphMaybeAddVertex mp acc in
                digraphAddEdge id mp 0 acc
              ) acc measPoints
            ) graph.graph shortContexts
          in
          let measContexts = mapInsert ident tree graph.measuringContexts in
          ( { { graph with measuringContexts = measContexts }
                      with graph = graphGraph },
            newMeasCount )

      else (graph, measCount)
    in

    -- Update 'cur' when recursing in body if defining a function that is part
    -- of the call graph.
    let curBody =
      match t.body with TmLam lm then
        if digraphHasVertex (ident, NoInfo ()) env.callGraph then (ident, t.info)
        else cur
      else cur
    in
    match buildDependencies curBody env data acc t.body with (acc, body) in
    match buildDependencies cur env data acc t.inexpr with (acc, inexpr) in
    (acc, TmLet {{t with body = body} with inexpr = inexpr})

  -- TODO: recursive lets

  | t ->
    smapAccumL_Expr_Expr (buildDependencies cur env data) acc t
end

lang TestLang = DependencyAnalysis + MExprHoleCFA + GraphColoring + BootParser +
                MExprPrettyPrint + MExprANFAll + MExprSym

mexpr
use TestLang in

let debug = false in
let parse = lam str.
  let ast = parseMExprString holeKeywords str in
  let ast = makeKeywords [] ast in
  symbolize ast
in

let test = lam debug: Bool. lam t: Expr.
    -- Use small ANF first, needed for context expansion
    let tANFSmall = use MExprHoles in normalizeTerm t in

    -- Do graph coloring to get context information (throw away the AST).
    match colorCallGraph [] tANFSmall with (env, _) in

    -- Initialize the graph data
    let graphData = graphDataFromEnv env in

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
      match cfaDebug (Some graphData) (Some pprintEnv) tANF with (Some pprintEnv,cfaRes) in
      match cfaGraphToString pprintEnv cfaRes with (_, resStr) in
      printLn "\n--- FINAL CFA GRAPH ---";
      printLn resStr;
      let cfaRes : CFAGraph = cfaRes in
      let dep : DependencyGraph = analyzeDependency env cfaRes tANF in
      printLn "\n--- DEPENDENCY GRAPH ---";
      digraphPrintDot dep.graph int2string int2string;
      (dep, env)

    else
      -- Version without debug printouts
      let cfaRes : CFAGraph = cfaData graphData tANF in
      let dep : DependencyGraph = analyzeDependency env cfaRes tANF in
      (dep, env)
in

type TestResult = {
  measuringPoints : [(String,[[String]])],
  -- Edges in the bipartite graph
  deps : [((String,[String]), (String,[String]))]
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
                lam graph : Digraph Int Int.
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

  -- printLn "holePathId";
  -- dprintLn holePathId;
  -- printLn "measPathId";
  -- dprintLn measPathId;

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
    not (null (digraphEdgesBetween from to graph))
  in

  -- Check whether the bipartite graph contains the edge.
  edgeExists fromId toId
in

-- Test equality function
let eqTest = lam lhs : (DependencyGraph, CallCtxEnv). lam rhs : TestResult.
  match lhs with (dep, env) in
  -- Convert from name info to string
  let measTreeBinds : [(Name,PTree NameInfo)] = mapBindings dep.measuringContexts in
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
  let nbrEdges2 = digraphCountEdges dep.graph in
  let nbrEdgesMatch = eqi nbrEdges1 nbrEdges2 in

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
     --prefixTreeDebug nameInfoGetStr v;
     let binds = prefixTreeBindings v in
     iter (lam b: (Int, [NameInfo]).
       printLn (strJoin " " [int2string b.0,
         strJoin " " (map nameInfoGetStr b.1)
         ])) binds;
     printLn "-------"
   ) holeTrees;

   printLn "Dependency graph";
   digraphPrintDot dep.graph int2string int2string
  in


  let result : [(Bool, String)] =
  [ (measCtxsMatch, "\nFAIL: Measuring context mismatch")
  , (nbrCtxsMatch, "\nFAIL: Number of measuring context mismatch")
  , (edgesExist, "\nFAIL: Some edge does not exist")
  , (nbrEdgesMatch, "\nFAIL: Number of edges mismatch")
  ] in

  iter (lam b: (Bool, String, Unit -> Unit).
    if b.0 then ()
    else printLn b.1; failPrint ()
  ) result;

  forAll (lam b : (Bool, String, Unit -> Unit). b.0) result
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

utest test debug t with {
  measuringPoints = [ ("a",[[]]), ("b",[[]]), ("c",[[]])],
  deps =
  [ ( ("h", []), ("a", []) )
  , ( ("h", []), ("b", []) )
  , ( ("h1", []), ("c", []) )
  ]
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

utest test debug t with {
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
  ]
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
let f3 = lam x.
  let c = f2 x in
  c
in
let f4 = lam x.
  let d = f3 x in
  d
in
f4 ()
" in

utest test debug t with {
  measuringPoints = [ ("m", [["d","c","a"]]) ],
  deps = [ (("h", ["d","c","a"]), ("m", ["d","c","a"])) ]
} using eqTest in

()
