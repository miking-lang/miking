
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
  measuringContexts : Map Name (PTree Name)
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
    let graph = {
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
        -- dprintLn ident;
        -- dprintLn (mapBindings shortContexts);

        -- Build a prefix tree with measuring contexts
        --let tree : PTree NameInfo = mapFoldWithKey (lam treeId. lam. lam path.
        match mapFoldWithKey (lam treeId. lam. lam path.
            match treeId with (tree,id) in
            switch prefixTreeMaybeInsert nameInfoCmp tree id path
            case (true,tree) then (tree, addi id 1)
            case (false,_) then (tree, id)
            end
          )
          (prefixTreeEmpty nameInfoCmp (nameSym "", NoInfo ()), measCount) shortContexts
        with (tree, measCount) in

        -- For each context-sensitive hole, add an edge to the set of measuring
        -- id's it affects
        let graphGraph = mapFoldWithKey (
          lam acc: Digraph Int Int. lam id: Int. lam path: [NameInfo].
            -- Set of measuring points that this context string affects.
            let measPoints : [Int] = prefixTreeGetIds tree path in
            -- Add context-expanded hole to dependency graph
            let acc = digraphMaybeAddVertex id acc in
            -- Add corresponding edges to dependency graph
            foldl (lam acc : Digraph Int Int. lam mp: Int.
              let acc = digraphMaybeAddVertex mp acc in
              digraphAddEdge id mp 0 acc
            ) acc measPoints
          ) graph.graph shortContexts
        in

        -- Insert the prefix tree and return final result
        let measuringContexts = mapInsert ident tree graph.measuringContexts in
        ( { { graph with measuringContexts = measuringContexts }
                    with graph = graphGraph },
          measCount )

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

let debug = true in
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
      dprintLn dep;
      printLn "\n--- DEPENDENCY GRAPH ---";
      digraphPrintDot dep.graph int2string int2string;
      ()

    else
      -- Version without debug printouts
      let cfaRes : CFAGraph = cfaData graphData tANF in
      let dep : DependencyGraph = analyzeDependency env cfaRes tANF in
      ()
in

-- Print out bipartite graph in dot format
-- Maybe provide bipartite graph as context strings
-- Provide names of holes and measuring points
-- Provide measuring contexts for each measuring name

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

utest test debug t with () in

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

utest test true t with () in

()
