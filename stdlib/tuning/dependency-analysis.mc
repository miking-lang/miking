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
  { graph = digraphEmpty subi eqi
  , holes = setEmpty nameCmp
  , measuringPoints = setEmpty nameCmp
  }

lang DependencyAnalysis = MExprHoleCFA
  sem analyzeDependency (env : CallCtxEnv) (cfaGraph : CFAGraph) =
  | t ->
    --let cfaRes = cfaData (graphDataFromEnv env) t in
    buildDependencies callGraphTop env cfaGraph.data _dependencyGraphEmpty t

  sem buildDependencies (cur : NameInfo) (env : CallCtxEnv)
                        (data : Map Name (Set AbsVal))
                        (graph : DependencyGraph) =
  | TmLet ({ident = ident} & t) ->
    -- Only keep the part of the path that happened before the current node in
    -- the call graph
    recursive let shortenPath = lam path.
      match path with [] then []
      else match path with [(from,to,lbl)] ++ path in
        if nameInfoEq cur from then []
        else cons (from,to,lbl) (shortenPath path)
    in

    -- Update 'cur' when recursing in body if defining a function that is part
    -- of the call graph.
    let curBody =
      match t.body with TmLam lm then
        if digraphHasVertex (ident, NoInfo ()) env.callGraph then (ident, t.info)
        else cur
      else cur
    in

    -- Update dependency graph from dependencies
    let graph =
      match mapLookup ident data with Some deps then
        let shortContexts : Map Int [NameInfo] =
          setFold (lam acc. lam av.
            match av with AVEHole {id = id, contexts = contexts} then
              setFold (lam acc. lam c.
                utest mapMem c acc with false in
                let shortPath : Path = shortenPath (mapFindExn c env.verbosePath) in
                let lblPath : [NameInfo] = map (lam e : Edge. e.2) shortPath in
                mapInsert c lblPath acc
              ) acc contexts
            else acc
          ) (mapEmpty subi) deps
        in
        dprintLn ident;
        dprintLn (mapBindings shortContexts);

        let tree : PTree NameInfo = 

        graph
      else graph
    in

    match buildDependencies curBody env data graph t.body with (graph, body) in
    match buildDependencies cur env data graph t.inexpr with (graph, inexpr) in
    (graph, TmLet {{t with body = body} with inexpr = inexpr})

  | t ->
    smapAccumL_Expr_Expr (buildDependencies cur env data) graph t
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
      analyzeDependency env cfaRes tANF;
      ()

    else
      -- Version without debug printouts
      let cfaRes : CFAGraph = cfaData graphData tANF in
      analyzeDependency env cfaRes tANF;
      ()
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
