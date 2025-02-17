-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Prints data about a program with holes.

include "csv.mc"
include "string.mc"

include "dependency-analysis.mc"
include "search-space.mc"
include "tune-options.mc"

lang MeasPointCSV = CSV
  syn CSVRow =
  | MeasPoint {id: Int,
               ident: String,
               context: [String],
               deps: [Int],
               searchSpace: Float,
               cc: Int}

  sem csvHeader =
  | MeasPoint _ ->
    ["id-meas", "ident", "context", "deps", "searchSpace", "connectedComponent"]

  sem csvRow2string =
  | MeasPoint m ->
    [ int2string m.id
    , m.ident
    , strJoin "|" m.context
    , strJoin "|" (map int2string m.deps)
    , float2string m.searchSpace
    , int2string m.cc
    ]
end

lang HoleCSV = CSV
  syn CSVRow =
  | Hole {id: Int,
          ident: String,
          context: [String],
          deps: [Int],
          domainSize: Int,
          cc: Int}

  sem csvHeader =
  | Hole _ ->
    ["id-hole", "ident", "context", "deps", "domainSize", "connectedComponent"]

  sem csvRow2string =
  | Hole h ->
    [ int2string h.id
    , h.ident
    , strJoin "|" h.context
    , strJoin "|" (map int2string h.deps)
    , int2string h.domainSize
    , int2string h.cc
    ]
end

lang ConnectedComponentCSV = CSV
  syn CSVRow =
  | CC {id: Int,
        deps: [Int],
        size: Float}

  sem csvHeader =
  | CC _ ->
    ["id-cc", "deps", "size"]

  sem csvRow2string =
  | CC c ->
    [ int2string c.id
    , strJoin "|" (map int2string c.deps)
    , float2string c.size
    ]
end

lang SizeCSV = CSV
  syn CSVRow =
  | Size {total: Float, reduced: Float}

  sem csvHeader =
  | Size _ ->
    ["total", "reduced"]

  sem csvRow2string =
  | Size s ->
    [ float2string s.total
    , float2string s.reduced
    ]
end

lang RunCSV = CSV
  syn CSVRow =
  | Run {id: Int, nbrRuns: Int, time: Float}

  sem csvHeader =
  | Run _ ->
    ["id-meas", "nbrRuns", "time"]

  sem csvRow2string =
  | Run r ->
    [ int2string r.id
    , int2string r.nbrRuns
    , float2string r.time
    ]
end

lang TuneStats = DependencyAnalysis

  sem tuneStatsMeasPoints
  : DependencyGraph -> SearchSpaceSize -> PprintEnv -> String
  sem tuneStatsMeasPoints graph searchSpace =
  | env ->
    use MeasPointCSV in
    let idNameContext: [(Int,Name,[Name])] =
      mapFoldWithKey (lam acc. lam name: Name. lam tree: PTree NameInfo.
        let binds: [(Int,[NameInfo])] = prefixTreeBindings tree in
        let res = foldl (lam acc. lam b: (Int,[NameInfo]).
            if setMem b.0 graph.alive then
              cons (b.0, name, map nameInfoGetName b.1) acc
            else acc
          ) [] binds
        in
        concat acc res
      ) [] graph.measuringPoints
    in
    let idStrContext: [(Int,String,[String])] = map (lam t: (Int,Name,[Name]).
        match t with (id, name, context) in
        let getStr = lam n.
          optionGetOrElse (lam. error (concat "unknown name: " (nameGetStr n)))
            (pprintEnvLookup n env)
        in
        let str = getStr name in
        let context = map getStr context in
        (id, str, context)
      ) idNameContext
    in
    let ids = map (lam t: (Int,String,[String]). t.0) idStrContext in
    let idents = map (lam t: (Int,String,[String]). t.1) idStrContext in
    let contexts = map (lam t: (Int,String,[String]). t.2) idStrContext in
    let deps = map (lam id. graphNeighbors id graph.graph) ids in
    let sizes = map (lam id. mapFindExn id searchSpace.measuringPoints) ids in
    let ccs =
      let findCC = lam id.
        match
          foldl (lam acc. lam c: ([Int],Float).
              match acc with (Some _, _) then acc
              else
                match acc with (_, i) in
                match find (eqi id) c.0 with Some _ then (Some i, i)
                else (None (), addi i 1)
            ) (None (), 0) searchSpace.connectedComponents
        with (Some i, _) then i
        else error "impossible"
      in
      map findCC ids
    in
    recursive let mkRow =
      lam acc. lam ids. lam idents. lam contexts. lam deps. lam sizes. lam ccs.
      match ids with [] then acc
      else
        let acc = cons (MeasPoint {id = head ids,
                                   ident = head idents,
                                   context = head contexts,
                                   deps = head deps,
                                   searchSpace = head sizes,
                                   cc = head ccs}) acc in
        mkRow acc (tail ids) (tail idents) (tail contexts) (tail deps)
              (tail sizes) (tail ccs)
    in
    let rows = mkRow [] ids idents contexts deps sizes ccs in
    -- Sort the rows according to id
    let rows = sort (lam h1: CSVRow. lam h2: CSVRow.
        match (h1, h2) with (MeasPoint {id = id1}, MeasPoint {id = id2}) in
        subi id1 id2
      ) rows
    in
    csvWrite "," rows

  sem tuneStatsHoles
  : DependencyGraph -> SearchSpaceSize -> TuneOptions -> CallCtxEnv -> PprintEnv
  -> String
  sem tuneStatsHoles graph searchSpace options callCtx =
  | env ->
    use HoleCSV in
    let idNameContext: [(Int,Name,[Name])] =
      mapFoldWithKey (lam acc. lam name: NameInfo. lam tree: PTree NameInfo.
        let binds: [(Int,[NameInfo])] = prefixTreeBindings tree in
        concat acc
        (map (lam b: (Int,[NameInfo]).
            (b.0, nameInfoGetName name, map nameInfoGetName b.1)
          ) binds)
      ) [] callCtx.contexts
    in
    utest length idNameContext with length callCtx.idx2hole in
    let idStrContext: [(Int,String,[String])] = map (lam t: (Int,Name,[Name]).
        match t with (id, name, context) in
        let getStr = lam n.
          optionGetOrElse (lam. error (concat "unknown name: " (nameGetStr n)))
            (pprintEnvLookup n env)
        in
        let str = getStr name in
        let context = map getStr context in
        (id, str, context)
      ) idNameContext
    in
    let ids = map (lam t: (Int,String,[String]). t.0) idStrContext in
    let idents = map (lam t: (Int,String,[String]). t.1) idStrContext in
    let contexts = map (lam t: (Int,String,[String]). t.2) idStrContext in
    let deps = map (lam id.
        if graphHasVertex id graph.graph then
          graphNeighbors id graph.graph
        else []
      ) ids
    in
    let sizes = map (lam id.
        domainSize options.stepSize (get callCtx.idx2hole id)
      ) ids
    in
    let ccs =
      let findCC = lam id.
        match
          foldl (lam acc. lam c: ([Int],Float).
              match acc with (Some _, _) then acc
              else
                match acc with (_, i) in
                match find (eqi id) c.0 with Some _ then (Some i, i)
                else (None (), addi i 1)
            ) (None (), 0) searchSpace.connectedComponents
        with (Some i, _) then i
        else negi 1
      in
      map findCC ids
    in
    recursive let mkRow =
      lam acc. lam ids. lam idents. lam contexts. lam deps. lam sizes. lam ccs.
      match ids with [] then acc
      else
        let acc = cons (Hole {id = head ids,
                              ident = head idents,
                              context = head contexts,
                              deps = head deps,
                              domainSize = head sizes,
                              cc = head ccs}) acc in
        mkRow acc (tail ids) (tail idents) (tail contexts) (tail deps)
              (tail sizes) (tail ccs)
    in
    let rows = mkRow [] ids idents contexts deps sizes ccs in
    -- Sort the rows according to id
    let rows = sort (lam h1: CSVRow. lam h2: CSVRow.
        match (h1, h2) with (Hole {id = id1}, Hole {id = id2}) in
        subi id1 id2
      ) rows
    in
    csvWrite "," rows

  sem tuneStatsCC : SearchSpaceSize -> String
  sem tuneStatsCC =
  | ss ->
    use ConnectedComponentCSV in
    let idIdsSize: [(Int,[Int],Float)] = mapi (lam i: Int. lam t:([Int],Float).
        match t with (ids, size) in
        (i,ids,size)
      ) ss.connectedComponents
    in
    let rows = map (lam t: (Int,[Int],Float).
        CC {id=t.0, deps=t.1, size=t.2}
      ) idIdsSize
    in
    csvWrite "," rows

  sem tuneStatsSize : SearchSpaceSize -> String
  sem tuneStatsSize =
  | ss ->
    use SizeCSV in
    let rows = [Size {total = ss.sizeTotal, reduced = ss.sizeReduced}] in
    csvWrite "," rows

  sem tuneStats
  : TuneOptions -> DependencyGraph -> SearchSpaceSize -> CallCtxEnv -> Expr
  -> String
  sem tuneStats options graph searchSpace env =
  | ast ->
    -- Populate the pretty print environment
    match pprintCode 0 pprintEnvEmpty ast with (pprintEnv, _) in
    let measPoints: String = tuneStatsMeasPoints graph searchSpace pprintEnv in
    let holes: String = tuneStatsHoles graph searchSpace options env pprintEnv in
    let ccs: String = tuneStatsCC searchSpace in
    let size: String = tuneStatsSize searchSpace in
    strJoin "\n" [measPoints, holes, ccs, size]

  sem tuneStatsTime: [(Int,Int,Float)] -> String
  sem tuneStatsTime =
  | res ->
    use RunCSV in
    let rows = map (lam t: (Int,Int,Float).
        Run {id= t.0, nbrRuns= t.1, time= t.2}
      ) res
    in
    csvWrite "," rows

end

lang TestLang = TuneStats + GraphColoring + NestedMeasuringPoints + SearchSpace
              + MExprSym + BootParser
end

mexpr

use TestLang in

let debug = true in

let parse = lam str.
  let ast = parseMExprStringKeywordsExn holeKeywords str in
  let ast = makeKeywords ast in
  symbolize ast
in

let test
  : Bool -> Expr -> String =
  lam debug. lam expr.
    -- Use small ANF first, needed for context expansion
    let tANFSmall = use HoleANF in normalizeTerm expr in

    -- Do graph coloring to get context information (throw away the AST).
    match colorCallGraph [] tANFSmall with (env, _) in

    -- Apply full ANF
    let tANF = use HoleANFAll in normalizeTerm tANFSmall in

    -- Perform dependency analysis
    match
      let graphData = graphDataInit env in
      let cfaRes : CFAGraph = holeCfa graphData tANF in
      let cfaRes : CFAGraph = analyzeNested env cfaRes tANF in
      (analyzeDependency env cfaRes tANF, tANF)
    with (dep, ast) in

    -- Compute search space
    let searchSpace = searchSpaceSize tuneOptionsDefault.stepSize env dep in

    tuneStats tuneOptionsDefault dep searchSpace env ast
in

let t = parse
"
let h = hole (Boolean {default = true}) in
let m = if h then true else false in
()
" in

utest test debug t with
"id-meas,ident,context,deps,searchSpace,connectedComponent
1,m,,0,2.,0

id-hole,ident,context,deps,domainSize,connectedComponent
0,h,,1,2,0

id-cc,deps,size
0,0|1,2.

total,reduced
2.,2.
"
in

-- Context-sensitivity
let t = parse
"
let f = lam.
  let hh = hole (Boolean {default = true, depth = 1}) in
  hh
in
let g = lam h.
  let m = if h then true else false in
  ()
in
let h1 = f () in
let h2 = f () in
let g1 = g h1 in
let g2 = g h2 in
()
" in

utest test debug t with
"id-meas,ident,context,deps,searchSpace,connectedComponent
2,m,,0|1,4.,0

id-hole,ident,context,deps,domainSize,connectedComponent
0,hh,h1,2,2,0
1,hh,h2,2,2,0

id-cc,deps,size
0,0|1|2,4.

total,reduced
4.,4.
"
in

-- Different connected components
let t = parse
"
let h1 = hole (IntRange {default = 0, min = 0, max = 1}) in
let m1 = sleepMs h1 in
let h2 = hole (IntRange {default = 0, min = 0, max = 1}) in
let m2 = sleepMs h2 in
()
" in

utest test debug t with
"id-meas,ident,context,deps,searchSpace,connectedComponent
2,m1,,0,2.,1
3,m2,,1,2.,0

id-hole,ident,context,deps,domainSize,connectedComponent
0,h1,,2,2,1
1,h2,,3,2,0

id-cc,deps,size
0,1|3,2.
1,0|2,2.

total,reduced
4.,2.
"
in

-- Context-sensitivity
let t = parse
"
let f = lam.
  let hh = hole (Boolean {default = true, depth = 1}) in
  hh
in
let g = lam h.
  let dummy = hole (Boolean {default = true, depth =1}) in
  let m = if h then true else false in
  ()
in
let e = lam.
  let h1 = f () in
  let h2 = f () in
  let g1 = g h1 in
  let g2 = g h2 in
  ()
in
e ()
" in

utest test debug t with
"id-meas,ident,context,deps,searchSpace,connectedComponent
4,m,,0|1,4.,0

id-hole,ident,context,deps,domainSize,connectedComponent
0,hh,h1,4,2,0
1,hh,h2,4,2,0
2,dummy,g1,,2,-1
3,dummy,g2,,2,-1

id-cc,deps,size
0,0|1|4,4.

total,reduced
16.,4.
"
in

utest tuneStatsTime [(1,2,3.),(4,5,6.)] with
"id-meas,nbrRuns,time
1,2,3.
4,5,6.
"
in

()
