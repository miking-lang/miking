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
               searchSpace: Float}

  sem csvHeader =
  | MeasPoint _ ->
    ["id", "ident", "context", "deps", "searchSpace"]

  sem csvRow2string =
  | MeasPoint m ->
    [ int2string m.id
    , m.ident
    , strJoin "|" m.context
    , strJoin "|" (map int2string m.deps)
    , float2string m.searchSpace
    ]

  sem csvString2Row =
  | row ->
    MeasPoint
    { id = string2int (get row 0)
    , ident = get row 1
    , context = strSplit "|" row 2
    , deps = map string2int (strSplit "|" (get row 3))
    , searchSpace = string2float (get row 4)
    }
end

lang HoleCSV = CSV
  syn CSVRow =
  | Hole {id: Int,
          ident: String,
          context: [String],
          deps: [Int],
          domainSize: Int}

  sem csvHeader =
  | Hole _ ->
    ["id", "ident", "context", "deps", "domainSize"]

  sem csvRow2string =
  | Hole h ->
    [ int2string h.id
    , h.ident
    , strJoin "|" h.context
    , strJoin "|" (map int2string h.deps)
    , int2string h.domainSize
    ]

  sem csvString2Row =
  | row ->
    Hole
    { id = string2int (get row 0)
    , ident = get row 1
    , context = strSplit "|" row 2
    , deps = map string2int (strSplit "|" (get row 3))
    , domainSize = string2int (get row 4)
    }
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
        concat acc
        (map (lam b: (Int,[NameInfo]).
            (b.0, name, map nameInfoGetName b.1)
          ) binds)
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
    recursive let mkRow =
      lam acc. lam ids. lam idents. lam contexts. lam deps. lam sizes.
      match ids with [] then acc
      else
        let acc = cons (MeasPoint {id = head ids,
                                   ident = head idents,
                                   context = head contexts,
                                   deps = head deps,
                                   searchSpace = head sizes}) acc in
        mkRow acc (tail ids) (tail idents) (tail contexts) (tail deps) (tail sizes)
    in
    let rows = mkRow [] ids idents contexts deps sizes in
    -- Sort the rows according to id
    let rows = sort (lam h1: CSVRow. lam h2: CSVRow.
        match (h1, h2) with (MeasPoint {id = id1}, MeasPoint {id = id2}) in
        subi id1 id2
      ) rows
    in
    csvWrite "," rows

  sem tuneStatsHoles
  : DependencyGraph -> TuneOptions -> CallCtxEnv -> PprintEnv -> String
  sem tuneStatsHoles graph options callCtx =
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
    recursive let mkRow =
      lam acc. lam ids. lam idents. lam contexts. lam deps. lam sizes.
      match ids with [] then acc
      else
        let acc = cons (Hole {id = head ids,
                              ident = head idents,
                              context = head contexts,
                              deps = head deps,
                              domainSize = head sizes}) acc in
        mkRow acc (tail ids) (tail idents) (tail contexts) (tail deps) (tail sizes)
    in
    let rows = mkRow [] ids idents contexts deps sizes in
    -- Sort the rows according to id
    let rows = sort (lam h1: CSVRow. lam h2: CSVRow.
        match (h1, h2) with (Hole {id = id1}, Hole {id = id2}) in
        subi id1 id2
      ) rows
    in
    csvWrite "," rows

  sem tuneStats
  : TuneOptions -> DependencyGraph -> SearchSpaceSize -> CallCtxEnv -> Expr
  -> String
  sem tuneStats options graph searchSpace env =
  | ast ->
    -- Populate the pretty print environment
    match pprintCode 0 pprintEnvEmpty ast with (pprintEnv, _) in
    let measPoints: String = tuneStatsMeasPoints graph searchSpace pprintEnv in
    let holes: String = tuneStatsHoles graph options env pprintEnv in
    join [measPoints, "\n", holes]

end

lang TestLang = TuneStats + GraphColoring + NestedMeasuringPoints + SearchSpace
              + MExprSym + BootParser
end

mexpr

use TestLang in

let debug = true in

let parse = lam str.
  let ast = parseMExprString holeKeywords str in
  let ast = makeKeywords [] ast in
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
      let graphData = graphDataFromEnv env in
      let cfaRes : CFAGraph = cfaData graphData tANF in
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
"id,ident,context,deps,searchSpace
1,m,,0,2.

id,ident,context,deps,domainSize
0,h,,1,2
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
"id,ident,context,deps,searchSpace
2,m,,0|1,4.

id,ident,context,deps,domainSize
0,hh,h1,2,2
1,hh,h2,2,2
"
in

-- Context-sensitivity
-- TODO: why isn't m context sensitive?
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
"id,ident,context,deps,searchSpace
4,m,,0|1,4.

id,ident,context,deps,domainSize
0,hh,h1,4,2
1,hh,h2,4,2
2,dummy,g1,,2
3,dummy,g2,,2
"
in


()
