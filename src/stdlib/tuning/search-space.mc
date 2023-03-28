
-- Implements helper functions for analyzing the search space of a program with
-- holes, given a dependency graph.

include "dependency-analysis.mc"
include "data-frame.mc"

include "map.mc"
include "graph.mc"
include "eqset.mc"

-- NOTE: floats because of numerical overflows with ints
type SearchSpaceSize = {
  -- Maps the id of a measuring point to its search space size.
  measuringPoints : Map Int Float,
  -- The connected components and their search space size.
  connectedComponents : [([Int], Float)],
  -- The total size of the search space (Cartesian product)
  sizeTotal : Float,
  -- The size of the reduced search space (taking dependencies into account)
  sizeReduced : Float
}

-- Computes the Cartesian product of the sequences in 'seqs', ordering
-- unspecified.
recursive let searchSpaceProduct : all a. [[a]] -> [[a]] = lam seqs.
  recursive let work = lam acc. lam s1. lam s2.
    if null s1 then acc
    else if null s2 then acc
    else match (s1, s2) with ([h1] ++ t1, [h2] ++ t2) in
      let acc = cons (cons h1 h2) acc in
      let acc = work acc t1 s2 in
      work acc [h1] t2
  in
  if null seqs then []
  else match seqs with [s] then
    map (lam x. [x]) s
  else
    let t = searchSpaceProduct (tail seqs) in
    work [] (head seqs) t
end

let _productEq : all a. (a -> a -> Int) -> [[a]] -> [[a]] -> Bool =
  lam cmp : a -> a -> Int. lam p1 : [[a]]. lam p2 : [[a]].
    let p1 = sort (seqCmp cmp) p1 in
    let p2 = sort (seqCmp cmp) p1 in
    let eq = lam s1. lam s2. eqi (seqCmp cmp s1 s2) 0 in
    eqSeq eq p1 p2

utest searchSpaceProduct [[],[1,2,3]] with [] using _productEq subi
utest searchSpaceProduct [[1,2,3]] with [[1],[2],[3]] using _productEq subi
utest searchSpaceProduct [[1,2,3],[4,5]] with [[1,4],[1,5],[2,4],[2,5],[3,4],[3,5]] using _productEq subi
utest searchSpaceProduct [[1],[2,3],[4]] with [[1,2,4],[1,3,4]] using _productEq subi

let _searchSpaceTestEq = lam lhs: Map Int Float. lam rhs: [(Int,Float)].
  eqSeq (lam t1: (Int,Float). lam t2: (Int,Float).
    and (eqi t1.0 t2.0) (eqf t1.1 t2.1)
  ) (mapBindings lhs) rhs

let searchSpaceSizeMeasuringPoint
  : [Int] -> Graph Int Int -> [Float] -> Map Int Float =
  lam points. lam graph. lam holeDomainSize.
    foldl (lam acc : Map Int Float. lam m.
      let holes = graphNeighbors m graph in
      let size =
        if null holes then 0.
        else
          foldl (
            lam acc. lam h.
              mulf acc (get holeDomainSize h)
            ) 1. holes
      in
      mapInsert m size acc
    ) (mapEmpty subi) points

utest
  let g = graphAddEdges [(0,2,0),(0,3,0),(1,3,0),(1,4,0)] (
    graphAddVertices [0,1,2,3,4] (graphEmpty subi eqi))
  in
  let domains = [3.,5.] in
  searchSpaceSizeMeasuringPoint [2,3,4] g domains
with [(2,3.),(3,15.),(4,5.)]
using _searchSpaceTestEq

let searchSpaceSizeConnectedComponent
  : Map Int Float -> Graph Int Int -> [Float] -> [([Int], Float)] =
  lam pointSizes. lam graph. lam holeDomainSize.
    let ccs = graphConnectedComponents graph in
    map (lam cc : [Int].
      let maxSize = foldl (lam acc. lam v.
        match mapLookup v pointSizes with Some s then
          if gtf s acc then s else acc
        else acc) 0. cc
      in
      (cc, maxSize)
    ) ccs

utest
  let g = graphAddEdges [(0,4,0),(1,4,0),(1,5,0),(2,6,0),(3,6,0)] (
    graphAddVertices [0,1,2,3, 4,5,6] (graphEmpty subi eqi))
  in
  let domains = [2.,3.,4.,5.] in
  let pointSizes = searchSpaceSizeMeasuringPoint [4,5,6] g domains in
  searchSpaceSizeConnectedComponent pointSizes g domains
with [ ([0,1,4,5],6.), ([2,3,6],20.) ]
using eqsetEqual (lam t1: ([Int],Float). lam t2: ([Int],Float).
  and (eqSeq eqi t1.0 t2.0) (eqf t1.1 t2.1))

lang SearchSpace = DependencyAnalysis
  sem searchSpaceSize (stepSize : Int) (env : CallCtxEnv) =
  | dep ->
    let dep : DependencyGraph = dep in
    let holeDomainSizes = map (domainSize stepSize) env.idx2hole in
    let holeDomainSizes: [Float] = map int2float holeDomainSizes in
    let mps = setToSeq dep.alive in
    if null mps then
      { measuringPoints = mapEmpty subi, connectedComponents = [],
        sizeTotal = 0., sizeReduced = 0. }
    else
      let sizeMps: Map Int Float = searchSpaceSizeMeasuringPoint mps dep.graph holeDomainSizes in
      let sizeCC: [([Int], Float)] = searchSpaceSizeConnectedComponent sizeMps dep.graph holeDomainSizes in
      let sizeTotal: Float = foldl mulf 1. holeDomainSizes in
      let sizeReduced: Float = optionGetOrElse (lam. error "Empty search space")
        (max (cmpfApprox 0.) (map (lam c : ([Int], Float). c.1) sizeCC))
      in
      { measuringPoints = sizeMps, connectedComponents = sizeCC,
        sizeTotal = sizeTotal, sizeReduced = sizeReduced }

  sem searchSpaceExhaustive (stepSize : Int) (env : CallCtxEnv) =
  | dep ->
    let dep : DependencyGraph = dep in
    let domains : [[Expr]] = map (domain stepSize) env.idx2hole in
    let mps = setToSeq dep.alive in
    searchSpaceExhaustiveH mps dep.graph domains

  sem searchSpaceExhaustiveMeasPoints (mp : [Int]) (graph : Graph Int Int) =
  | domains ->
    let domains : [[Expr]] = domains in
    -- Generate exhaustive tables for each measuring point
    let tables = map (lam m.
      let holes = graphNeighbors m graph in
      let doms = map (get domains) holes in
      let prod = searchSpaceProduct doms in
      (holes, prod)
    ) mp
    in tables

  sem searchSpaceExhaustiveH (mp : [Int]) (graph : Graph Int Int) =
  | domains ->
    let tables = searchSpaceExhaustiveMeasPoints mp graph domains in

    -- The longest table is the initial base table
    match
      foldl (lam acc. lam table: ([Int],[[Expr]]).
        match acc with (cur, longest, t) in
        if gti (length table.1) (length t) then (addi cur 1, cur, table.1)
        else (addi cur 1, longest, t)
      ) (0, subi 0 1, []) tables
    with (_, longestIdx, longestTable) in

    utest geqi longestIdx 0 with true in

    -- Create a data frame from the base table
    let ncols = if null longestTable then 0 else length (head longestTable) in
    let df = dataFrameFromSeq longestTable ncols in
    let df = dataFrameMap (lam x. Some x) df in

    -- Extend columns of base table to include all holes, add empty slots for
    -- unknown values
    let ncols = length domains in
    let idxs =
      let t : ([Int],[[Expr]]) = get tables longestIdx in
      t.0
    in
    let df =
      -- No need to extend if already fully sized
      if eqi ncols df.ncols then df
      else dataFrameExtendCols ncols idxs (None ()) df
    in

    -- Equality function: handle None () as a match.
    -- OPT(Linnea,2022-02-02): Check fuzzy vs. exact match
    let eq = lam e1. lam e2.
      use MExprEq in
      switch (e1, e2)
      case ((None (), _) | (_, None ())) then true
      case (Some v1, Some v2) then eqExpr v1 v2
      end
    in

    -- For each row in each table: find first matching row in data frame, add
    -- the row there.
    match
      -- For each table
      foldl (lam acc. lam t : ([Int],[[Expr]]).
        match acc with (i, df) in
        -- Skip the original base table (already in the data frame)
        if eqi i longestIdx then (addi i 1, df) else

        match t with (idxs, table) in
        -- For each row in the table
        let df =
          foldl (lam df. lam row.
            let row = map (lam x. Some x) row in
            -- By construction, there has to be a matching row
            match dataFrameHasRowSlice eq idxs row df with Some i then
              dataFrameSetRowSlice i idxs row df
            else error "Impossible: no match in data frame"
            ) df table
        in (addi i 1, df)
      ) (0, df) tables
    with (_, df) in
    df
end

lang Test = SearchSpace + MExprEq end

mexpr

use Test in

let debug = false in

let optionInt2str = lam x.
  use MExprAst in
  match x with Some (TmConst {val = CInt {val = i}}) then int2string i
  else match x with None () then "-"
  else never
in

let eqTestMeasPoints = lam lhs : [([Int],[[Expr]])]. lam rhs : [([Int],[[Expr]])].
  let eqElem = lam l : ([Int],[[Expr]]). lam r : ([Int],[[Expr]]).
    if eqSeq eqi l.0 r.0 then
      eqsetEqual (eqSeq eqExpr) l.1 r.1
    else false
  in eqsetEqual eqElem lhs rhs
in

let eqOptionInt = lam lhs : Option Expr. lam rhs : Option Int.
  use MExprEq in
  switch (lhs, rhs)
  case (None (), None ()) then true
  case (Some e1, Some i2) then eqExpr e1 (int_ i2)
  case ((None (), _) | (_, None ())) then false
  case t then dprintLn t; error "impossible"
  end
in

let eqTestDF = lam lhs : DataFrame (Option Expr). lam rhs : [[Option Int]].
  dataFrameEq eqOptionInt lhs (dataFrameFromSeq rhs (length (head rhs)))
in

utest
  let g = graphAddEdges [(0,2,0),(0,3,0),(1,3,0),(1,4,0)] (
    graphAddVertices [0,1,2,3,4] (graphEmpty subi eqi))
  in
  let mp = [2,3,4] in
  let domains = [[int_ 0, int_ 1], [int_ 2, int_ 3, int_ 4]] in
  searchSpaceExhaustiveMeasPoints mp g domains
with
[ ([0],  [ [int_ 0], [int_ 1] ])
, ([0,1],[ [int_ 0, int_ 2]
         , [int_ 0, int_ 3]
         , [int_ 0, int_ 4]
         , [int_ 1, int_ 2]
         , [int_ 1, int_ 3]
         , [int_ 1, int_ 4]
         ])
, ([1],  [ [int_ 2], [int_ 3], [int_ 4] ])
] using eqTestMeasPoints in


utest
  let g = graphAddEdges [(0,2,0),(0,3,0),(1,3,0),(1,4,0)] (
    graphAddVertices [0,1,2,3,4] (graphEmpty subi eqi))
  in
  let mp = [2,3,4] in
  let domains = [[int_ 0, int_ 1], [int_ 2, int_ 3, int_ 4]] in
  let df = searchSpaceExhaustiveH mp g domains in
  (if debug then printLn (dataFrame2str optionInt2str df) else ());
  df
with
[ [Some 0, Some 2]
, [Some 0, Some 3]
, [Some 0, Some 4]
, [Some 1, Some 2]
, [Some 1, Some 3]
, [Some 1, Some 4]
] using eqTestDF in


utest
  let g = graphAddEdges [(0,3,0),(1,3,0),(1,4,0),(2,4,0)] (
    graphAddVertices [0,1,2,3,4] (graphEmpty subi eqi))
  in
  let mp = [3,4] in
  let domains = [[int_ 0, int_ 1, int_ 2], [int_ 0, int_ 1, int_ 2], [int_ 0, int_ 1, int_ 2]] in
  let df : DataFrame (Option Expr) = searchSpaceExhaustiveH mp g domains in
  (if debug then printLn (dataFrame2str optionInt2str df) else ());
  -- Several different data frames are possible, so we check its properties
  let eq = optionEq eqExpr in
  let _oe = lam row: [Int]. map (lam i. Some (int_ i)) row in
  forAll (lam x. x)
  [ eqi df.ncols 3
  , eqi (length df.data) 9
  -- Measuring point 3
  , optionIsSome (dataFrameHasRowSlice eq [0,1] (_oe [0,0]) df)
  , optionIsSome (dataFrameHasRowSlice eq [0,1] (_oe [0,1]) df)
  , optionIsSome (dataFrameHasRowSlice eq [0,1] (_oe [0,2]) df)
  , optionIsSome (dataFrameHasRowSlice eq [0,1] (_oe [1,0]) df)
  , optionIsSome (dataFrameHasRowSlice eq [0,1] (_oe [1,1]) df)
  , optionIsSome (dataFrameHasRowSlice eq [0,1] (_oe [1,2]) df)
  , optionIsSome (dataFrameHasRowSlice eq [0,1] (_oe [2,0]) df)
  , optionIsSome (dataFrameHasRowSlice eq [0,1] (_oe [2,1]) df)
  , optionIsSome (dataFrameHasRowSlice eq [0,1] (_oe [2,2]) df)
  -- Measuring point 4
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [0,0]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [0,1]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [0,2]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [1,0]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [1,1]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [1,2]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [2,0]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [2,1]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [2,2]) df)
  ]
with true in


utest
  let g = graphAddEdges [(0,2,0),(1,3,0)] (
    graphAddVertices [0,1,2,3] (graphEmpty subi eqi))
  in
  let mp = [2,3] in
  let domains = [[int_ 0, int_ 1], [int_ 2, int_ 3, int_ 4]] in
  let df : DataFrame (Option Expr) = searchSpaceExhaustiveH mp g domains in
  (if debug then printLn (dataFrame2str optionInt2str df) else ());
  -- Several different data frames are possible, so we check its properties
  let eq = optionEq eqExpr in
  let _oe = lam row: [Int]. map (lam i. Some (int_ i)) row in
  use MExprEq in
  forAll (lam x. x)
  [ eqi df.ncols 2
  , eqi (length df.data) 3
  -- Measuring point 2 (has one 'bubble')
  , optionIsSome (dataFrameHasRowSlice eq [0] (_oe [0]) df)
  , optionIsSome (dataFrameHasRowSlice eq [0] (_oe [1]) df)
  , optionIsSome (dataFrameHasRowSlice (optionEq eqExpr) [0] [None ()] df)
  -- Measuring point 4
  , optionIsSome (dataFrameHasRowSlice eq [1] (_oe [2]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1] (_oe [3]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1] (_oe [4]) df)
  ]
with true in


utest
  let g = graphAddEdges [(0,3,0),(1,4,0),(2,4,0)] (
    graphAddVertices [0,1,2,3,4] (graphEmpty subi eqi))
  in
  let mp = [3,4] in
  let domains = [[int_ 0, int_ 1], [int_ 0, int_ 1], [int_ 0, int_ 1]] in
  let df : DataFrame (Option Expr) = searchSpaceExhaustiveH mp g domains in
  (if debug then printLn (dataFrame2str optionInt2str df) else ());
  -- Several different data frames are possible, so we check its properties
  let eq = optionEq eqExpr in
  let _oe = lam row: [Int]. map (lam i. Some (int_ i)) row in
  use MExprEq in
  forAll (lam x. x)
  [ eqi df.ncols 3
  , eqi (length df.data) 4
  -- Measuring point 3 (has two 'bubbles')
  , optionIsSome (dataFrameHasRowSlice eq [0] (_oe [0]) df)
  , optionIsSome (dataFrameHasRowSlice eq [0] (_oe [1]) df)
  , optionIsSome (dataFrameHasRowSlice (optionEq eqExpr) [0] [None ()] df)
  -- Measuring point 4
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [0,0]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [0,1]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [1,0]) df)
  , optionIsSome (dataFrameHasRowSlice eq [1,2] (_oe [1,1]) df)
  ]
with true in

()
