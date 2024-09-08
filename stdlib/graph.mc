include "digraph.mc"

-- Represents a graph with labeled edges.

-- Vertices and labels can be of any data types, as long as they have an
-- equality function (given as arguments to the graph when created).

-- An edge is represented as a triple (v1, v2, label), where the edge connects
-- the vertices v1 and v2, and "label" is the label of the edge. There can be
-- several edges between two vertices.

-- Vertices must be unique: there cannot be two vertices whose value of the
-- equality function is true. This is maintained as invariant. Similarly, labels
-- between any pair of vertices must be unique; this is also maintained as
-- invariant.

-- Presently, the graph is implemented using an adjacency map, which maps each
-- vertex to a list of incident edges upon that vertex.

type Graph v l = Digraph v l

-- Returns an empty graph. Input: equality functions for vertices and labels.
let graphEmpty = digraphEmpty

-- Access vertices and edges
let graphVertices = digraphVertices

-- Get comparison function for vertices.
let graphCmpv : all v. all l. Graph v l -> v -> v -> Int =
  lam g. mapGetCmpFun g.adj

let graphEdgeEq : all v. all l. Graph v l -> DigraphEdge v l -> DigraphEdge v l -> Bool =
  lam g. lam e1. lam e2.
  let eqv = digraphEqv g in
  and (or (and (eqv e1.0 e2.0) (eqv e1.1 e2.1))
          (and (eqv e1.1 e2.0) (eqv e1.0 e2.1)))
      (g.eql e1.2 e2.2)

let graphEdges = lam g. distinct (graphEdgeEq g) (digraphEdges g) -- Remove duplicate edges

let graphEdgesFrom = digraphEdgesFrom

let graphLabels = digraphLabels

let graphCountVertices = digraphCountVertices

let graphCountEdges = lam g. divi (digraphCountEdges g) 2

let graphHasVertex = digraphHasVertex

let graphHasEdges = digraphHasEdges

let graphHasVertices = digraphHasVertices

let graphNeighbors = digraphSuccessors

let graphIsAdjacent = digraphIsSuccessor

-- Add vertices and edges
let graphAddVertex = digraphAddVertex

let graphMaybeAddVertex = digraphMaybeAddVertex

let graphAddEdge = lam v1. lam v2. lam l. lam g.
    digraphAddEdge v1 v2 l (digraphAddEdge v2 v1 l g)

let graphAddVertices = lam vs. lam g.
  foldl (lam g. lam v. graphAddVertex v g) g vs

let graphAddEdges : all v. all l. [DigraphEdge v l] -> Graph v l -> Graph v l =
  lam es. lam g.
    foldl (lam g. lam e : DigraphEdge v l. graphAddEdge e.0 e.1 e.2 g) g es

let graphConnectedComponents : all v. all l. Graph v l -> [[v]] = lam g.
  let cs : [Map v Int] = foldl (
    lam acc: [Map v Int]. lam v: v.
      if any (mapMem v) acc then acc
      else cons (digraphBFS v g) acc
    ) [] (graphVertices g)
  in map mapKeys cs

let graphRemoveVertex: all v. all l. v -> Graph v l -> Graph v l = lam v. lam g.
  -- Remove all edges containing 'v'
  let edges = graphEdgesFrom v g in
  let g: Graph v l = foldl (lam acc. lam e: (v, v, l).
      let acc = digraphRemoveEdge e.0 e.1 e.2 acc in
      digraphRemoveEdge e.1 e.0 e.2 acc
    ) g edges
  in
  -- Remove 'v' itself
  {g with adj = mapRemove v g.adj}

-- Finds the maximal cliques of a given graph using the Bron Kerbosch
-- algorithm: https://en.wikipedia.org/wiki/Bron%E2%80%93Kerbosch_algorithm.
-- NOTE(larshum, 2024-05-09): This algorithm solves an NP-hard problem, so it
-- runs in exponential time.
let bronKerbosch : all v. all l. Graph v l -> [Set v] = lam g.
  let cmpv = graphCmpv g in
  recursive let helper : [Set v] -> Set v -> Set v -> Set v -> [Set v] =
    lam cliques. lam r. lam p. lam x.
    if and (setIsEmpty p) (setIsEmpty x) then cons r cliques
    else
      let u =
        match setChoose p with Some u then u
        else match setChoose x with Some u then u
        else error "BronKerbosch: Impossible case"
      in
      let pmnu = setSubtract p (setOfSeq cmpv (graphNeighbors u g)) in
      let acc =
        setFold
          (lam acc. lam v.
            match acc with (cliques, p, x) in
            let nv = setOfSeq cmpv (graphNeighbors v g) in
            let cliques =
              helper cliques (setInsert v r) (setIntersect p nv) (setIntersect x nv)
            in
            (cliques, setRemove v p, setInsert v x))
          (cliques, p, x) pmnu
      in
      acc.0
  in

  -- Order the graph vertices by degree, so we can repeatedly select the vertex
  -- with the minimum degree.
  let #var"V" = graphVertices g in
  let vertexDegrees =
    mapFromSeq cmpv (map (lam v. (v, length (graphNeighbors v g))) #var"V")
  in
  let deg = lam v.
    match mapLookup v vertexDegrees with Some d then d
    else error "BronKerbosch: Could not find vertex"
  in
  let degord = sort (lam v1. lam v2. subi (deg v1) (deg v2)) #var"V" in
  let acc =
    foldl
      (lam acc. lam v.
        match acc with (cliques, p, x) in
        let nv = setOfSeq cmpv (graphNeighbors v g) in
        let r = setOfSeq cmpv [v] in
        let cliques = helper cliques r (setIntersect p nv) (setIntersect x nv) in
        (cliques, setRemove v p, setInsert v x))
      ([], setOfSeq cmpv #var"V", setEmpty cmpv) degord
  in
  acc.0

mexpr

let empty = graphEmpty subi eqsym in

utest graphEdges empty with [] in
utest graphVertices empty with [] in
utest graphCountVertices empty with 0 in
utest graphCountEdges empty with 0 in
utest graphHasVertex 1 empty with false in

utest graphCountVertices (graphAddVertex 1 empty) with 1 in
utest graphVertices (graphAddVertex 1 empty) with [1] in
utest graphHasVertex 1 (graphAddVertex 1 empty) with true in
utest graphHasVertex 2 (graphAddVertex 1 empty) with false in

let g = graphAddVertex 3 (graphAddVertex 2 (graphAddVertex 1 empty)) in
utest graphHasVertex 1 g with true in
utest graphHasVertex 2 g with true in
utest graphHasVertex 3 g with true in
utest graphHasVertices [1, 2, 3] g with true in
utest graphHasVertices [3, 2] g with true in
utest graphHasVertices [1, 2, 3, 4] g with false in
let l1 = gensym () in
let l2 = gensym () in
utest graphEdgesFrom 1 g with [] in
utest graphLabels 1 2 g with [] in
let g1 = graphAddEdge 1 2 l2 (graphAddEdge 1 2 l1 g) in
utest graphHasEdges [(1, 2, l1), (1, 2, l2)] g1 with true in
utest graphHasEdges [(1, 2, l2)] g1 with true in
utest graphHasEdges [(1, 2, l1)] g1 with true in
utest graphHasEdges [(2, 1, l1), (2, 1, l2)] g1 with true in
utest graphHasEdges [(2, 1, l2)] g1 with true in
utest graphHasEdges [(2, 1, l1)] g1 with true in

let l1 = gensym () in
let g = graphAddVertex 1 (graphAddVertex 2 (graphAddVertex 3 empty)) in
let g1 = graphAddEdge 1 2 l1 g in
utest graphNeighbors 1 g1 with [2] in
utest graphIsAdjacent 2 1 g1 with true in
utest graphIsAdjacent 1 2 g1 with true in
utest any (eqsym l1) (graphLabels 1 2 g1) with true in
utest any (eqsym l1) (graphLabels 1 2 g1) with true in

let l3 = gensym () in
let g2 = graphAddEdge 3 2 l3 g1 in
utest graphIsAdjacent 2 3 g2 with true in
utest graphIsAdjacent 3 2 g2 with true in
utest any (eqsym l3) (graphLabels 3 2 g2) with true in

let compsEq = eqsetEqual (eqsetEqual eqi) in

utest compsEq (digraphStrongConnects empty) [] with true in

let g = foldr graphAddVertex empty [1,2,3,4,5,6,7,8] in

let g1 = g in

utest compsEq (digraphStrongConnects g1) [[1],[2],[3],[4],[5],[6],[7],[8]]
with true in

let g2 = graphAddEdge 1 2 (gensym ()) g in
let g2 = graphAddEdge 2 3 (gensym ()) g2 in
let g2 = graphAddEdge 3 1 (gensym ()) g2 in
let g2 = graphAddEdge 4 5 (gensym ()) g2 in
let g2 = graphAddEdge 5 4 (gensym ()) g2 in

utest compsEq (digraphStrongConnects g2) [[1,2,3],[4,5],[6],[7],[8]]
with true in

-- Figure 3 from Tarjans original paper with undirected edges.
let g3 = graphAddEdge 1 2 (gensym ()) g in
let g3 = graphAddEdge 2 3 (gensym ()) g3 in
let g3 = graphAddEdge 2 8 (gensym ()) g3 in
let g3 = graphAddEdge 3 4 (gensym ()) g3 in
let g3 = graphAddEdge 3 7 (gensym ()) g3 in
let g3 = graphAddEdge 4 5 (gensym ()) g3 in
let g3 = graphAddEdge 5 3 (gensym ()) g3 in
let g3 = graphAddEdge 5 6 (gensym ()) g3 in
let g3 = graphAddEdge 7 4 (gensym ()) g3 in
let g3 = graphAddEdge 7 6 (gensym ()) g3 in
let g3 = graphAddEdge 8 1 (gensym ()) g3 in
let g3 = graphAddEdge 8 7 (gensym ()) g3 in

utest compsEq (digraphStrongConnects g3) [[1,2,8,3,4,5,7,6]] with true in

let gcc = graphAddEdges
  [ (0,4,gensym ())
  , (1,4,gensym ())
  , (1,5,gensym ())
  , (2,6,gensym ())
  , (3,6,gensym ())
  ] (graphAddVertices [0,1,2,3,4,5,6] empty)
in

utest graphConnectedComponents gcc with [[0,1,4,5],[2,3,6]] using compsEq in

utest
  let g = graphAddEdges
  [ (0,1,gensym ())
  , (0,2,gensym ())
  , (1,2,gensym ())
  ] (graphAddVertices [0,1,2] empty)
  in
  let g = graphRemoveVertex 0 g in
  (graphVertices g, graphCountEdges g, graphIsAdjacent 1 2 g)
with ([1,2], 1, true) in

-- Bron Kerbosch tests
let ppSets = lam l. lam r.
  let pp = lam s.
    strJoin ", "
      (map
        (lam is. join ["{", strJoin " " (map int2string (setToSeq is)), "}"])
        (setToSeq s))
  in
  join [
    "  LHS: ", pp l, "\n",
    "  RHS: ", pp r
  ]
in

let g = graphEmpty subi (lam. lam. true) in
let g = graphAddVertices [1,2,3,4,5,6] g in
let g = graphAddEdges [
  (1, 2, ()),
  (1, 5, ()),
  (2, 3, ()),
  (2, 5, ()),
  (3, 4, ()),
  (4, 5, ()),
  (4, 6, ())
] g in
let out = setOfSeq setCmp (bronKerbosch g) in
let expected = setOfSeq setCmp [
  setOfSeq subi [2, 3],
  setOfSeq subi [3, 4],
  setOfSeq subi [4, 5],
  setOfSeq subi [4, 6],
  setOfSeq subi [1, 2, 5]
] in
utest out with expected using setEq else ppSets in

let g = graphEmpty subi (lam. lam. true) in
let g = graphAddVertices [1,2,3,4,5,6,7,8,9] g in
let g = graphAddEdges [
  (1, 2, ()),
  (1, 3, ()),
  (1, 4, ()),
  (2, 3, ()),
  (2, 4, ()),
  (2, 6, ()),
  (2, 7, ()),
  (3, 4, ()),
  (4, 6, ()),
  (5, 6, ()),
  (5, 7, ()),
  (5, 8, ()),
  (6, 7, ()),
  (8, 9, ())
] g in
let out = setOfSeq setCmp (bronKerbosch g) in
let expected = setOfSeq setCmp [
  setOfSeq subi [1,2,3,4],
  setOfSeq subi [5,6,7],
  setOfSeq subi [2,6,7],
  setOfSeq subi [2,4,6],
  setOfSeq subi [5,8],
  setOfSeq subi [8,9]
] in
utest out with expected using setEq else ppSets in

()
