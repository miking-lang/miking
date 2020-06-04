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

type Graph = Digraph

-- Returns an empty graph. Input: equality functions for vertices and labels.
let graphEmpty = digraphEmpty

-- Access vertices and edges
let graphVertices = digraphVertices

let graphEdgeEq = lam g. lam e1. lam e2.
  and (or (and (g.eqv e1.0 e2.0) (g.eqv e1.1 e2.1))
          (and (g.eqv e1.1 e2.0) (g.eqv e1.0 e2.1)))
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

let graphIsAdjecent = digraphIsSuccessor

-- Add vertices and edges
let graphAddVertex = digraphAddVertex

let graphMaybeAddVertex = digraphMaybeAddVertex

let graphAddEdge = lam v1. lam v2. lam l. lam g.
    digraphAddEdge v1 v2 l (digraphAddEdge v2 v1 l g)

let graphMaybeAddEdge = lam v1. lam v2. lam l. lam g.
    digraphMaybeAddEdge v2 v1 l (digraphMaybeAddEdge v1 v2 l g)

-- Union of two graphs
let graphUnion = digraphUnion

mexpr

let empty = graphEmpty eqi eqs in

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
utest graphIsAdjecent 2 1 g1 with true in
utest graphIsAdjecent 1 2 g1 with true in
utest any (eqs l1) (graphLabels 1 2 g1) with true in
utest any (eqs l1) (graphLabels 1 2 g1) with true in

let l3 = gensym () in
let g2 = graphAddEdge 3 2 l3 g1 in
utest graphIsAdjecent 2 3 g2 with true in
utest graphIsAdjecent 3 2 g2 with true in
utest any (eqs l3) (graphLabels 3 2 g2) with true in

let l2 = gensym () in
let g3 = graphUnion (graphAddVertex 1 empty) (graphAddVertex 2 empty) in
utest graphCountVertices g3 with 2 in
utest graphCountEdges g3 with 0 in
let g4 = graphUnion (graphAddEdge 1 2 l1 g3) (graphAddEdge 1 2 l2 g3) in
utest graphCountVertices g4 with 2 in
utest graphCountEdges g4 with 2 in
let g5 = graphUnion g4 g4 in
utest graphCountVertices g5 with 2 in
utest graphCountEdges g5 with 2 in
let g6 = graphUnion empty empty in
utest graphCountVertices g6 with 0 in

let compsEq = setEqual (setEqual eqi) in

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

()
