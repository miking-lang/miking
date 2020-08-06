include "option.mc"
include "seq.mc"
include "set.mc"
include "map.mc"

-- Represents a directed graph with labeled edges.

-- Vertices and labels can be of any data types, as long as they have an
-- equality function (given as arguments to the graph when created).

-- An edge is represented as a triple (from, to, label), where the edge goes
-- from "from" to "to", and "label" is the label of the edge. There can be
-- several edges between two vertices.

-- Vertices must be unique: there cannot be two vertices whose value of the
-- equality function is true. This is maintained as invariant. Similarly, labels
-- between any pair of vertices must be unique; this is also maintained as
-- invariant.

-- Presently, the graph is implemented using an adjacency map, which maps each
-- vertex to a list of outgoing edges from that vertex.

type Digraph = { adj : [(a,[(a,b)])],
                 eqv : a -> a -> Bool,
                 eql : b -> b -> Bool }

-- Returns an empty graph. Input: equality functions for vertices and labels.
let digraphEmpty = lam eqv. lam eql. {adj = [], eqv = eqv, eql = eql}

-- Get the vertices of the graph g.
let digraphVertices = lam g. (map (lam tup. tup.0) g.adj)

-- Get the edges of the graph g.
let digraphEdges = lam g.
    foldl concat []
      (map
        (lam tup.
           let v = tup.0 in
           let edgelist = tup.1 in
           (map (lam tup. (v, tup.0, tup.1)) edgelist))
       g.adj)

-- Get the outgoing edges from vertex v in graph g.
let digraphEdgesFrom = lam v. lam g.
                       map (lam tup. (v, tup.0, tup.1)) (mapLookup g.eqv v g.adj)

-- Get the incoming edges to vertex v in graph g.
let digraphEdgesTo = lam v. lam g.
                     let allEdges = digraphEdges g in
                     filter (lam tup. g.eqv v tup.1) allEdges

-- Get all edges from v1 to v2 in graph g.
let digraphEdgesBetween = lam v1. lam v2. lam g.
  let fromV1 = digraphEdgesFrom v1 g in
  filter (lam tup. g.eqv v2 tup.1) fromV1

-- Get all labels between v1 and v2 in graph g.
let digraphLabels = lam v1. lam v2. lam g.
    let from_v1_to_v2 = filter (lam tup. g.eqv tup.1 v2) (digraphEdgesFrom v1 g) in
    map (lam tup. tup.2) from_v1_to_v2

-- Get the number of vertices in graph g.
let digraphCountVertices = lam g. length g.adj

-- Get the number of edges in graph g.
let digraphCountEdges = lam g. length (digraphEdges g)

-- Check whether g has vertex v.
let digraphHasVertex = lam v. lam g. any (g.eqv v) (digraphVertices g)

-- Check whether g has all the vertices vs.
let digraphHasVertices = lam vs. lam g.
                         all (lam b. b) (map (lam v. digraphHasVertex v g) vs)

-- Check whether edges e1 and e2 are equal in graph g.
let digraphEdgeEq = lam g. lam e1. lam e2.
                    and (and (g.eqv e1.0 e2.0)
                             (g.eqv e1.1 e2.1))
                        (g.eql e1.2 e2.2)

-- Check whether graph g has all the edges in es.
let digraphHasEdges = lam es. lam g.
                      setIsSubsetEq (digraphEdgeEq g) es (digraphEdges g)

-- Get successor nodes of v.
let digraphSuccessors = lam v. lam g.
  distinct g.eqv (map (lam tup. tup.1) (digraphEdgesFrom v g))

-- Get predecessor nodes of v.
let digraphPredeccessors = lam v. lam g.
  distinct g.eqv (map (lam tup. tup.0) (digraphEdgesTo v g))

-- Check whether vertex v1 is a successor of vertex v2 in graph g.
let digraphIsSuccessor = lam v1. lam v2. lam g.
  any (g.eqv v1) (digraphSuccessors v2 g)

-- Add vertex v to graph g if it doesn't already exist in g.
-- If v exists in g and check is true, an error is thrown.
-- If v exist in g and check is false, g stays unchanged.
let digraphAddVertexCheck = lam v. lam g. lam check.
  if digraphHasVertex v g then
    if check then error "vertex already exists" else g
  else
    {adj = snoc g.adj (v,[]), eqv = g.eqv, eql = g.eql}

-- Add a vertex to graph g. Throws an error if v already exists in g.
let digraphAddVertex = lam v. lam g.
  digraphAddVertexCheck v g true

-- Maybe add a vertex v to g. Graph stays unchanged if v already exists in g.
let digraphMaybeAddVertex = lam v. lam g.
  digraphAddVertexCheck v g false

-- Add edge e=(v1,v2,l) to graph g.
-- If v1 or v2 do not exist in g, an error is thrown.
-- If l exists in g and check is true, an error is thrown.
-- If l exist in g and check is false, g stays unchanged.
-- Otherwise, e is added to g.
let digraphAddEdgeCheckLabel = lam v1. lam v2. lam l. lam g. lam check.
  if not (digraphHasVertices [v1, v2] g) then
    error "some vertices do not exist"
  else if any (g.eql l) (digraphLabels v1 v2 g) then
    if check then error "label already exists" else g
  else
    {g with adj = mapUpdate g.eqv v1 (lam es. snoc es (v2, l)) g.adj}

-- Add edge e=(v1,v2,l) to g. Throws an error if l already exists in g.
let digraphAddEdge = lam v1. lam v2. lam l. lam g.
    digraphAddEdgeCheckLabel v1 v2 l g true

-- Maybe add edge e=(v1,v2,l) to g. Graph stays unchanged if l already exists in g.
let digraphMaybeAddEdge = lam v1. lam v2. lam l. lam g.
    digraphAddEdgeCheckLabel v1 v2 l g false

-- Add a list of vertices to a graph g.
let digraphAddVertices = lam vs. lam g.
  foldl (lam g. lam v. digraphAddVertex v g) g vs

-- Add a list of edges to a graph g.
let digraphAddEdges = lam es. lam g.
  foldl (lam g. lam e. digraphAddEdge e.0 e.1 e.2 g) g es

-- Create the union of two graphs.
let digraphUnion = lam g1. lam g2.
  let g3 = foldl (lam g. lam v. digraphMaybeAddVertex v g) g1 (digraphVertices g2)
  in foldl (lam g. lam tup. digraphMaybeAddEdge tup.0 tup.1 tup.2 g) g3 (digraphEdges g2)

-- Reverse the direction of graph g.
let digraphReverse = lam g.
  let edgesReversed = map (lam e. (e.1, e.0, e.2)) (digraphEdges g) in
  let vs = digraphVertices g in
  digraphAddEdges edgesReversed (digraphAddVertices vs (digraphEmpty g.eqv g.eql))

-- Strongly connected components of g.
-- From the paper: Depth-First Search and Linear Graph Algorithms, Tarjan 72.
-- https://doi.org/10.1137/0201010
let digraphTarjan = lam g.
  let min = lam l. lam r. if lti l r then l else r in
  let mapMem = mapMem g.eqv in
  let mapLookup = mapLookup g.eqv in
  let mapInsert = mapInsert g.eqv in
  let setMem = setMem g.eqv in

  recursive let strongConnect = lam s. lam v.
    let traverseSuccessors = lam s. lam w.
      if not (mapMem w s.number) then
        let s = strongConnect s w in
        let n = min (mapLookup v s.lowlink) (mapLookup w s.lowlink) in
        {s with lowlink = mapInsert v n s.lowlink}
      else if lti (mapLookup w s.number) (mapLookup v s.number) then
        if setMem w s.stack then
          let n = min (mapLookup v s.lowlink) (mapLookup w s.number) in
          {s with lowlink = mapInsert v n s.lowlink}
        else s
      else s
    in

    let popStackIntoComp = lam s.
      let vn = mapLookup v s.number in

      recursive let work = lam comp. lam stack.
        if null stack then (comp,stack)
        else
          let w = head stack in
          if lti (mapLookup w s.number) vn then (comp,stack)
          else work (snoc comp w) (tail stack)
      in
      let t = work [] s.stack in
      {{s with comps = snoc s.comps t.0}
          with stack = t.1}
    in

    let s = {{{{s with number = mapInsert v s.i s.number}
                  with lowlink = mapInsert v s.i s.lowlink}
                  with stack = cons v s.stack}
                  with i = addi s.i 1}
    in

    let s = foldl traverseSuccessors s (digraphSuccessors v g) in

    if eqi (mapLookup v s.lowlink) (mapLookup v s.number)
    then popStackIntoComp s else s
  in

  let s = foldl (lam s. lam v. if not (mapMem v s.number)
                               then strongConnect s v else s)
                {i = 0, number = [], lowlink = [], stack = [], comps = []}
                (digraphVertices g)
  in s.comps

-- Strongly connected components of g.
let digraphStrongConnects = lam g. digraphTarjan g

-- Print as dot format
let digraphPrintDot = lam g. lam v2str. lam l2str.
  let _ = print "digraph {" in
  let _ = map
    (lam e. let _ = print (v2str e.0) in
            let _ = print " -> " in
            let _ = print (v2str e.1) in
            let _ = print "[label=" in
            let _ = print (l2str e.2) in
            print "];")
    (digraphEdges g) in
  let _ = print "}\n" in ()

mexpr
let l1 = gensym () in
let l2 = gensym () in
let l3 = gensym () in
let l4 = gensym () in

let empty = digraphEmpty eqi eqs in

utest digraphEdges empty with [] in
utest digraphVertices empty with [] in
utest digraphCountVertices empty with 0 in
utest digraphCountEdges empty with 0 in
utest digraphHasVertex 1 empty with false in

utest digraphCountVertices (digraphAddVertex 1 empty) with 1 in
utest digraphVertices (digraphAddVertex 1 empty) with [1] in
utest digraphHasVertex 1 (digraphAddVertex 1 empty) with true in
utest digraphHasVertex 2 (digraphAddVertex 1 empty) with false in

let g = digraphAddVertex 3 (digraphAddVertex 2 (digraphAddVertex 1 empty)) in
utest digraphHasVertex 1 g with true in
utest digraphHasVertex 2 g with true in
utest digraphHasVertex 3 g with true in
utest digraphHasVertices [1, 2, 3] g with true in
utest digraphHasVertices [3, 2] g with true in
utest digraphHasVertices [1, 2, 3, 4] g with false in
utest digraphEdgesFrom 1 g with [] in
utest digraphLabels 1 2 g with [] in
let g1 = digraphAddEdge 1 2 l2 (digraphAddEdge 1 2 l1 g) in
utest digraphHasEdges [(1, 2, l1), (1, 2, l2)] g1 with true in
utest digraphHasEdges [(1, 2, l2)] g1 with true in
utest digraphHasEdges [(1, 2, l1)] g1 with true in

let g = digraphAddVertex 1 (digraphAddVertex 2 (digraphAddVertex 3 empty)) in
let g1 = (digraphAddEdge 1 2 l2 (digraphAddEdge 1 2 l1 g)) in
utest digraphSuccessors 1 g1 with [2] in
utest digraphPredeccessors 1 g1 with [] in
utest digraphIsSuccessor 2 1 g1 with true in
utest any (eqs l1) (digraphLabels 1 2 g1) with true in
utest any (eqs l2) (digraphLabels 1 2 g1) with true in
utest any (eqs l2) (digraphLabels 2 1 g1) with false in

let g = digraphAddVertex 1 (digraphAddVertex 2 (digraphAddVertex 3 empty)) in
let g = digraphAddEdge 2 3 l4 (digraphAddEdge 1 3 l3 (digraphAddEdge 1 2 l2 (digraphAddEdge 1 2 l1 g))) in
utest digraphEdgesBetween 1 3 g with [(1,3,l3)] in
utest match digraphEdgesBetween 1 2 g with [(1,2,l1),(1,2,l2)] | [(1,2,l2),(1,2,l1)] then true else false with true in
utest match digraphPredeccessors 3 g with [1,2] | [2,1] then true else false with true in

let g = digraphAddEdges [(1,2,l1),(1,3,l2),(3,1,l3)] (digraphAddVertices [1,2,3] empty) in
let gRev = digraphReverse g in
utest digraphHasEdges [(2,1,l1),(3,1,l2),(1,3,l3)] gRev with true in
utest digraphCountVertices gRev with 3 in
utest digraphCountEdges gRev with 3 in

let l3 = gensym () in
let g2 = digraphAddEdge 3 2 l3 g1 in
utest digraphIsSuccessor 2 3 g2 with true in
utest any (eqs l3) (digraphLabels 3 2 g2) with true in

let g3 = digraphUnion (digraphAddVertex 1 empty) (digraphAddVertex 2 empty) in
utest digraphCountVertices g3 with 2 in
utest digraphCountEdges g3 with 0 in
let g4 = digraphUnion (digraphAddEdge 1 2 l1 g3) (digraphAddEdge 1 2 l2 g3) in
utest digraphCountVertices g4 with 2 in
utest digraphCountEdges g4 with 2 in
let g5 = digraphUnion g4 g4 in
utest digraphCountVertices g5 with 2 in
utest digraphCountEdges g5 with 2 in
let g6 = digraphUnion empty empty in
utest digraphCountVertices g6 with 0 in

let compsEq = setEqual (setEqual eqi) in

utest compsEq (digraphStrongConnects empty) [] with true in

let g = foldr digraphAddVertex empty [1,2,3,4,5,6,7,8] in

let g1 = g in

utest compsEq (digraphStrongConnects g1) [[1],[2],[3],[4],[5],[6],[7],[8]]
with true in

let g2 = digraphAddEdge 1 2 (gensym ()) g in
let g2 = digraphAddEdge 2 3 (gensym ()) g2 in
let g2 = digraphAddEdge 3 1 (gensym ()) g2 in
let g2 = digraphAddEdge 4 5 (gensym ()) g2 in
let g2 = digraphAddEdge 5 4 (gensym ()) g2 in

utest compsEq (digraphStrongConnects g2) [[1,2,3],[4,5],[6],[7],[8]]
with true in

-- Figure 3 from Tarjans original paper.
let g3 = digraphAddEdge 1 2 (gensym ()) g in
let g3 = digraphAddEdge 2 3 (gensym ()) g3 in
let g3 = digraphAddEdge 2 8 (gensym ()) g3 in
let g3 = digraphAddEdge 3 4 (gensym ()) g3 in
let g3 = digraphAddEdge 3 7 (gensym ()) g3 in
let g3 = digraphAddEdge 4 5 (gensym ()) g3 in
let g3 = digraphAddEdge 5 3 (gensym ()) g3 in
let g3 = digraphAddEdge 5 6 (gensym ()) g3 in
let g3 = digraphAddEdge 7 4 (gensym ()) g3 in
let g3 = digraphAddEdge 7 6 (gensym ()) g3 in
let g3 = digraphAddEdge 8 1 (gensym ()) g3 in
let g3 = digraphAddEdge 8 7 (gensym ()) g3 in

utest compsEq (digraphStrongConnects g3) [[1,2,8],[3,4,5,7],[6]] with true in

()
