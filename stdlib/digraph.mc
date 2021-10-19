-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Represents a directed graph with labeled edges.
--
-- Vertices and labels can be of any data types, as long as they have an
-- equality function.
--
-- An edge is represented as a triple (from, to, label), where the edge goes
-- from "from" to "to", and "label" is the label of the edge. There can be
-- several edges between two vertices.
--
-- Vertices must be unique: there cannot be two vertices whose value of the
-- equality function is true. This is maintained as invariant. Similarly, labels
-- between any pair of vertices must be unique; this is also maintained as
-- invariant.

include "option.mc"
include "seq.mc"
include "map.mc"
include "eqset.mc"
include "set.mc"

type DigraphEdge v l = (v, v, l)
type Digraph v l = { adj : Map v [(v,l)],
                     eql : l -> l -> Bool }

-- Returns an empty graph. Input: equality functions for vertices and labels.
let digraphEmpty : (v -> v -> Int) -> (l -> l -> Bool) -> Digraph v l =
  lam cmpv : v -> v -> Int. lam eql : l -> l -> Bool.
  {adj = mapEmpty cmpv, eql = eql}

-- Get comparison function for vertices.
let digraphCmpv = lam g : Digraph v l.
  mapGetCmpFun g.adj

-- Get equivalence function for vertices.
let digraphEqv = lam g : Digraph v l.
  lam v1. lam v2. eqi (digraphCmpv g v1 v2) 0

-- Get equivalence function for labels.
let digraphEql = lam g : Digraph v l.
  g.eql

-- Get the vertices of the graph g.
let digraphVertices = lam g : Digraph v l.
  mapKeys g.adj

-- Get the number of vertices in graph g.
let digraphCountVertices = lam g : Digraph v l.
  mapSize g.adj

-- Get the edges of the graph g.
let digraphEdges : Digraph v l -> [DigraphEdge v l] = lam g : Digraph v l.
  foldl (lam acc. lam b : (v, [(v,l)]).
    concat acc (map (lam t : (v, l). (b.0, t.0, t.1)) b.1))
    [] (mapBindings g.adj)

-- Get the edges of the graph g.
let digraphCountEdges = lam g : Digraph v l.
  foldl (lam acc. lam es. addi acc (length es)) 0 (mapValues g.adj)

-- Get the outgoing edges from vertex v in graph g.
let digraphEdgesFrom = lam v : v. lam g : Digraph v l.
  map (lam t : (v, l). (v, t.0, t.1))
    (mapLookupOrElse (lam. error "Lookup failed") v g.adj)

-- Get the incoming edges to vertex v in graph g.
let digraphEdgesTo = lam v : v. lam g : Digraph v l.
  let allEdges = digraphEdges g in
  filter (lam tup : DigraphEdge v l. eqi (digraphCmpv g v tup.1) 0) allEdges

-- Get all edges from v1 to v2 in graph g.
let digraphEdgesBetween : v -> v -> Digraph v l -> [DigraphEdge v l] =
  lam v1. lam v2. lam g : Digraph v l.
  let fromV1 = digraphEdgesFrom v1 g in
  filter (lam t : DigraphEdge v l. eqi (digraphCmpv g v2 t.1) 0) fromV1

-- Get all labels between v1 and v2 in graph g.
let digraphLabels = lam v1 : v. lam v2 : v. lam g : Digraph v l.
  let from_v1_to_v2 =
    filter (lam tup : DigraphEdge v l. eqi (digraphCmpv g tup.1 v2) 0)
      (digraphEdgesFrom v1 g) in
  map (lam tup : DigraphEdge v l. tup.2) from_v1_to_v2

-- Check whether g has vertex v.
let digraphHasVertex = lam v. lam g : Digraph v l.
  mapMem v g.adj

-- Check whether g has all the vertices vs.
let digraphHasVertices = lam vs. lam g.
  all (lam v. digraphHasVertex v g) vs

-- Check whether edges e1 and e2 are equal in graph g.
let digraphEdgeEq =
  lam g : Digraph v l. lam e1 : DigraphEdge v l. lam e2 : DigraphEdge v l.
  and (and (eqi (digraphCmpv g e1.0 e2.0) 0)
           (eqi (digraphCmpv g e1.1 e2.1) 0))
      (g.eql e1.2 e2.2)

-- Check whether g has edge e.
let digraphHasEdge = lam e. lam g.
  any (digraphEdgeEq g e) (digraphEdges g)

-- Check whether graph g has all the edges in es.
let digraphHasEdges = lam es. lam g.
  all (lam e. digraphHasEdge e g) es

-- Get successor nodes of v.
let digraphSuccessors = lam v. lam g : Digraph v l.
  let outgoing = digraphEdgesFrom v g in
  let successors = map (lam t : DigraphEdge v l. t.1) outgoing in
  setToSeq (setOfSeq (digraphCmpv g) successors)

-- Get predecessor nodes of v.
let digraphPredeccessors = lam v. lam g : Digraph v l.
  distinct (lam v1. lam v2. eqi (digraphCmpv g v1 v2) 0)
    (map (lam tup : DigraphEdge v l. tup.0) (digraphEdgesTo v g))

-- Check whether vertex v1 is a successor of vertex v2 in graph g.
let digraphIsSuccessor = lam v1. lam v2. lam g : Digraph v l.
  let outgoing = mapLookupOrElse (lam. error "Lookup failed") v2 g.adj in
  let successors = map (lam t : (v, l). t.0) outgoing in
  let successors = setOfSeq (digraphCmpv g) successors in
  let res = setMem v1 successors in
  res

-- Add vertex v to graph g if it doesn't already exist in g.
-- If v exists in g and check is true, an error is thrown.
-- If v exist in g and check is false, g stays unchanged.
let digraphAddVertexCheck = lam v. lam g : Digraph v l. lam check.
  if digraphHasVertex v g then
    if check then error "vertex already exists" else g
  else
    {g with adj = mapInsert v [] g.adj}

-- Add a vertex to graph g. Throws an error if v already exists in g.
let digraphAddVertex = lam v. lam g.
  digraphAddVertexCheck v g true

-- Maybe add a vertex v to g. Graph stays unchanged if v already exists in g.
let digraphMaybeAddVertex = lam v. lam g.
  digraphAddVertexCheck v g false

-- Add edge e=(v1,v2,l) to g. Checks invariants iff utests are enabled.
let digraphAddEdge = lam v1. lam v2. lam l. lam g : Digraph v l.
  utest digraphHasVertex v1 g with true in
  utest digraphHasVertex v2 g with true in
  utest
    any (g.eql l) (digraphLabels v1 v2 g)
  with false in

  let oldEdgeList =
    mapLookupOrElse (lam. error "Vertex not found") v1 g.adj
  in
  {g with adj = mapInsert v1 (snoc oldEdgeList (v2, l)) g.adj}

-- Add a list of vertices to a graph g.
let digraphAddVertices = lam vs. lam g.
  foldl (lam g. lam v. digraphAddVertex v g) g vs

-- Add a list of edges to a graph g.
let digraphAddEdges = lam es. lam g.
  foldl (lam g. lam e : DigraphEdge v l. digraphAddEdge e.0 e.1 e.2 g) g es

-- Reverse the direction of graph g.
let digraphReverse = lam g : Digraph v l.
  let edgesReversed = map (lam e : DigraphEdge v l. (e.1, e.0, e.2)) (digraphEdges g) in
  let vs = digraphVertices g in
  digraphAddEdges edgesReversed
    (digraphAddVertices vs (digraphEmpty (digraphCmpv g) g.eql))

-- Remove an edge from the graph g.
let digraphRemoveEdge = lam from. lam to. lam l. lam g : Digraph v l.
  utest (digraphHasEdge (from, to, l) g) with true in
  let outgoing = mapFindExn from g.adj in
  let newOutgoing = filter (lam o : (v, l). not (g.eql l o.1)) outgoing in
  {g with adj = mapInsert from newOutgoing g.adj}

-- Breadth-first search. Marks all reachable vertices from the source with the
-- distance to the source.
let digraphBFS : Digraph v l -> v -> Map v Int = lam source. lam g.
  recursive let work = lam fs. lam level. lam dist : Map v Int.
    if null fs then dist else
    match
      foldl (lam acc : ([v], Map v Int). lam f.
        foldl (lam acc : ([v], Map v Int). lam v.
          if mapMem v acc.1 then acc
          else (cons v acc.0, mapInsert v level acc.1)
        ) acc (digraphSuccessors f g)
      ) ([], dist) fs
    with (ns, dist) then
      work ns (addi level 1) dist
    else never
  in
  work [source] 1 (mapInsert source 0 (mapEmpty (digraphCmpv g)))

type Successors v l = {
  i : Int,
  number : Map v l,
  lowlink : Map v l,
  stack : [v],
  comps : [[v]]
}

-- Strongly connected components of g.
-- From the paper: Depth-First Search and Linear Graph Algorithms, Tarjan 72.
-- https://doi.org/10.1137/0201010
let digraphTarjan : Digraph v l -> [[v]] =
lam g.
  let cmpv = digraphCmpv g in
  let eqv = lam x. lam y. eqi (cmpv x y) 0 in
  let mapFind = mapFindExn in
  let and = lam x. lam y. if not x then false else y in

  recursive let strongConnect = lam s : Successors v l. lam v.
    let traverseSuccessors = lam s : Successors v l. lam w.
      if not (mapMem w s.number) then
        let s : Successors v l = strongConnect s w in
        let n = mini (mapFind v s.lowlink) (mapFind w s.lowlink) in
        {s with lowlink = mapInsert v n s.lowlink}
      else if lti (mapFind w s.number) (mapFind v s.number) then
        if any (eqv w) s.stack then
          let n = mini (mapFind v s.lowlink) (mapFind w s.number) in
          {s with lowlink = mapInsert v n s.lowlink}
        else s
      else s
    in

    let popStackIntoComp = lam s : Successors v l.
      let vn = mapFind v s.number in
      recursive let work = lam comp. lam stack.
        match stack with [] then (comp, stack)
        else match stack with [w] ++ ws then
          if lti (mapFind w s.number) vn then (comp, stack)
          else work (snoc comp w) ws
        else never
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

    let s : Successors v l =
      foldl traverseSuccessors s (digraphSuccessors v g)
    in

    if eqi (mapFind v s.lowlink) (mapFind v s.number)
    then popStackIntoComp s else s
  in

  let s : Successors v l =
    foldl
      (lam s : Successors v l. lam v.
        if not (mapMem v s.number) then strongConnect s v else s)
      {
        i = 0,
        number = mapEmpty cmpv,
        lowlink = mapEmpty cmpv,
        stack = [],
        comps = []
      }
      (digraphVertices g)
  in s.comps

-- Strongly connected components of g.
let digraphStrongConnects = lam g. digraphTarjan g

-- Print as dot format
let digraphPrintDot = lam g. lam v2str. lam l2str.
  print "digraph {";
  (map
    (lam e : DigraphEdge v l.
            print (v2str e.0);
            print " -> ";
            print (v2str e.1);
            print "[label=";
            print (l2str e.2);
            print "];")
    (digraphEdges g));
  print "}\n"; ()

mexpr

let l1 = gensym () in
let l2 = gensym () in
let l3 = gensym () in
let l4 = gensym () in
let l5 = gensym () in

let empty = digraphEmpty subi eqsym in

utest digraphVertices empty with [] using eqSeq eqi in
utest digraphEdges empty with [] using eqSeq eqi in
utest digraphCountVertices empty with 0 in
utest digraphCountEdges empty with 0 in

let g = digraphAddVertex 1 empty in

utest digraphCountVertices g with 1 in
utest digraphVertices g with [1] in
utest digraphEdges g with [] using eqSeq eqi in
utest digraphHasVertex 1 g with true in
utest digraphHasVertex 2 g with false in

let g = digraphAddVertex 3 (digraphAddVertex 2 (digraphAddVertex 1 empty)) in

utest digraphHasVertex 1 g with true in
utest digraphHasVertex 2 g with true in
utest digraphHasVertex 3 g with true in
utest digraphHasVertices [1, 2, 3] g with true in
utest digraphHasVertices [3, 2] g with true in
utest digraphHasVertices [1, 2, 3, 4] g with false in

let g = digraphAddEdge 1 2 l2 (digraphAddEdge 1 2 l1 g) in

utest
  match digraphEdges g with [(1,2,l1),(1,2,l2)] | [(1,2,l2),(1,2,l1)]
  then true else false with true
in
utest digraphHasEdges [(1, 2, l1), (1, 2, l2)] g with true in
utest digraphHasEdges [(1, 2, l2)] g with true in
utest digraphHasEdges [(1, 2, l1)] g with true in

utest digraphSuccessors 1 g with [2] in
utest digraphPredeccessors 1 g with [] using eqSeq eqi in
utest digraphIsSuccessor 2 1 g with true in
utest
  match digraphLabels 1 2 g with [l1,l2] | [l2,l1]
  then true else false with true
in

let g : Digraph v l =
  digraphAddEdges [(2,3,l4),(1,3,l3),(1,2,l2),(1,2,l1)] (digraphAddVertices [1,2,3] empty)
in

utest digraphEdgesBetween 1 3 g with [(1,3,l3)]
using eqSeq (digraphEdgeEq g) in

utest
  match digraphEdgesBetween 1 2 g
  with [(1,2,l2),(1,2,l1)] | [(1,2,l1),(1,2,l2)]
  then true else false with true
in
utest match digraphPredeccessors 3 g with [1,2] | [2,1] then true else false with true in

let g = digraphAddEdges [(1,2,l1),(1,3,l2),(3,1,l3)] (digraphAddVertices [1,2,3] empty) in
let gRev = digraphReverse g in

utest digraphHasEdges [(2,1,l1),(3,1,l2),(1,3,l3)] gRev with true in
utest digraphCountVertices gRev with 3 in
utest digraphCountEdges gRev with 3 in

let g = digraphRemoveEdge 1 3 l2 g in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 2 in
utest digraphHasEdges [(1,2,l1),(3,1,l3)] g with true in

let g = digraphAddEdges [(0,1,l1), (0,2,l2), (2,3,l3), (3,4,l4), (0,4,l5)]
  (digraphAddVertices [0,1,2,3,4] empty) in
utest mapBindings (digraphBFS 0 g) with [(0,0), (1,1), (2,1), (3,2), (4,1)] in

-- Test for strongly connected components of g.
let compsEq = eqsetEqual (eqsetEqual eqi) in

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
