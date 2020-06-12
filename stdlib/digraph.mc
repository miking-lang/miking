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

-- Access vertices and edges
let digraphVertices = lam g. (map (lam tup. tup.0) g.adj)

let digraphEdges = lam g.
    foldl concat []
      (map
        (lam tup.
           let v = tup.0 in
           let edgelist = tup.1 in
           (map (lam tup. (v, tup.0, tup.1)) edgelist))
       g.adj)

let digraphEdgesFrom = lam v. lam g.
                       map (lam tup. (v, tup.0, tup.1)) (mapLookup g.eqv v g.adj)

let digraphLabels = lam v1. lam v2. lam g.
    let from_v1_to_v2 = filter (lam tup. g.eqv tup.1 v2) (digraphEdgesFrom v1 g) in
    map (lam tup. tup.2) from_v1_to_v2

let digraphCountVertices = lam g. length g.adj

let digraphCountEdges = lam g. length (digraphEdges g)

let digraphHasVertex = lam v. lam g. any (g.eqv v) (digraphVertices g)

let digraphHasVertices = lam vs. lam g.
                         all (lam b. b) (map (lam v. digraphHasVertex v g) vs)

-- Edges e1 and e2 equal in graph g.
let digraphEdgeEq = lam g. lam e1. lam e2.
                    and (and (g.eqv e1.0 e2.0)
                             (g.eqv e1.1 e2.1))
                        (g.eql e1.2 e2.2)

-- Graph g contains edges es.
let digraphHasEdges = lam es. lam g.
                      setIsSubsetEq (digraphEdgeEq g) es (digraphEdges g)

let digraphSuccessors = lam v. lam g.
    distinct g.eqv (map (lam tup. tup.1) (digraphEdgesFrom v g))

-- TODO: predecessors

let digraphIsSuccessor = lam v1. lam v2. lam g.
  any (g.eqv v1) (digraphSuccessors v2 g)

-- Add vertices and edges
let digraphAddVertexCheck = lam v. lam g. lam check.
  if digraphHasVertex v g then
    if check then error "vertex already exists" else g
  else
    {adj = snoc g.adj (v,[]), eqv = g.eqv, eql = g.eql}

let digraphAddVertex = lam v. lam g.
  digraphAddVertexCheck v g true

let digraphMaybeAddVertex = lam v. lam g.
  digraphAddVertexCheck v g false

let digraphAddEdgeCheckLabel = lam v1. lam v2. lam l. lam g. lam check.
  if not (digraphHasVertices [v1, v2] g) then
    error "some vertices do not exist"
  else if any (g.eql l) (digraphLabels v1 v2 g) then
    if check then error "label already exists" else g
  else
    {g with adj = mapUpdate g.eqv v1 (lam es. snoc es (v2, l)) g.adj}

let digraphAddEdge = lam v1. lam v2. lam l. lam g.
    digraphAddEdgeCheckLabel v1 v2 l g true

let digraphMaybeAddEdge = lam v1. lam v2. lam l. lam g.
    digraphAddEdgeCheckLabel v1 v2 l g false

-- Union of two graphs
let digraphUnion = lam g1. lam g2.
  let g3 = foldl (lam g. lam v. digraphMaybeAddVertex v g) g1 (digraphVertices g2)
  in foldl (lam g. lam tup. digraphMaybeAddEdge tup.0 tup.1 tup.2 g) g3 (digraphEdges g2)

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

mexpr

-- graph tests
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
let l1 = gensym () in
let l2 = gensym () in
utest digraphEdgesFrom 1 g with [] in
utest digraphLabels 1 2 g with [] in
let g1 = digraphAddEdge 1 2 l2 (digraphAddEdge 1 2 l1 g) in
utest digraphHasEdges [(1, 2, l1), (1, 2, l2)] g1 with true in
utest digraphHasEdges [(1, 2, l2)] g1 with true in
utest digraphHasEdges [(1, 2, l1)] g1 with true in

let g = digraphAddVertex 1 (digraphAddVertex 2 (digraphAddVertex 3 empty)) in
let g1 = (digraphAddEdge 1 2 l2 (digraphAddEdge 1 2 l1 g)) in
utest digraphSuccessors 1 g1 with [2] in
utest digraphIsSuccessor 2 1 g1 with true in
utest any (eqs l1) (digraphLabels 1 2 g1) with true in
utest any (eqs l2) (digraphLabels 1 2 g1) with true in
utest any (eqs l2) (digraphLabels 2 1 g1) with false in

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
