include "option.mc"
include "seq.mc"

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

-- Map functions
let mapLookup = lam key. lam eq. lam m.
                match findAssoc (eq key) m with Some e
                then e
                else error "Element not found"

recursive
let mapUpdate = lam key. lam f. lam eq. lam m.
                let k = (head m).0 in
                let v = (head m).1 in
                if eq key k then
                  cons (k, f v) (tail m)
                else
                  cons (head m) (mapUpdate key f eq (tail m))
end

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
                       map (lam tup. (v, tup.0, tup.1)) (mapLookup v g.eqv g.adj)

let digraphLabels = lam v1. lam v2. lam g.
    let from_v1_to_v2 = filter (lam tup. g.eqv tup.1 v2) (digraphEdgesFrom v1 g) in
    map (lam tup. tup.2) from_v1_to_v2

let digraphCountVertices = lam g. length g.adj

let digraphCountEdges = lam g. length (digraphEdges g)

let digraphHasVertex = lam v. lam g. any (g.eqv v) (digraphVertices g)

let digraphHasVertices = lam vs. lam g.
                         all (lam b. b) (map (lam v. digraphHasVertex v g) vs)

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
    {adj = cons (v,[]) g.adj, eqv = g.eqv, eql = g.eql}

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
    {g with adj = mapUpdate v1 (cons (v2, l)) g.eqv g.adj}

let digraphAddEdge = lam v1. lam v2. lam l. lam g.
    digraphAddEdgeCheckLabel v1 v2 l g true

let digraphMaybeAddEdge = lam v1. lam v2. lam l. lam g.
    digraphAddEdgeCheckLabel v1 v2 l g false

-- Union of two graphs
let digraphUnion = lam g1. lam g2.
  let g3 = foldl (lam g. lam v. digraphMaybeAddVertex v g) g1 (digraphVertices g2)
  in foldl (lam g. lam tup. digraphMaybeAddEdge tup.0 tup.1 tup.2 g) g3 (digraphEdges g2)


mexpr
-- map tests
let m = [(1,3), (4,6)] in
utest mapLookup 1 eqi m with 3 in
utest mapUpdate 4 (addi 1) eqi m with [(1,3), (4,7)] in

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
let label = gensym () in
utest digraphEdgesFrom 1 g with [] in
utest digraphLabels 1 2 g with [] in
let g1 = digraphAddEdge 1 2 label g in
utest digraphEdges (digraphAddEdge 1 2 label g) with [(1, 2, label)] in

let l1 = gensym () in
let l2 = gensym () in
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

()
