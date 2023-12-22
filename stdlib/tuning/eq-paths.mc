include "common.mc"
include "digraph.mc"
include "string.mc"
include "eqset.mc"

-- Computes equivalence paths for holes.

-- 'eqPaths g endNode depth startNodes' computes representative paths in the
-- call graph 'g' for the equivalence classes used for classifying computation
-- contexts for holes. The paths are suffixes of paths starting in any of the
-- 'startNodes' and end in 'endNode'.
let eqPaths : all v. all l. Digraph v l -> v -> Int -> [v] -> [[(v,v,l)]] =
  lam g. lam endNode. lam depth. lam startNodes.
    -- Reverse graph for forward search (more efficient for adjacency map)
    let gRev = digraphReverse g in
    let eqv = lam v1. lam v2. eqi (digraphCmpv g v1 v2) 0 in

    recursive let traverse : Digraph v l -> v -> [(v,v,l)] -> [v] -> Int -> [[(v,v,l)]] =
      lam g. lam v. lam curPath. lam visited. lam d.
        let fromEdges = digraphEdgesFrom v g in
        if eqi d 0 then [curPath]
        else if null fromEdges then [curPath]
        else if eqsetMem eqv v visited then [curPath]
        else
          let paths =
            map (lam edge : DigraphEdge v l.
                   traverse g edge.1 (cons edge curPath) (cons v visited) (subi d 1))
                fromEdges in
          -- If current node is a start node, the current path is a valid path
          let paths =
            if eqsetMem eqv v startNodes then cons [curPath] paths
            else paths in
          foldl concat [] paths
    in
    let res: [[(v,v,l)]] = traverse gRev endNode [] [] depth in
    map (lam p: [(v,v,l)]. map (lam e: (v, v, l). (e.1, e.0, e.2)) p) res

let eqPathsToLbls : all v. all l. [[DigraphEdge v l]] -> [[l]] = lam paths.
  map (lam p. map (lam e : DigraphEdge v l. e.2) p) paths

mexpr
-- To construct test graphs
let empty = digraphEmpty subi eqChar in
let fromList = lam vs. foldl (lam g. lam v. digraphAddVertex v g) empty vs in
let addEdges : all v. all l. Digraph v l -> [DigraphEdge v l] -> Digraph v l =
  lam g. lam es.
    foldl (lam acc. lam e : DigraphEdge v l. digraphAddEdge e.0 e.1 e.2 acc) g es
in

let eqPaths = lam g. lam endNode. lam depth. lam startNodes.
  eqPathsToLbls (eqPaths g endNode depth startNodes)
in

let digraphPrintDot = lam g. printLn (digraphToDot int2string (lam x. x) g) in

-- Create some labels
let a = 'a' in
let b = 'b' in
let c = 'c' in
let d = 'd' in
let e = 'e' in
let f = 'f' in
let g = 'g' in
let h = 'h' in
let i = 'i' in
let j = 'j' in

let samePaths = lam p1. lam p2.
  eqsetEqual eqString p1 p2 in

-- Graph with one node
-- ┌─────┐
-- │  1  │
-- └─────┘
let g = fromList [1] in
utest eqPaths g 1 0 [] with [""] using eqSeq eqString in
utest eqPaths g 1 1 [] with [""] using eqSeq eqString in
utest eqPaths g 1 2 [] with [""] using eqSeq eqString in

utest eqPaths g 1 0 [1] with [""] using eqSeq eqString in
utest eqPaths g 1 1 [1] with [""] using eqSeq eqString in
utest eqPaths g 1 2 [1] with [""] using eqSeq eqString in

-- Simple chain graph
-- ┌─────┐
-- │  4  │
-- └─────┘
--   │
--   │ c
--   ▼
-- ┌─────┐
-- │  3  │
-- └─────┘
--   │
--   │ b
--   ▼
-- ┌─────┐
-- │  2  │
-- └─────┘
--   │
--   │ a
--   ▼
-- ┌─────┐
-- │  1  │
-- └─────┘
let g = addEdges
        (fromList [1, 2, 3, 4])
        [(4,3,c),
         (3,2,b),
         (2,1,a)]
in
-- let _ = digraphPrintDot g in

let v = 1 in
-- Without specified start nodes
utest eqPaths g v 0 [] with [""] using eqSeq eqString in
utest eqPaths g v 1 [] with ["a"] in
utest eqPaths g v 2 [] with ["ba"] in
utest eqPaths g v 3 [] with ["cba"] in

-- With start nodes
utest eqPaths g v 0 [1,2,3,4] with [""] using eqSeq eqString in
utest samePaths (eqPaths g v 1 [1]) ["","a"] with true in
utest samePaths (eqPaths g v 2 [1]) ["", "ba"] with true in
utest samePaths (eqPaths g v 2 [1,2]) ["", "a", "ba"] with true in
utest samePaths (eqPaths g v 2 [1,2,3]) ["", "a", "ba"] with true in
utest samePaths (eqPaths g v 3 [2,3]) ["a", "ba", "cba"] with true in
utest samePaths (eqPaths g v 3 [1,2,3,4]) ["", "a", "ba", "cba"] with true in

-- Chain with several edges
-- ┌─────┐
-- │  4  │
-- └─────┘
--   │
--   │ c
--   ▼
-- ┌─────┐
-- │  3  │ ─┐
-- └─────┘  │
--   │      │
--   │ d    │ b
--   ▼      │
-- ┌─────┐  │
-- │  2  │ ◀┘
-- └─────┘
--   │
--   │ a
--   ▼
-- ┌─────┐
-- │  1  │
-- └─────┘
let g = addEdges
        (fromList [1, 2, 3, 4])
        [(4,3,c),
         (3,2,b),
         (3,2,d),
         (2,1,a)]
in
-- let _ = digraphPrintDot g in

let v = 1 in
utest eqPaths g v 1 [] with ["a"] in
utest samePaths (eqPaths g v 2 []) ["ba", "da"] with true in
utest samePaths (eqPaths g v 3 []) ["cba", "cda"] with true in

utest samePaths (eqPaths g v 3 [3]) ["ba", "cba", "da", "cda"] with true in

-- Self looping graph
-- ┌───┐   a
-- │   │ ─────┐
-- │ 1 │      │
-- │   │ ◀────┘
-- └───┘
let g0 = addEdges
         (fromList [1])
         [(1,1,a)] in
-- let _ = digraphPrintDot g0 in

utest eqPaths g0 1 0 [] with [""] using eqSeq eqString in
utest eqPaths g0 1 0 [1] with [""] using eqSeq eqString in
utest samePaths (eqPaths g0 1 1 [1]) ["", "a"] with true in

-- Loop with two nodes (mutual recursion)
-- ┌─────┐
-- │  2  │ ◀┐
-- └─────┘  │
--   │      │
--   │ a    │ b
--   ▼      │
-- ┌─────┐  │
-- │  1  │ ─┘
-- └─────┘
let g = addEdges
        (fromList [1, 2])
        [(1,2,'b'),(2,1,'a')] in
-- let _ = digraphPrintDot g in

utest eqPaths g 1 0 [1,2] with [""] using eqSeq eqString in
utest samePaths (eqPaths g 1 1 [1]) ["", "a"] with true in
utest samePaths (eqPaths g 1 2 [1]) ["", "ba"] with true in
utest samePaths (eqPaths g 1 2 [1,2]) ["", "a", "ba"] with true in

-- Mutual recursion again
-- ┌─────┐
-- │  1  │
-- └─────┘
--   │
--   │ a
--   ▼
-- ┌─────┐
-- │  2  │ ◀┐
-- └─────┘  │
--   │      │
--   │ b    │ c
--   ▼      │
-- ┌─────┐  │
-- │  3  │ ─┘
-- └─────┘
let g = addEdges
        (fromList [1, 2, 3])
        [(1,2,a), (3,2,c),(2,3,b)] in
-- let _ = digraphPrintDot g in

utest eqPaths g 2 0 [1,2,3] with [""] using eqSeq eqString in
utest samePaths (eqPaths g 2 1 [1,2,3]) ["", "a", "c"] with true in
utest samePaths (eqPaths g 2 2 [1,2,3]) ["", "a", "c", "bc"] with true in
utest samePaths (eqPaths g 2 1000000000 [1,2,3]) ["", "a", "c", "bc"] with true in

-- Yet another mutual recursion
--      ┌─────┐
-- ┌──▶ │  3  │
-- │    └─────┘
-- │      │
-- │      │ b
-- │      ▼
-- │    ┌─────┐
-- │  c │  2  │ ◀┐
-- │    └─────┘  │
-- │      │      │
-- │      │  a   │ d
-- │      ▼      │
-- │    ┌─────┐  │
-- └─── │  1  │ ─┘
--      └─────┘
let g = addEdges
        (fromList [1, 2, 3])
        [(2,1,a), (3,2,b), (1,3,c), (1,2,d)] in
-- let _ = digraphPrintDot g in

utest samePaths (eqPaths g 2 3 [1,2,3]) ["","d","ad","b","cb","acb"] with true in

-- Loop with three nodes
-- ┌─────┐
-- │  3  │ ◀┐
-- └─────┘  │
--   │      │
--   │ c    │
--   ▼      │
-- ┌─────┐  │
-- │  1  │  │ b
-- └─────┘  │
--   │      │
--   │ a    │
--   ▼      │
-- ┌─────┐  │
-- │  2  │ ─┘
-- └─────┘
let g = addEdges
        (fromList [1, 2, 3])
        [(1,2,a),(2,3,b),(3,1,c)] in
-- let _ = digraphPrintDot g in

utest samePaths (eqPaths g 2 3 [3]) ["ca","bca"] with true in

-- Two way loop
-- ┌─────┐
-- │  4  │ ◀┐
-- └─────┘  │
--   │      │
--   │ e    │ d
--   ▼      │
-- ┌───────────────────┐
-- │         2         │
-- └───────────────────┘
--   │      ▲      │
--   │ a    │ c    │ b
--   ▼      │      ▼
-- ┌─────┐  │    ┌─────┐
-- │  1  │  └─── │  3  │
-- └─────┘       └─────┘
let g = addEdges
        (fromList [1,2,3,4])
        [(2,3,b),(3,2,c),(2,4,d),(4,2,e),(2,1,a)] in
-- let _ = digraphPrintDot g in

utest samePaths (eqPaths g 1 10 [2]) ["a", "bca", "dea"] with true in
utest samePaths (eqPaths g 1 10 [4]) ["bca", "ea", "dea"] with true in

-- Chain with loops
-- ┌─────┐   c
-- │     │ ─────┐
-- │  3  │      │
-- │     │ ◀────┘
-- └─────┘
--   │
--   │ a
--   ▼
-- ┌─────┐   b
-- │     │ ─────┐
-- │  2  │      │
-- │     │ ◀────┘
-- └─────┘
--   │
--   │ d
--   ▼
-- ┌─────┐
-- │  1  │
-- └─────┘
let g = addEdges
        (fromList [1,2,3])
        [(3,3,c),(2,2,b),(3,2,a),(2,1,d)] in
-- let _ = digraphPrintDot g in

utest samePaths (eqPaths g 1 3 [3]) ["bd", "ad", "cad"] with true in

()
