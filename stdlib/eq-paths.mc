include "digraph.mc"
include "string.mc"

-- This file implements eqPaths: computing equivalence paths for decision
-- points.

-- Input: a graph, a start node v and a depth d
-- Output: the set of equivalence paths ending in v. The lengths of the
-- paths are at most d.

-- It's really a graph algorithm, but very specific, and the test cases
-- takes lots of space, so it's currently in a separate file from digraph.mc.

-- TODO: prove true/false: an eq. path is never a sub-path of another eq-path


-- Complexity: O(V+E), as we explore each node and its neighbours at most
-- once (compare to DFS). This assumes digraphEdgesTo, isVisited and concat are
-- constant operations.
let eqPaths = lam g. lam v. lam d.
  let isVisited = lam eq. lam path. lam v.
    optionIsSome (find (eq v) path) in

  let isSelfLoop = lam eq. lam e. eq e.0 e.1 in

  recursive let traverse = lam v. lam path. lam visited. lam d.
    let toEdges = digraphEdgesTo v g in
    let nonSelfLoops = filter (lam e. not (isSelfLoop g.eqv e)) toEdges in

    if isVisited g.eqv visited v then
        [tail path]
    -- Dead end: depth is 0, or no incoming edges except self loops
    else if or (eqi d 0) (null nonSelfLoops) then
      [path]
    else
      -- Recursively compute paths for all predecessors
      let paths = map (lam edge.
                         traverse edge.0 (cons edge.2 path) (cons v visited) (subi d 1))
                       nonSelfLoops in
      -- Return the union of the paths
      foldl concat [] paths
  in
  traverse v [] [] d

mexpr
-- To construct test graphs
let empty = digraphEmpty eqi eqstr in
let fromList = lam vs. foldl (lam g. lam v. digraphAddVertex v g) empty vs in
let addEdges = lam g. lam es. foldl (lam acc. lam e. digraphAddEdge e.0 e.1 e.2 acc) g es in

-- To compare paths
recursive let eqpath = lam eq. lam p1. lam p2.
  match (p1, p2) with ([], []) then true else
  match (p1, p2) with ([], _) | (_, []) then false
  else and (eq (head p1) (head p2)) (eqpath eq (tail p1) (tail p2))
in

-- To compare edges
let eqedge = lam e1. lam e2.
  eqstr e1 e2
in

let samePaths = lam eq. lam seq1. lam seq2.
  and
    -- equal number of paths
    (eqi (length seq1) (length seq2))
    -- each path in seq1 exists in seq2
    (all (lam p. optionIsSome (find (eqpath eq p) seq2)) seq1)
in

-- Create some labels
let l1 = "l1" in
let l2 = "l2" in
let l3 = "l3" in
let l4 = "l4" in
let l5 = "l5" in
let l6 = "l6" in
let l7 = "l7" in
let l8 = "l8" in
let l9 = "l9" in
let l10 = "l10" in

-- Simple chain graph
-- ┌─────┐
-- │  4  │
-- └─────┘
--   │
--   │ l3
--   ▼
-- ┌─────┐
-- │  3  │
-- └─────┘
--   │
--   │ l2
--   ▼
-- ┌─────┐
-- │  2  │
-- └─────┘
--   │
--   │ l1
--   ▼
-- ┌─────┐
-- │  1  │
-- └─────┘
let g = addEdges
        (fromList [1, 2, 3, 4])
        [(4,3,l3),
         (3,2,l2),
         (2,1,l1)]
in
let _ = digraphPrintDot g int2string (lam x. x) in

let v = 1 in
utest eqPaths g v 0 with [[]] in
utest eqPaths g v 1 with [[l1]] in
utest eqPaths g v 2 with [[l2, l1]] in
utest eqPaths g v 3 with [[l3, l2, l1]] in
utest eqPaths g v 4 with [[l3, l2, l1]] in

-- Chain with several edges
-- ┌─────┐
-- │  4  │
-- └─────┘
--   │
--   │ l3
--   ▼
-- ┌─────┐
-- │  3  │ ─┐
-- └─────┘  │
--   │      │
--   │ l4   │ l2
--   ▼      │
-- ┌─────┐  │
-- │  2  │ ◀┘
-- └─────┘
--   │
--   │ l1
--   ▼
-- ┌─────┐
-- │  1  │
-- └─────┘
let g = addEdges
        (fromList [1, 2, 3, 4])
        [(4,3,l3),
         (3,2,l2),
         (3,2,l4),
         (2,1,l1)]
in
let _ = digraphPrintDot g int2string (lam x. x) in

let v = 1 in
utest eqPaths g v 0 with [[]] in
utest eqPaths g v 1 with [[l1]] in
utest samePaths eqedge (eqPaths g v 2)
                       ([[l2, l1],
                         [l4, l1]]) with true in
utest samePaths eqedge (eqPaths g v 3)
                          ([[l3, l2, l1],
                            [l3, l4, l1]]) with true in

-- Self looping graph
-- ┌───┐   l1
-- │   │ ─────┐
-- │ 1 │      │
-- │   │ ◀────┘
-- └───┘
let g0 = addEdges
         (fromList [1])
         [(1,1,l1)] in
let _ = digraphPrintDot g0 int2string (lam x. x) in

-- Path should always be empty
utest eqPaths g0 1 0  with [[]] in
utest eqPaths g0 1 10 with [[]] in

-- Loop with two nodes (mutual recursion)
-- ┌─────┐
-- │  2  │ ◀┐
-- └─────┘  │
--   │      │
--   │ 21   │ 12
--   ▼      │
-- ┌─────┐  │
-- │  1  │ ─┘
-- └─────┘
let g = addEdges
        (fromList [1, 2])
        [(1,2,"12"),(2,1,"21")] in
let _ = digraphPrintDot g int2string (lam x. x) in

utest eqPaths g 1 0 with [[]] in
utest eqPaths g 1 1 with [["21"]] in
utest eqPaths g 1 2 with [["21"]] in
utest eqPaths g 1 3 with [["21"]] in
utest eqPaths g 1 10 with [["21"]] in

-- Mutual recursion again
-- ┌─────┐
-- │  1  │
-- └─────┘
--   │
--   │ l1
--   ▼
-- ┌─────┐
-- │  2  │ ◀┐
-- └─────┘  │
--   │      │
--   │ l2   │ l3
--   ▼      │
-- ┌─────┐  │
-- │  3  │ ─┘
-- └─────┘
let g = addEdges
        (fromList [1, 2, 3])
        [(1,2,l1), (3,2,l3),(2,3,l2)] in
let _ = digraphPrintDot g int2string (lam x. x) in

utest eqPaths g 2 0 with [[]] in
utest samePaths eqedge (eqPaths g 2 1) [[l1],[l3]] with true in
utest samePaths eqedge (eqPaths g 2 2) [[l1],[l3]] with true in

-- Yet another mutual recursion
--      ┌─────┐
-- ┌──▶ │  3  │
-- │    └─────┘
-- │      │
-- │      │ l2
-- │      ▼
-- │    ┌─────┐
-- │ l3 │  2  │ ◀┐
-- │    └─────┘  │
-- │      │      │
-- │      │ l1   │ l4
-- │      ▼      │
-- │    ┌─────┐  │
-- └─── │  1  │ ─┘
--      └─────┘
let g = addEdges
        (fromList [1, 2, 3])
        [(2,1,l1), (3,2,l2), (1,3,l3), (1,2,l4)] in
let _ = digraphPrintDot g int2string (lam x. x) in

utest eqPaths g 1 0 with [[]] in
utest eqPaths g 1 1 with [[l1]] in
utest samePaths eqedge (eqPaths g 1 2) [[l2, l1], [l1]] with true in
utest samePaths eqedge (eqPaths g 1 3) [[l2, l1], [l1]] with true in


-- Loop with three nodes
-- ┌─────┐
-- │  3  │ ◀┐
-- └─────┘  │
--   │      │
--   │ l3   │
--   ▼      │
-- ┌─────┐  │
-- │  1  │  │ l2
-- └─────┘  │
--   │      │
--   │ l1   │
--   ▼      │
-- ┌─────┐  │
-- │  2  │ ─┘
-- └─────┘
let g = addEdges
        (fromList [1, 2, 3])
        [(1,2,l1),(2,3,l2),(3,1,l3)] in
let _ = digraphPrintDot g int2string (lam x. x) in

utest eqPaths g 1 1 with [[l3]] in
utest eqPaths g 1 2 with [[l2, l3]] in

-- Two way loop
-- ┌─────┐
-- │  4  │ ◀┐
-- └─────┘  │
--   │      │
--   │ l5   │ l4
--   ▼      │
-- ┌───────────────────┐
-- │         2         │
-- └───────────────────┘
--   │      ▲      │
--   │ l1   │ l3   │ l2
--   ▼      │      ▼
-- ┌─────┐  │    ┌─────┐
-- │  1  │  └─── │  3  │
-- └─────┘       └─────┘
let g = addEdges
        (fromList [1,2,3,4])
        [(2,3,l2),(3,2,l3),(2,4,l4),(4,2,l5),(2,1,l1)] in
let _ = digraphPrintDot g int2string (lam x. x) in

utest eqPaths g 1 1 with [[l1]] in
utest samePaths eqedge (eqPaths g 1 2)
                       ([[l5, l1],
                         [l3, l1]]) with true in
-- d=3 same result as d=2
utest eqPaths g 1 3 with eqPaths g 1 2 in



-- Chain with loops
-- ┌─────┐   l3
-- │     │ ─────┐
-- │  3  │      │
-- │     │ ◀────┘
-- └─────┘
--   │
--   │ l1
--   ▼
-- ┌─────┐   l2
-- │     │ ─────┐
-- │  2  │      │
-- │     │ ◀────┘
-- └─────┘
--   │
--   │ l4
--   ▼
-- ┌─────┐
-- │  1  │
-- └─────┘
let g = addEdges
        (fromList [1,2,3])
        [(3,3,l3),(2,2,l2),(3,2,l1),(2,1,l4)] in
let _ = digraphPrintDot g int2string (lam x. x) in

utest eqPaths g 1 2 with [[l1, l4]] in
utest eqPaths g 1 3 with [[l1, l4]] in

-- Long cycle
--             ┌─────┐
--             │  1  │
--             └─────┘
--               │
--               │ l1
--               ▼
-- ┌───┐  l8   ┌───────────────────┐
-- │ 7 │ ◀──── │         3         │
-- └───┘       └───────────────────┘
--               │      ▲      ▲
--               │ l4   │ l7   │ l2
--               ▼      │      │
--             ┌─────┐  │    ┌─────┐
--             │  4  │  │    │  2  │
--             └─────┘  │    └─────┘
--               │      │
--               │ l5   │
--               ▼      │
--             ┌─────┐  │
--             │  5  │  │
--             └─────┘  │
--               │      │
--               │ l6   │
--               ▼      │
--             ┌─────┐  │
--             │  6  │ ─┘
--             └─────┘
let g = addEdges
        (fromList [1,2,3,4,5,6,7])
        [(1,3,l1), (2,3,l2), (3,4,l4), (4,5,l5), (5,6,l6), (6,3,l7), (3,7,l8)] in
let _ = digraphPrintDot g int2string (lam x. x) in

utest samePaths eqedge (eqPaths g 7 2) [[l7, l8], [l2, l8], [l1, l8]] with true in
utest samePaths eqedge (eqPaths g 7 10) [[l5, l6, l7, l8], [l2, l8], [l1, l8]] with true in

()
