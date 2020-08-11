include "digraph.mc"
include "string.mc"
include "dfa.mc"
include "regex.mc"

-- This file implements eqPaths: computing equivalence paths for decision
-- points.

-- Expand the regular expression as far as possible, at most to length d
-- Kleene closures are walked at most once
-- TODO: Set #laps in Kleene closures as a parameter
let regExpand: (a -> a -> bool) -> RegEx -> Int -> [[a]] =
  lam eqsym. lam r. lam d.
  -- Marker for finished expansion
  con ExpandEnd in
  -- Check if path is marked as finished
  let isFinished = lam path.
    match path with h ++ [ExpandEnd ()] then true
    else false
  in
  -- Actual expansion
  recursive let expand: RegEx -> Int -> [a] -> [[a]] =
    lam r. lam d. lam cur. lam acc.
      match isFinished cur with true then cons cur acc else
      match d with 0 then cons cur acc else
      match r with Empty () then acc else
      match r with Epsilon () then cons cur acc else
      match r with Symbol s then cons (snoc cur s) acc else
      match r with Concat (r1, r2) then
        let left = expand r1 d [] [] in
        foldl (lam a. lam l.
                 let len = length l in
                 let newCur = concat cur l in
                 expand r2 (subi d len) newCur a)
              acc left
      else
      match r with Union (r1, r2) then
        let left = expand r1 d cur acc in
        expand r2 d cur left
      else
      -- Ignore self loops
      match r with Kleene (Symbol s) then
        cons cur acc
      else
      -- Walk the loop 0 or 1 times
      match r with Kleene w then
        let zeroLaps = cur in
        let oneLap = expand w d cur acc in
        -- Mark one-laps with a end marker
        let oneLap = map (lam x. snoc x (ExpandEnd ())) oneLap in
        cons zeroLaps oneLap
      else error "Unknown RegEx in expand"
    in
  let expansion = expand r d [] [] in
  -- Remove trailing end markers
  recursive let trim = lam path.
    match path with (h ++ [ExpandEnd ()]) then trim h else path
  in
  let trimmedPaths = map trim expansion in
  -- Equality function for paths
  let eq = lam p1. lam p2.
    and (eqi (length p1) (length p2))
        (all (lam t. eqsym t.0 t.1) (zipWith (lam e1. lam e2. (e1, e2)) p1 p2)) in
  -- Remove duplicate paths
  let upaths = distinct eq trimmedPaths in
  upaths

let regExpandChar = regExpand eqchar
utest regExpandChar (Empty ()) 1 with []
utest regExpandChar (Epsilon ()) 1 with [[]]
utest regExpandChar (Symbol 'a') 1 with [['a']]

utest regExpandChar (Concat (Symbol 'a', Symbol 'b')) 2 with [['a', 'b']]
utest regExpandChar (Concat (Symbol 'a', Symbol 'b')) 1 with [['a']]

utest regExpandChar (Concat (Symbol 'a', Concat (Symbol 'b', Symbol 'c'))) 1 with [['a']]
utest regExpandChar (Concat (Symbol 'a', Concat (Symbol 'b', Symbol 'c'))) 2 with [['a','b']]
utest regExpandChar (Concat (Concat (Symbol 'a', Symbol 'b'), Symbol 'c')) 2 with [['a','b']]
utest regExpandChar (Concat (Concat (Symbol 'a', Symbol 'b'), Symbol 'c')) 3 with [['a','b','c']]

utest regExpandChar (Kleene (Symbol 'a')) 1 with [[]]
utest regExpandChar (Concat (Kleene (Symbol 'a'), Symbol 'b')) 1 with [['b']]
utest regExpandChar (Concat (Kleene (Symbol 'a'), Symbol 'b')) 2 with [['b']]
utest regExpandChar (Kleene (Concat (Symbol 'a', Symbol 'b'))) 5 with [[], ['a','b']]
utest regExpandChar (Concat (Kleene (Concat (Symbol 'a', Symbol 'b')), Symbol 'c')) 3 with [['a','b'], ['c']]
utest regExpandChar (Concat (Kleene (Concat (Symbol 'a', Symbol 'b')), Symbol 'c')) 2 with [['a','b'], ['c']]

-- Input: a graph, a start node v, depth d and start nodes.
-- Output: the set of equivalence paths ending in v. The lengths of the
-- paths are at most d.
let eqPaths = lam g. lam v. lam d. lam sStates.
  -- Compute a reversed regular expression from the call graph
  let callGraph2RegEx = lam g. lam sStates. lam aState.
    let gRev = digraphReverse g in
    let dfa = dfaFromDigraph gRev aState sStates in
    regexFromDFA dfa
  in
  let re = callGraph2RegEx g sStates v in
  -- Expand regex into paths
  let paths = regExpand (digraphEql g) re d in
  -- Define equality function for paths
  let eq = lam p1. lam p2.
             and (eqi (length p1) (length p2))
                 (all (lam t. (digraphEql g) t.0 t.1) (zipWith (lam e1. lam e2. (e1, e2)) p1 p2)) in
  -- Remove duplicate paths
  let upaths = distinct eq paths in
  -- Reverse paths, making v the end node
  map (lam p. reverse p) upaths

mexpr
-- To construct test graphs
let empty = digraphEmpty eqi eqchar in
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
  eqchar e1 e2
in

let samePaths = lam eq. lam seq1. lam seq2.
  and
    -- equal number of paths
    (eqi (length seq1) (length seq2))
    -- each path in seq1 exists in seq2
    (all (lam p. optionIsSome (find (eqpath eq p) seq2)) seq1)
in

let eq = samePaths eqedge in

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
-- let _ = digraphPrintDot g int2string (lam x. x) in

let v = 1 in
utest eqPaths g v 2 [] with [] in
utest eqPaths g v 2 [4] with [[b, a]] in
utest eqPaths g v 4 [4] with [[c, b, a]] in
utest eqPaths g v 4 [3,4] with [[c, b, a], [b,a]] in
utest eq (eqPaths g v 4 [1,2,3,4]) [[c, b, a], [b,a], [a], []] with true in


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
--   │ d   │ b
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
-- let _ = digraphPrintDot g int2string (lam x. x) in

let v = 1 in
utest eq (eqPaths g v 3 [1,2,3,4]) ([[c,d,a],[c,b,a],[d,a],[b,a],[a],[]]) with true in
utest eq (eqPaths g v 2 [1,2,3,4]) ([[d,a],[b,a],[a],[]]) with true in

-- Self looping graph
-- ┌───┐   a
-- │   │ ─────┐
-- │ 1 │      │
-- │   │ ◀────┘
-- └───┘
let g0 = addEdges
         (fromList [1])
         [(1,1,a)] in
-- let _ = digraphPrintDot g0 int2string (lam x. x) in

-- Path should always be empty
utest eqPaths g0 1 0 [1] with [[]] in
utest eqPaths g0 1 1 [1] with [[]] in
utest eqPaths g0 1 10 [1] with [[]] in

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
-- let _ = digraphPrintDot g int2string (lam x. x) in

utest eqPaths g 1 0 [2] with [[]] in
utest eqPaths g 1 1 [2] with [['a']] in
-- Questionable result: Includes a loop
utest eqPaths g 1 2 [2] with [['b','a'],['a']] in
utest eqPaths g 1 2 [1,2] with [['b','a'],['a'],[]] in

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
-- let _ = digraphPrintDot g int2string (lam x. x) in

utest eqPaths g 2 0 [1,2,3] with [[]] in
-- Questionable result: cuts off at the mutual recursion
utest eqPaths g 2 3 [1] with [[b,c], [a]] in
utest eqPaths g 2 3 [3] with [[b,c], [c]] in
utest eq (eqPaths g 2 3 [1,2,3]) [[b,c], [a], [], [c]] with true in

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
-- let _ = digraphPrintDot g int2string (lam x. x) in

utest eqPaths g 1 1 [1] with [[],[a]] in
utest eqPaths g 1 5 [3] with [[d,a], [c, b, a], [b,a]] in

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
-- let _ = digraphPrintDot g int2string (lam x. x) in

utest eqPaths g 2 3 [3] with [[b,c,a],[c,a]] in

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
-- let _ = digraphPrintDot g int2string (lam x. x) in

utest eqPaths g 1 10 [2] with [[a], [d,e,a], [b,c,a]] in
utest eqPaths g 1 1 [4] with [[a]] in
utest eqPaths g 1 2 [4] with [[e,a], [c,a]] in
utest eqPaths g 1 3 [4] with [[e,a], [d,e,a], [b,c,a]] in

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
-- let _ = digraphPrintDot g int2string (lam x. x) in

utest eqPaths g 1 3 [3] with [[a,d]] in
utest eqPaths g 1 3 [2,3] with [[a,d],[d]] in
utest eqPaths g 1 3 [1,2,3] with [[a,d],[d],[]] in

()
