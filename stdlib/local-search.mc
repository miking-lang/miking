include "digraph.mc"
include "string.mc"

type Assignment = [a]
type Cost = Int
type Solution = (Assignment, Cost)
type SearchState = {cur : Solution, inc : Solution, iter : Int, appendix : Record}

type StepF = (SearchState -> [Assignment]) -> ([Assignment] -> Assignment) -> (Assignment -> Cost)

-- TODO: Satisfiability of best found solution
-- TODO: Where to compute cost function
-- TODO: Combine tabu search and SA

--  'initAssign ()' returns the initial assignment of the variables
--  'step' is the step function
--  'stop' is the stop condition
let lsMinimize : (Unit -> Assignment) -> StepF -> (Unit -> Bool) -> (SearchState -> Unit) -> Record -> SearchState =
  lam initAssign. lam step. lam terminate. lam extra. lam stateAppend.
    let init = initAssign () in
    let state = {cur = init, inc = init, iter = 0, appendix = stateAppend} in
    recursive let search = lam state.
      if not (terminate state) then
        let state = {state with iter=addi state.iter 1} in
        let state = step state in
        -- Improving solution?
        let incumbent =
          if leqi state.cur.1 state.inc.1 then state.cur else state.inc in
        let _ = extra state in
        search state
      else
        state
    in search state

-- A generic step function for local search
--  'neighbours s' returns the neighbours of solution 's'
--  'legal ns s' returns the legal neighbours in 'ns' w.r.t. 's'
--  'select sols s' returns a selected element of 'sols' w.r.t. 's'
--  'cost s' returns the cost of a solution s, to be minimized
--  'state' current state. 'state.cur'
let lsStep =
  lam neighbours. lam select. lam cost. lam state.
    let ns = neighbours state in
    let newCur = select (neighbours state) cost state in
    {state with cur=newCur}


-- Simulated annealing


mexpr

-- Example: Travelling Salesman Problem (TSP)
-- Given a weighted undirected graph, find a tour (Hamiltonian circuit) that
-- visits each node exactly once, with minimum path weight.

-- Define instance data
let vs = ["Uppsala", "Stockholm", "Kiruna", "Gothenburg"] in
let es = [("Uppsala", "Stockholm", 80), ("Stockholm", "Uppsala", 90),
          ("Uppsala", "Gothenburg", 200), ("Gothenburg", "Uppsala", 250),
          ("Uppsala", "Kiruna", 10), ("Kiruna", "Uppsala", 320),
          ("Kiruna", "Stockholm", 500), ("Stockholm", "Kiruna", 20),
          ("Stockholm", "Gothenburg", 40), ("Gothenburg", "Stockholm", 65),
          ("Kiruna", "Gothenburg", 111), ("Gothenburg", "Kiruna", 321)] in

let g = digraphAddEdges es (digraphAddVertices vs (digraphEmpty eqstr eqi)) in

-- Check solution
let isHamiltonianCircuit = lam g. lam path. true in

-- Define initial assignment, cost, select and legal functions
let initTour = [("Uppsala", "Kiruna", 10),
                ("Kiruna", "Stockholm", 500),
                ("Stockholm", "Gothenburg", 40),
                ("Gothenburg", "Uppsala", 250)] in

let cost = lam s.
  foldl (lam sum. lam edge. addi sum edge.2) 0 s in

let init = lam _. (initTour, cost initTour) in

-- Neighbourhood: replace 2 edges by two others s.t. still a tour
let neighbours = lam state.
  -- TODO: initial state
  let g = state.appendix.g in
  let tour = state.cur.0 in

  let tourHasEdge = lam v1. lam v2.
    any (lam e. or (and (eqstr v1 e.0) (eqstr v2 e.1))
                   (and (eqstr v1 e.1) (eqstr v2 e.0))) tour in

  -- Find replacing edges for 'e12' and 'e34'
  let exchange = lam e12. lam e34.
    let v1 = e12.0 in
    let v2 = e12.1 in
    let v3 = e34.0 in
    let v4 = e34.1 in

    let v1v3 = digraphEdgesBetween v1 v3 g in
    let v2v4 = digraphEdgesBetween v2 v4 g in

    let res =
      match (v1v3, v2v4) with ([],_) | (_,[]) then None () else
      match (v1v3, v2v4) with ([e13], [e24]) then
        if not (tourHasEdge v1 v3) then Some (e12, e34, e13, e24)
        else None ()
      else
        let _ = dprint (v1v3, v2v4) in
      error "Expected at most one edge between any two nodes"
    in
    res
  in

  let neighbourFromExchange = lam oldEdgs. lam newEdgs. lam tour.
    let equal = digraphEdgeEq g in
    setUnion equal newEdgs (setDiff equal tour oldEdgs)
  in

  let possibleExchanges =
    foldl (lam outerAcc. lam e1.
           concat outerAcc
           (foldl (lam innerAcc. lam e2.
                     let e = exchange e1 e2 in
                     match e with Some r then cons r innerAcc else innerAcc)
                  []
            tour))
          []
          tour
   in map (lam ex. neighbourFromExchange [ex.0,ex.1] [ex.2,ex.3] tour) possibleExchanges
in

-- Select a random best neighbour
let randomBest = lam neighs. lam costF. lam _.
  let costs = map costF neighs in
  let minCost = min subi costs in
  let neighCosts = zipWith (lam n. lam c. (n,c)) neighs costs in
  let minNeighs = filter (lam t. eqi t.1 minCost) neighCosts in
  let randIdx = randIntU 0 (length minNeighs) in
  get minNeighs randIdx

in

let stepF = lsStep neighbours randomBest cost in

let res = lsMinimize init stepF (lam state. eqi state.iter 10) (lam state. print "iter\n") {g=g} in

dprint res.inc


