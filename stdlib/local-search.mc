include "set.mc"
include "digraph.mc"
include "string.mc"

type Assignment = [v]
-- TODO: support other types than int
type Cost = Int
type Solution = (Assignment, Cost)

type NeighbourhoodFun = SearchState -> [Assignment]
type SearchState = {cur : Solution, inc : Solution, iter : Int, stuck : Bool}

type MetaHeuristic
con Base               : {select : ([Assignment] -> SearchState -> AssignmentOption)} -> MetaHeuristic
con SimulatedAnnealing : {select : ([Assignment] -> SearchState -> AssignmentOption),
                          temp : Float,
                          decayFun : Float -> SearchState -> Float}                   -> MetaHeuristic
con TabuSearch         : {select : ([Assignment] -> SearchState -> AssignmentOption),
                          tabuConvert : Assignment -> t,
                          tabu : [t],
                          isTabu : t -> [t] -> Bool,
                          tabuAdd : t -> [t] -> [t]}                                  -> MetaHeuristic

-- Internal definitions
recursive
  let _search = lam meta. lam terminate. lam callAfterEachIter. lam nextSol. lam state.
    if not (terminate state) then
      let state = {state with iter=addi state.iter 1} in
      let next = nextSol state meta in
      let newCur = next.0 in
      match newCur with None () then
        ({state with stuck = true}, meta)
      else
        let meta = next.1 in
        let cur = optionGetOrElse (lam _. error "Expected a solution") newCur in
        -- New best solution?
        let inc = if leqi cur.1 state.inc.1 then cur else state.inc in
        let state = {{state with cur = cur} with inc = inc} in
        let _ = callAfterEachIter state in
        _search meta terminate callAfterEachIter nextSol state
    else
      (state, meta)
end

-- External definitions
let initSearchState : (Unit -> Solution) -> SearchState = lam initAssign.
  let init = initAssign () in
  {cur = init,
   inc = init,
   iter = 0,
   stuck = false}

let minimize : MetaHeuristic -> (SearchState -> Bool) -> (SearchState -> Unit) ->
               NieghbourhoodFun -> SearchState -> (SearchState, MetaHeuristic) =
  lam terminate. lam callAfterEachIter. lam neighbourhood. lam state. lam meta.

    match meta with Base r then
      let nextSol = lam state. lam meta.
        (r.select (neighbourhood state) state, meta)
      in _search meta terminate callAfterEachIter nextSol state else

    match meta with SimulatedAnnealing r then
      -- Compute exponential of x
      -- TODO: Refactor into a proper implementation of exponential function
      let exp = lam x.
        addf x 1. in
      let nextSol = lam state. lam meta.
        let proposal = r.select (neighbourhood state) state in
        match proposal with None () then (None (), meta) else
        -- Accept proposal according to Metropolis condition
        if leqi proposal.1 state.cur.1 then
          (Some proposal, meta)
        else
          match meta with SimulatedAnnealing r then
            let pAccept = exp (divf (int2float (subi proposal.1 state.cur.1)) r.temp) in
            let rnd = int2float (randIntU 0 100) in
            let choice = if geqf (mulf pAccept 100.0) rnd then proposal else state.cur in
            (Some choice, SimulatedAnnealing {r with temp=r.decayFunc r.temp state})
          else
            error "Expected SimulatedAnnealing as meta heuristics"
        in _search meta terminate callAfterEachIter nextSol state else

      match meta with TabuSearch r then
        let nextSol = lam state. lam meta.
          let ns = neighbourhood state in
          let nonTabus = filter (lam n. not (r.isTabu n r.tabu)) ns in
          let choice = r.select nonTabus state in
          optionMapOr (choice, meta)
                      (lam s. (Some s, TabuSearch {r with tabu=r.tabuAdd (r.tabuConvert s) r.tabu}))
                      (choice)
        in _search meta terminate callAfterEachIter nextSol state

    else error "Unknown meta heuristic in minimize"

mexpr

-- Example: Travelling Salesman Problem (TSP)
-- Given a weighted undirected graph, find a tour (Hamiltonian circuit) that
-- visits each node exactly once, with minimum path weight.

--------------------
-- Set up problem --
--------------------

-- Define instance data
let vs = ["Uppsala", "Stockholm", "Kiruna", "Gothenburg"] in
let es = [("Uppsala", "Stockholm", 80), ("Stockholm", "Uppsala", 90),
          ("Uppsala", "Gothenburg", 200), ("Gothenburg", "Uppsala", 250),
          ("Uppsala", "Kiruna", 10), ("Kiruna", "Uppsala", 320),
          ("Kiruna", "Stockholm", 500), ("Stockholm", "Kiruna", 20),
          ("Stockholm", "Gothenburg", 40), ("Gothenburg", "Stockholm", 65),
          ("Kiruna", "Gothenburg", 111), ("Gothenburg", "Kiruna", 321)] in

let g = digraphAddEdges es (digraphAddVertices vs (digraphEmpty eqstr eqi)) in

-- Define initial assignment, cost, select and legal functions
let initTour = [("Uppsala", "Kiruna", 10),
                ("Kiruna", "Stockholm", 500),
                ("Stockholm", "Gothenburg", 40),
                ("Gothenburg", "Uppsala", 250)] in

let cost = lam s.
  foldl (lam sum. lam edge. addi sum edge.2) 0 s in

let init = lam _. (initTour, cost initTour) in

-- Neighbourhood: replace 2 edges by two others s.t. still a tour
let neighbours = lam g. lam state.
  let curSol = state.cur in
  --let _ = dprint curSol in
  let tour = curSol.0 in

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

let terminate = lam state. geqi state.iter 10 in
let printIter = lam state. print (strJoin "" ["Iter: ", int2string state.iter, ", ",
                                              "Best: ", int2string state.inc.1, "\n"]) in

let initState = initSearchState init in

let minimizeTSP = minimize terminate printIter (neighbours g) initState in

----------------------------
-- Set up meta heuristics --
----------------------------

-- Select a random best neighbour
let randomBest = lam neighs. lam state.
  match neighs with [] then None () else
  let costs = map cost neighs in
  let minCost = min subi costs in
  let neighCosts = zipWith (lam n. lam c. (n,c)) neighs costs in
  let minNeighs = filter (lam t. eqi t.1 minCost) neighCosts in
  let randIdx = randIntU 0 (length minNeighs) in
  Some (get minNeighs randIdx)
in

let metaRandBest = Base {select = randomBest} in

-- Simulated annealing
let randSol = lam ns. lam state.
  match ns with [] then None () else
  let nRand = get ns (randIntU 0 (length ns)) in
  (nRand, cost nRand)
in

let decayFunc = lam temp. lam state.
  mulf temp 0.95
in

let metaSA = SimulatedAnnealing {select = randSol, temp = 100.0, decayFunc = decayFunc} in

-- Tabu search
let metaTabu = TabuSearch {select = randomBest,
                           tabu = [],
                           isTabu = lam assign. lam tabu. false,
                           tabuAdd = lam assign. lam tabu. cons assign tabu,
                           tabuConvert = identity} in

-----------------------
-- Solve the problem --
-----------------------

let _ = print "Choose a random best solution:\n" in
let _ = printIter initState in
let r = minimizeTSP metaRandBest in

let _ = print "Simulated annealing:\n" in
let _ = printIter initState in
let r = minimizeTSP metaSA in

let _ = print "Tabu search:\n" in
let _ = printIter initState in
let r = minimizeTSP metaTabu in

()
