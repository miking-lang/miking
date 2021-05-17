
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- A generic library for (stochastic) local search algorithms.
--
-- To design a local search algorithm, provide implementations for the semantic
-- functions in the language fragment 'LocalSearchBase'. The syn 'MetaState' can
-- be used to maintain meta-information between search iterations. See the
-- fragments 'LocalSearchSimulatedAnnealing' and 'LocalSearchTabuSearch' for an
-- implementation of simulated annealing and tabu search, respectively.
--
-- The tests contain an implementation of the travelling salesman problem (TSP).
-- See this example for how to use the pre-defined language fragments as
-- building blocks when implementing local search for this problem.

include "common.mc"
include "string.mc"
include "digraph.mc"

-- A local search solution: an assignment with a cost.
type Solution = {assignment : Assignment, cost : Cost}

-- Search state.
type SearchState = {
  cur : Solution,              -- current solution
  inc : Solution,              -- incumbent (best solution thus far)
  iter : Int,                  -- number of iterations thus far
  stuck : Bool,                -- whether the search is stuck
                               -- (no local moves possible)
  cost : Assignment -> Cost    -- cost of an assignment
}

----------------------------
-- Base language fragment --
----------------------------

lang LocalSearchBase

  -- Maintains meta-information between search iterations.
  syn MetaState =

  -- An assignment of variables to values.
  syn Assignment =

  -- Cost of an assignment.
  syn Cost =

  -- Initialize the search state from an initial assignment.
  -- : (Assignment -> Cost) -> Assignment -> SearchState
  sem initSearchState (cost : Assignment -> Cost) =
  | a ->
    let sol = {assignment = a, cost = cost a} in
    {cur = sol, inc = sol, iter = 0, stuck = false, cost = cost}

  -- The neighbouring assignments from a search state.
  -- : SearchState -> [Assignment]
  sem neighbourhood =

  -- Select a solution among the neighbours.
  -- : [Assignment] -> SearchState -> Option Solution
  sem select (assignments : [Assignment]) =

  -- Comparison function for costs.
  -- : (Cost, Cost) -> Int
  sem compare =

  -- Take one step, return both the next solution (if there is one), and the
  -- resulting meta state.
  -- : SearchState -> MetaState -> (Option Solution, MetaState)
  sem step (searchState : SearchState) =

  -- Take one step and update search state accordingly, return both the
  -- resulting search state and meta state.
  -- : SearchState -> MetaState -> (SearchState, MetaState)
  sem minimize (searchState : SearchState) =
  | metaState ->
    match searchState with {stuck = true} then
      (searchState, metaState)
    else match searchState with {inc = inc} then
      let searchState = {searchState with iter = addi searchState.iter 1} in
      let next = step searchState metaState in
      match next with (None (), _) then
        ({searchState with stuck = true}, metaState)
      else match next with (Some cur, metaState) then
        let cur : Solution = cur in
        let inc : Solution = inc in
        let inc = if lti (compare (cur.cost, inc.cost)) 0 then cur else inc in
        let searchState = {{searchState with cur = cur} with inc = inc} in
        (searchState, metaState)
      else dprintLn next; never
    else never

  -- Debug a meta state.
  -- : MetaState -> Unit
  sem debugMeta =
  | meta -> ()

  -- Debug a search state.
  -- : SearchState -> Unit
  sem debugSearch =
end

------------------------------------
-- Convenience language fragments --
-- for building search heuristics --
------------------------------------

-- Select a solution among the neighbours uniformly at random.
lang LocalSearchSelectRandomUniform = LocalSearchBase
  sem select (assignments : [Assignment]) =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState with {cost = cost} then
      match randElem assignments with Some a then
        Some {assignment = a, cost = cost a}
      else
        None ()
    else never
end

-- Select a random best neighbour.
lang LocalSearchSelectRandomBest = LocalSearchBase
  sem select (assignments : [Assignment]) =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState with {cost = cost} then
      match assignments with [] then None () else

      -- Find minimum and filter out other elements in one pass.
      recursive let filterMin : a -> [a] -> (a -> a -> Int) -> [a] -> [a] =
        lam e. lam acc. lam cmp. lam xs.
        match xs with [] then acc
        else match xs with [x] ++ xs then
          let v = cmp e x in
          match v with 0 then
            filterMin e (cons x acc) cmp xs
          else if lti v 0 then
            filterMin e acc cmp xs
          else
            filterMin x [x] cmp xs
        else never
      in
      utest filterMin 1000 [] subi [42,1,1,3] with [1,1] in

      let sols = map (lam a. {assignment = a, cost = cost a}) assignments in
      let s = head sols in
      let minSols =
        filterMin s [s] (lam s1 : Solution. lam s2 : Solution.
                           compare (s1.cost, s2.cost)) sols in
      randElem minSols
    else never
end

-- Select the first improving neighbour.
lang LocalSearchSelectFirstImproving = LocalSearchBase
  sem select (assignments : [Assignments v]) =
  | searchState ->
    match searchState with {cur = cur, cost = cost} then
      let cur : Solution = cur in
      let curCost = cur.cost in
      recursive let firstImproving = lam as : [Assignment].
        match as with [] then None ()
        else match as with [a] ++ as then
          let acost = cost a in
          if lti acost curCost then
            Some {assignment = a, cost = acost}
          else firstImproving as
        else never
      in
      firstImproving assignments
    else never
end

-- Simulated annealing
lang LocalSearchSimulatedAnnealing = LocalSearchBase
  syn MetaState =
  | SimulatedAnnealing {temp : Float}

  -- Modifies the temperature in each iteration
  -- : SearchState -> MetaState -> MetaState
  sem decay (searchState : SearchState) =

  sem step (searchState : SearchState) =
  | SimulatedAnnealing t ->
    let proposal = select (neighbourhood searchState) searchState in
    match proposal with None () then
      (None (), SimulatedAnnealing t)
    else match proposal with Some proposal then
      let proposal : Solution = proposal in
      let decayed = decay searchState (SimulatedAnnealing t) in
      let cur : Solution = searchState.cur in
      -- Metropolis condition
      if leqi (compare (proposal.cost, cur.cost)) 0 then
        -- Improving solution: accept.
        (Some proposal, decayed)
      else
        -- Worsening solution: accept with probability depending on temperature.
        let accept =
          let pAccept =
            exp (divf (int2float (compare (proposal.cost, cur.cost))) t.temp) in
          let rnd = int2float (randIntU 0 100) in
          geqf (mulf pAccept 100.0) rnd
        in
        (Some (if accept then proposal else cur), decayed)
    else never
end

-- Tabu search
lang LocalSearchTabuSearch = LocalSearchBase
  syn TabuSet =

  syn MetaState =
  | TabuSearch {tabu : TabuSet}

  -- : (Assignment, TabuSet) -> Bool
  sem isTabu =

  -- Update the tabu set
  -- : (Assignment, TabuSet) -> TabuSet
  sem tabuUpdate =

  sem step (searchState : SearchState) =
  | TabuSearch ({tabu = tabu} & t) ->
    let ns = neighbourhood searchState in
    let nonTabus = filter (lam n. not (isTabu (n, tabu))) ns in
    match select nonTabus searchState with Some choice then
      let choice : Solution = choice in
      (Some choice, TabuSearch {tabu = tabuUpdate (choice.assignment, tabu)})
    else
      (None (), TabuSearch t)
end

-----------
-- Tests --
-----------

-- Example: Travelling Salesman Problem (TSP)
-- Given a weighted directed graph, find a tour (Hamiltonian circuit) that
-- visits each node exactly once, with minimum path weight.

type TspEdge = (String, String, Int)

-- Define instance data
let _vs = ["Uppsala", "Stockholm", "Kiruna", "Gothenburg"]
let _es = [("Uppsala", "Stockholm", 80), ("Stockholm", "Uppsala", 90),
           ("Uppsala", "Gothenburg", 200), ("Gothenburg", "Uppsala", 250),
           ("Uppsala", "Kiruna", 10), ("Kiruna", "Uppsala", 320),
           ("Kiruna", "Stockholm", 500), ("Stockholm", "Kiruna", 20),
           ("Stockholm", "Gothenburg", 40), ("Gothenburg", "Stockholm", 65),
           ("Kiruna", "Gothenburg", 111), ("Gothenburg", "Kiruna", 321)]

let _tspGraph = digraphAddEdges _es (digraphAddVertices _vs (digraphEmpty eqString eqi))

-- Define initial solution
let _initTour = [("Uppsala", "Kiruna", 10),
                 ("Kiruna", "Stockholm", 500),
                 ("Stockholm", "Gothenburg", 40),
                 ("Gothenburg", "Uppsala", 250)]

let _toursEq = lam t1. lam t2.
  eqsetEqual (digraphEdgeEq _tspGraph) t1 t2

let _tspCost = lam tour.
  foldl (lam acc. lam edge : TspEdge. addi acc edge.2) 0 tour

-- Neighbourhood: replace 2 edges by two others s.t. tour is still a
-- Hamiltonian circuit.
let _tspNeighbours = lam g. lam tour : [TspEdge].
  let tourHasEdge = lam v1. lam v2.
    any (lam e : TspEdge. or (and (eqString v1 e.0) (eqString v2 e.1))
                                 (and (eqString v1 e.1) (eqString v2 e.0))) tour in

  -- Find replacing edges for 'e12' and 'e34'
  let exchange = lam e12 : TspEdge. lam e34 : TspEdge.
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
        error "Expected at most one edge between any two nodes"
    in res
  in

  let neighbourFromExchange = lam oldEdgs. lam newEdgs. lam tour.
    let equal = digraphEdgeEq g in
    eqsetUnion equal newEdgs (eqsetDiff equal tour oldEdgs)
  in

  let possibleExchanges =
    foldl (lam outerAcc. lam e1.
           concat outerAcc
           (foldl (lam innerAcc. lam e2.
                     let e = exchange e1 e2 in
                     match e with Some r then cons r innerAcc else innerAcc)
                  [] tour))
          []
          tour
  in map (lam ex : (TspEdge, TspEdge, TspEdge, TspEdge).
            neighbourFromExchange [ex.0,ex.1] [ex.2,ex.3] tour) possibleExchanges

-- Problem-specific definitions.
lang _testTsp = LocalSearchBase
  syn Assignment =
  | TspTour {tour : [TspEdge]}

  syn Cost =
  | TspCost {cost : Float}

  sem neighbourhood =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState with {cur = {assignment = TspTour {tour = tour}}} then
      map (lam tour. TspTour {tour = tour})
          (_tspNeighbours _tspGraph tour)
    else never

  sem compare =
  | (TspCost {cost = v1}, TspCost {cost = v2}) ->
    subi v1 v2

  sem debugSearch =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState with {iter = iter, inc = {cost = TspCost {cost = cost}}}
    then
      printLn (join ["Iter: ", int2string iter, "\n",
                     "Best cost: ", int2string cost])
    else never
end

lang _testTspSimulatedAnnealing = _testTsp
                                + LocalSearchSimulatedAnnealing
                                + LocalSearchSelectRandomUniform

  sem decay (searchState : SearchState) =
  | SimulatedAnnealing ({temp = temp} & t) ->
    SimulatedAnnealing {t with temp = mulf 0.95 temp}

  sem debugMeta =
  | SimulatedAnnealing {temp = temp} ->
    print (join ["Temperature: ", float2string temp, "\n"])
end

lang _testTspTabuSearch = _testTsp
                        + LocalSearchTabuSearch
                        + LocalSearchSelectRandomBest
  syn TabuSet =
  | TabuList {list : [[TspEdge]]}

  sem isTabu =
  | (TspTour {tour = tour}, TabuList {list = list}) ->
    any (_toursEq tour) list

  sem tabuUpdate =
  | (TspTour {tour = tour}, TabuList {list = list}) ->
    TabuList {list = cons tour list}

  sem debugMeta =
  | TabuSearch {tabu = TabuList {list = list}} ->
    print (join ["Tabu length: ", int2string (length list), "\n"])
end

mexpr

let debug = false in

let nIters = lam n. lam state : SearchState.
  or (state.stuck) (geqi state.iter n) in

recursive let loop =
  lam terminate : SearchState -> Bool.
  lam state : (SearchState, MetaState).
  lam debugMeta : MetaState -> Unit.
  lam debugSearch : SearchState -> Unit.
  lam minimize : SearchState -> MetaState -> (SearchState, MetaState).
  match state with (searchState, metaState) then
    (if debug then debugSearch searchState else ());
    (if debug then debugMeta metaState else ());
    if terminate searchState then
      (searchState, metaState)
    else
      loop terminate (minimize searchState metaState)
        debugMeta debugSearch minimize
  else never in

use _testTsp in

let startState = initSearchState
  (lam tour : Assignment.
     match tour with TspTour {tour = tour}
     then TspCost {cost = _tspCost tour}
     else never)
  (TspTour {tour = _initTour}) in

-- Use simulated annealing.
use _testTspSimulatedAnnealing in

let metaSA = SimulatedAnnealing {temp = 100.0} in

(match loop (nIters 100) (startState, metaSA) debugMeta debugSearch minimize
 with ({inc = {cost = TspCost {cost = cost}}}, _) then
   utest cost with 251 in ()
 else never);

-- Use tabu search.
use _testTspTabuSearch in

let metaTabu = TabuSearch {tabu = TabuList {list = []}} in

(match loop (nIters 100) (startState, metaTabu) debugMeta debugSearch minimize
 with ({inc = {cost = TspCost {cost = cost}}}, metaState) then
   utest cost with 251 in ()
 else never);

-- Start with simulated annealing, then switch to tabu search.
use _testTspSimulatedAnnealing in

(match loop (nIters 10) (startState, metaSA) debugMeta debugSearch minimize
 with ({inc = {cost = TspCost {cost = cost}}} & searchState, _) then
   utest leqi cost 800 with true in

   use _testTspTabuSearch in

   match loop (nIters 100) (searchState, metaTabu) debugMeta debugSearch  minimize
   with ({inc = {cost = TspCost {cost = cost}}}, metaState) then
     utest cost with 251 in ()
    else never
 else never);

()
