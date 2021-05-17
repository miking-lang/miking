
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

-- An assignment of indices to values.
type Assignment v = [v]

-- A local search solution: an assignment with a cost.
type Solution v c = {assignment : Assignment v, cost : c}

-- Search state.
type SearchState v c = {
  cur : Solution v c,  -- current solution
  inc : Solution v c,  -- incumbent (best solution thus far)
  iter : Int,          -- number of iterations thus far
  stuck : Bool         -- whether the search is stuck
}                      -- (no local moves possible)

----------------------------
-- Base language fragment --
----------------------------

lang LocalSearchBase

  syn MetaState =

  -- Initialize the search state from an initial assignment.
  -- : Assignment v -> SearchState v c
  sem initSearchState =
  | a ->
    let sol = {assignment = a, cost = cost a} in
    {cur = sol, inc = sol, iter = 0, stuck = false}

  -- The neighbouring assignments from a search state.
  -- : SearchState v c -> [Assignment v]
  sem neighbourhood =

  -- Select a solution among the neighbours.
  -- : [Assignment v] -> SearchState v c -> Option (Solution v c)
  sem select (assignments : [Assignment v]) =

  -- The cost of an assignment.
  -- : Assignment v -> c
  sem cost =

  -- Comparison function for costs.
  -- : c -> c -> Int
  sem compare (v1 : c) =

  -- Take one step, return both the next solution (if there is one), and the
  -- resulting meta state.
  -- : SearchState v c -> MetaState -> (Option (Solution v c), MetaState)
  sem step (searchState : SearchState v c) =

  -- Take one step and update search state accordingly, return both the
  -- resulting search state and meta state.
  -- : SearchState v c -> MetaState -> (SearchState v c, MetaState)
  sem minimize (searchState : SearchState v c) =
  | metaState ->
    match searchState with {stuck = true} then
      (searchState, metaState)
    else match searchState with {inc = inc} then
      let searchState = {searchState with iter = addi searchState.iter 1} in
      let next = step searchState metaState in
      match next with (None (), _) then
        ({searchState with stuck = true}, metaState)
      else match next with (Some cur, metaState) then
        let cur : Solution v c = cur in
        let inc : Solution v c = inc in
        let inc = if lti (compare cur.cost inc.cost) 0 then cur else inc in
        let searchState = {{searchState with cur = cur} with inc = inc} in
        (searchState, metaState)
      else never
    else never

  -- Debug a meta state.
  -- : Bool -> MetaState -> Unit
  sem debugMeta (debug : Bool) =
  | meta -> ()
end

------------------------------------
-- Convenience language fragments --
-- for building search heuristics --
------------------------------------

-- Select a solution among the neighbours uniformly at random.
lang LocalSearchSelectRandomUniform = LocalSearchBase
  sem select (assignments : [Assignment v]) =
  | searchState ->
    match randElem assignments with Some a then
      Some {assignment = a, cost = cost a}
    else
      None ()
end

-- Select a random best neighbour.
lang LocalSearchSelectRandomBest = LocalSearchBase
  sem select (assignments : [Assignment v]) =
  | searchState ->
    let searchState : SearchState v c = searchState in
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
      filterMin s [s] (lam s1 : Solution v c. lam s2 : Solution v c.
                         compare s1.cost s2.cost) sols in
    randElem minSols
end

-- Select the first improving neighbour.
lang LocalSearchSelectFirstImproving = LocalSearchBase
  sem select (assignments : [Assignments v]) =
  | searchState ->
    match searchState with {cur = cur} then
      let cur : Solution v c = cur in
      let curCost = cur.cost in
      recursive let firstImproving = lam as : [Assignment v].
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
  -- : SearchState v c -> MetaState -> MetaState
  sem decay (searchState : SearchState v c) =

  sem step (searchState : SearchState v c) =
  | SimulatedAnnealing t ->
    let proposal = select (neighbourhood searchState) searchState in
    match proposal with None () then
      (None (), SimulatedAnnealing t)
    else match proposal with Some proposal then
      let proposal : Solution v c = proposal in
      let decayed = decay searchState (SimulatedAnnealing t) in
      let cur : Solution v c = searchState.cur in
      -- Metropolis condition
      if leqi (compare proposal.cost cur.cost) 0 then
        -- Improving solution: accept.
        (Some proposal, decayed)
      else
        -- Worsening solution: accept with probability depending on temperature.
        let accept =
          let pAccept =
            exp (divf (int2float (subi proposal.cost cur.cost)) t.temp) in
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

  -- : Assignment -> TabuSet -> Bool
  sem isTabu (assignment : Assignment v) =

  -- Update the tabu set
  -- : Assignment v -> TabuSet -> TabuSet
  sem tabuUpdate (assignment : Assignment v) =

  sem step (searchState : SearchState v c) =
  | TabuSearch ({tabu = tabu} & t) ->
    let ns = neighbourhood searchState in
    let nonTabus = filter (lam n. not (isTabu n tabu)) ns in
    match select nonTabus searchState with Some choice then
      let choice : Solution v c = choice in
      (Some choice, TabuSearch {tabu = tabuUpdate choice.assignment tabu})
    else
      (None (), TabuSearch t)
end

-----------
-- Tests --
-----------

-- Example: Travelling Salesman Problem (TSP)
-- Given a weighted directed graph, find a tour (Hamiltonian circuit) that
-- visits each node exactly once, with minimum path weight.

type TspTourEdge = (String, String, Int)
type TspTour = [TspTourEdge]

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

-- Neighbourhood: replace 2 edges by two others s.t. tour is still a
-- Hamiltonian circuit.
let _tspNeighbours = lam g. lam state : SearchState TspTour Int.
  let curSol : Solution TspTour Int = state.cur in
  let tour = curSol.assignment in

  let tourHasEdge = lam v1. lam v2.
    any (lam e : TspTourEdge. or (and (eqString v1 e.0) (eqString v2 e.1))
                                 (and (eqString v1 e.1) (eqString v2 e.0))) tour in

  -- Find replacing edges for 'e12' and 'e34'
  let exchange = lam e12 : TspTourEdge. lam e34 : TspTourEdge.
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
  in map (lam ex : (TspTourEdge, TspTourEdge, TspTourEdge, TspTourEdge).
            neighbourFromExchange [ex.0,ex.1] [ex.2,ex.3] tour) possibleExchanges


-- Problem-specific definitions.
lang _testTsp = LocalSearchBase
  sem neighbourhood =
  | searchState -> _tspNeighbours _tspGraph searchState

  sem cost =
  | s ->
    foldl (lam acc. lam edge : TspTourEdge. addi acc edge.2) 0 s

  sem compare (v1 : c) =
  | v2 -> subi v1 v2
end

lang _testTspSimulatedAnnealing = _testTsp
                                + LocalSearchSimulatedAnnealing
                                + LocalSearchSelectRandomUniform

  sem decay (searchState : SearchState v c) =
  | SimulatedAnnealing ({temp = temp} & t) ->
    SimulatedAnnealing {t with temp = mulf 0.95 temp}

  sem debugMeta (debug : Bool) =
  | SimulatedAnnealing {temp = temp} ->
    if debug then
      print (join ["Temperature: ", float2string temp, "\n"])
    else ()
end

lang _testTspTabuSearch = _testTsp
                        + LocalSearchTabuSearch
                        + LocalSearchSelectRandomBest
  syn TabuSet =
  | TabuList {list : [Assignment TspTour]}

  sem isTabu (tour : Assignment v) =
  | TabuList {list = list} ->
    any (_toursEq tour) list

  sem tabuUpdate (tour : Assignment TspTour) =
  | TabuList {list = list} ->
    TabuList {list = cons tour list}

  sem debugMeta (debug : Bool) =
  | TabuSearch {tabu = TabuList {list = list}} ->
    if debug then
      print (join ["Tabu length: ", int2string (length list), "\n"])
    else ()
end

mexpr

let debug = false in
let debugPrint = if debug then print else lam. () in

let nIters = lam n. lam state : SearchState TspTour Int.
  or (state.stuck) (geqi state.iter n) in

let printSearchState = lam state : SearchState TspTour Int.
  let inc : Solution TspTour Int = state.inc in
  debugPrint (join ["Iter: ", int2string state.iter, ", ",
                    "Best: ", int2string inc.cost, "\n"]) in

recursive let loop =
  lam terminate : SearchState TspTour Int -> Bool.
  lam state : (SearchState TspTour Int, MetaState).
  lam debugMeta : Bool -> MetaState -> Unit.
  lam minimize : SearchState TspTour Int -> MetaState -> (SearchState TspTour Int, MetaState).
  match state with (searchState, metaState) then
    printSearchState searchState;
    debugMeta debug metaState;
    if terminate searchState then
      (searchState, metaState)
    else
      loop terminate (minimize searchState metaState) debugMeta minimize
  else never in

use _testTsp in

let startState = initSearchState _initTour in

-- Use simulated annealing.
use _testTspSimulatedAnnealing in

let metaSA = SimulatedAnnealing {temp = 100.0} in

(match loop (nIters 100) (startState, metaSA) debugMeta minimize
 with ({inc = {cost = cost}}, _) then
   utest cost with 251 in ()
 else never);

-- Use tabu search.
use _testTspTabuSearch in

let metaTabu = TabuSearch {tabu = TabuList {list = []}} in

(match loop (nIters 100) (startState, metaTabu) debugMeta minimize
  with ({inc = {cost = cost}}, metaState) then
   utest cost with 251 in ()
 else never);

-- Start with simulated annealing, then switch to tabu search.
use _testTspSimulatedAnnealing in

(match loop (nIters 10) (startState, metaSA) debugMeta minimize
 with ({inc = {cost = cost}} & searchState, _) then
   utest leqi cost 800 with true in

   use _testTspTabuSearch in

   match loop (nIters 100) (searchState, metaTabu) debugMeta minimize
   with ({inc = {cost = cost}}, metaState) then
     utest cost with 251 in ()
    else never
 else never);

()
