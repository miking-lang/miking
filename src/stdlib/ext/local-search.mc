
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
include "iterator.mc"

----------------------------
-- Base language fragment --
----------------------------

lang LocalSearchBase

  -- A local search solution: an assignment with a cost.
  type Solution = {assignment : Assignment, cost : Cost}

  -- Search state
  type SearchState = {
    cur : Solution,                               -- current solution
    inc : Solution,                               -- incumbent (best solution thus far)
    iter : Int,                                   -- number of iterations thus far
    stuck : Bool,                                 -- whether the search is stuck
    -- (no local moves possible)
    cost : Option Solution -> Assignment -> Cost, -- cost of an assignment
    cmp : Cost -> Cost -> Int,                    -- comparison of costs
    data : Option LSData                          -- any custom data
  }

  -- Maintains meta-information between search iterations.
  syn MetaState =

  -- An assignment of variables to values.
  syn Assignment =

  -- Cost of an assignment.
  syn Cost =

  -- Custom data to carry around in the search state
  syn LSData =

  -- Initialize the search state from an initial solution.
  sem initSearchState (cost : Option Solution -> Assignment -> Cost)
                      (cmp : Cost -> Cost -> Int) =
  | sol ->
    { cur = sol, inc = sol, iter = 0, stuck = false, cost = cost, cmp = cmp,
      data = None () }

  -- Initialize the search state from data and solution.
  sem initSearchStateData (cost : Option Solution -> Assignment -> Cost)
                          (cmp : Cost -> Cost -> Int) (data : LSData) =
  | sol ->
    { cur = sol, inc = sol, iter = 0, stuck = false, cost = cost, cmp = cmp,
      data = Some data }

  -- The neighbouring assignments from a search state.
  sem neighbourhood : SearchState -> Iterator [Assignment] Assignment

  -- Select a solution among the neighbours.
  sem select : Iterator [Assignment] Assignment -> SearchState -> Option Solution

  -- Take one step, return both the next solution (if there is one), and the
  -- resulting meta state.
  sem step : SearchState -> MetaState -> (Option Solution, MetaState)

  -- Take one step and update search state accordingly, return both the
  -- resulting search state and meta state.
  sem minimize : SearchState -> MetaState -> (SearchState, MetaState)
  sem minimize (searchState : SearchState) =
  | metaState ->
    match searchState with {stuck = true} then
      (searchState, metaState)
    else match searchState with {inc = inc, cmp = cmp} in
    let searchState = {searchState with iter = addi searchState.iter 1} in
    let next = step searchState metaState in
    match next with (None (), _) then
      ({searchState with stuck = true}, metaState)
    else match next with (Some cur, metaState) in
      let cur : Solution = cur in
      let inc : Solution = inc in
      let inc = if lti (cmp cur.cost inc.cost) 0 then cur else inc in
      let searchState = {{searchState with cur = cur} with inc = inc} in
      (searchState, metaState)

  -- Debug a meta state.
  sem debugMeta : MetaState -> ()
  sem debugMeta =
  | meta -> ()

  -- Debug a search state.
  sem debugSearch : SearchState -> ()
end

------------------------------------
-- Convenience language fragments --
-- for building search heuristics --
------------------------------------

-- Select a solution among the neighbours uniformly at random.
lang LocalSearchSelectRandomUniform = LocalSearchBase
  sem select assignments =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState with {cost = cost, inc = inc} then
      let as: [Assignment] = (iteratorToSeq assignments) in
      match randElem as with Some a then
        Some { assignment = a, cost = cost (Some searchState.inc) a }
      else
        None ()
    else never
end

-- Select a random best neighbour.
lang LocalSearchSelectRandomBest = LocalSearchBase
  sem select assignments =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState with {cost = cost, cmp = cmp, inc = inc} then
      let assignments = iteratorToSeq assignments in
      match assignments with [] then None () else

      -- Find minimum and filter out other elements in one pass.
      recursive let filterMin : all a. a -> [a] -> (a -> a -> Int) -> [a] -> [a] =
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

      let sols = map (lam a. {assignment = a, cost = cost (Some searchState.inc) a}) assignments in
      let s = head sols in
      let minSols =
        filterMin s [s] (lam s1 : Solution. lam s2 : Solution.
                           cmp s1.cost s2.cost) sols in
      randElem minSols
    else never
end

-- Select the first improving neighbour.
lang LocalSearchSelectFirstImproving = LocalSearchBase
  sem select assignments =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState with {cur = cur, cost = cost, cmp = cmp, inc = inc} then
      let cur : Solution = cur in
      let curCost = cur.cost in
      recursive let firstImproving = lam as.
        match iteratorNext as with (as, Some a) then
          let acost = cost (Some searchState.inc) a in
          if lti (cmp acost curCost) 0 then
            Some {assignment = a, cost = acost}
          else firstImproving as
        else None ()
      in
      firstImproving assignments
    else never
end

lang LocalSearchSelectFirst = LocalSearchBase
  sem select assignments =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState with {cost = cost, inc = inc} then
      match iteratorNext assignments with (_, Some a) then
        Some {assignment = a, cost = cost (Some searchState.inc) a}
      else None ()
    else never
end

-- Simulated annealing
lang LocalSearchSimulatedAnnealing = LocalSearchBase
  syn MetaState =
  | SimulatedAnnealing {temp : Float}

  -- Modifies the temperature in each iteration
  sem decay : SearchState -> MetaState -> MetaState

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
      if leqi (searchState.cmp proposal.cost cur.cost) 0 then
        -- Improving solution: accept.
        (Some proposal, decayed)
      else
        -- Worsening solution: accept with probability depending on temperature.
        let accept =
          let pAccept =
            exp (divf
              (int2float (searchState.cmp proposal.cost cur.cost)) t.temp) in
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

  sem isTabu : (Assignment, TabuSet) -> Bool

  -- Update the tabu set
  sem tabuUpdate : (Assignment, TabuSet) -> TabuSet

  sem step (searchState : SearchState) =
  | TabuSearch ({tabu = tabu} & t) ->
    let nonTabus =
      iteratorFilter (lam n. not (isTabu (n, tabu))) (neighbourhood searchState)
    in
    match select nonTabus searchState with Some choice then
      let choice : Solution = choice in
      (Some choice, TabuSearch {t with tabu = tabuUpdate (choice.assignment, tabu)})
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

let _tspGraph = digraphAddEdges _es (digraphAddVertices _vs (digraphEmpty cmpString eqi))

-- Define initial solution
let _initTour = [("Uppsala", "Kiruna", 10),
                 ("Kiruna", "Stockholm", 500),
                 ("Stockholm", "Gothenburg", 40),
                 ("Gothenburg", "Uppsala", 250)]

let _toursEq = lam t1. lam t2.
  eqsetEqual (digraphEdgeEq _tspGraph) t1 t2

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
  | TspCost {cost : Int}

  sem neighbourhood =
  | searchState ->
    let ns: [Assignment] =
      let searchState : SearchState = searchState in
      match searchState with {cur = {assignment = TspTour {tour = tour}}} then
        map (lam tour. TspTour {tour = tour})
            (_tspNeighbours _tspGraph tour)
      else never
    in
    iteratorFromSeq ns

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

-- NOTE(johnwikman, 2024-09-11): Test cases below make use of randIntU within
-- simulated annealing. Had one of those tests below randomly fail in a manner
-- which I cannot reproduce, so explicitly setting seed to 0 to make tests
-- below deterministic.
randSetSeed 0;

type SearchState = use LocalSearchBase in SearchState in
type MetaState = use LocalSearchBase in MetaState in

let debug = false in

let nIters = lam n. lam state : use LocalSearchBase in SearchState.
  or (state.stuck) (geqi state.iter n) in

recursive let loopf =
  lam terminate : use LocalSearchBase in SearchState -> Bool.
  lam state : use LocalSearchBase in (SearchState, MetaState).
  lam debugMeta : use LocalSearchBase in MetaState -> ().
  lam debugSearch : use LocalSearchBase in SearchState -> ().
  lam minimize :
    use LocalSearchBase in SearchState -> MetaState -> (SearchState, MetaState).
  match state with (searchState, metaState) then
    (if debug then debugSearch searchState else ());
    (if debug then debugMeta metaState else ());
    if terminate searchState then
      (searchState, metaState)
    else
      loopf terminate (minimize searchState metaState)
        debugMeta debugSearch minimize
  else never in

use _testTsp in

let costFun : Option Solution -> Assignment -> Cost = lam. lam tour : Assignment.
  match tour with TspTour {tour = tour} in
  TspCost {cost = foldl (lam acc. lam e : TspEdge. addi acc e.2) 0 tour}
in

let cmpFun : Cost -> Cost -> Int = lam c1. lam c2.
  match (c1, c2) with (TspCost {cost = v1}, TspCost {cost = v2}) in
  subi v1 v2
in

let initAssignment = TspTour {tour = _initTour} in
let initSol = {
  assignment = initAssignment,
  cost = costFun (None ()) initAssignment
} in

let startState = initSearchState costFun cmpFun initSol in

-- Use simulated annealing.
use _testTspSimulatedAnnealing in

let metaSA = SimulatedAnnealing {temp = 100.0} in

utest
  match loopf (nIters 100) (startState, metaSA) debugMeta debugSearch minimize
  with ({inc = {cost = TspCost {cost = cost}}}, _) then cost
  else never
with 251 in

-- Use tabu search.
use _testTspTabuSearch in

let metaTabu = TabuSearch {tabu = TabuList {list = []}} in

utest
  match loopf (nIters 100) (startState, metaTabu) debugMeta debugSearch minimize
  with ({inc = {cost = TspCost {cost = cost}}}, metaState) then
    cost
  else never
with 251 in

-- Start with simulated annealing, then switch to tabu search.
use _testTspSimulatedAnnealing in

utest
  match loopf (nIters 10) (startState, metaSA) debugMeta debugSearch minimize
  with ({inc = {cost = TspCost {cost = cost}}} & searchState, _) then
    use _testTspTabuSearch in

    utest
      match
        loopf (nIters 100) (searchState, metaTabu) debugMeta debugSearch minimize
      with ({inc = {cost = TspCost {cost = cost}}}, metaState) then
        cost
      else never
    with 251 in

    leqi cost 800
  else never
with true in

()
