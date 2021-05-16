
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- A generic library for (stochastic) local search algorithms.
-- Includes pre-defined meta-heuristics and allows design of custom dittos.

include "digraph.mc"
include "string.mc"
include "common.mc"

-- 'v': polymorphic value type
-- 'c': polymorphic cost type
type Assignment v = [v]
type Solution v c = {assignment : Assignment v, cost : c}
type SearchState v c = {
  cur : Solution v c,
  inc : Solution v c,
  iter : Int,
  stuck : Bool
}

----------------------------
-- Base language fragment --
----------------------------

lang LocalSearchBase

  syn MetaState =

  -- Solution v c -> (c -> c -> Int) -> SearchState v c
  sem initSearchState =
  | sol -> {cur = sol, inc = sol, iter = 0, stuck = false}

  -- SearchState v c -> [Assignment v]
  sem neighbourhood =

  -- [Assignment v] -> SearchState v c -> Option (Solution v c)
  sem select (assignments : [Assignment v]) =

  -- Assignment v -> c
  sem cost =

  -- 'cmp c1 c2' is negative if 'c1' < 'c2', positive if 'c1' > 'c2', otherwise 0
  sem compare (v1 : c) =

  -- SearchState v c -> MetaState v c -> (Option (Solution v c), MetaState v c)
  sem step (searchState : SearchState v c) =

  -- TODO: merge {searchState , metaState}
  -- TODO: handle stuck
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
      filterMin s [s] (lam s1. lam s2. searchState.cmp s1.cost s2.cost) sols in
    randElem minSols
end

-- No meta information
lang LocalSearchEmptyMeta = LocalSearchBase
  syn MetaState =
  | Empty {}

  sem step (searchState : SearchState v c) =
  | Empty {} ->
    (select (neighbourhood searchState) searchState, Empty {})
end

-- Simulated annealing
lang LocalSearchSimulatedAnnealing = LocalSearchBase
  syn MetaState =
  | SimulatedAnnealing {temp : Float}

  -- Modifies the temperature in each iteration
  -- Float -> SearchState v c -> Float
  sem decay (temp : Float) =

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

-----------
-- Tests --
-----------

type TspTourEdge = (String, String, Int)
type TspTour = [TspTourEdge]

-- Define instance data
let vs = ["Uppsala", "Stockholm", "Kiruna", "Gothenburg"]
let es = [("Uppsala", "Stockholm", 80), ("Stockholm", "Uppsala", 90),
          ("Uppsala", "Gothenburg", 200), ("Gothenburg", "Uppsala", 250),
          ("Uppsala", "Kiruna", 10), ("Kiruna", "Uppsala", 320),
          ("Kiruna", "Stockholm", 500), ("Stockholm", "Kiruna", 20),
          ("Stockholm", "Gothenburg", 40), ("Gothenburg", "Stockholm", 65),
          ("Kiruna", "Gothenburg", 111), ("Gothenburg", "Kiruna", 321)]

let g = digraphAddEdges es (digraphAddVertices vs (digraphEmpty eqString eqi))

-- Define initial solution
let initTour = [("Uppsala", "Kiruna", 10),
                ("Kiruna", "Stockholm", 500),
                ("Stockholm", "Gothenburg", 40),
                ("Gothenburg", "Uppsala", 250)]

let cost = lam s.
  foldl (lam sum. lam edge : TspTourEdge. addi sum edge.2) 0 s

let initSol = {assignment = initTour, cost = cost initTour}

-- Neighbourhood: replace 2 edges by two others s.t. tour is still a
-- Hamiltonian circuit
let neighbours = lam g. lam state : SearchState TspTour Int.
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


lang LocalSearchTsp = LocalSearchBase
  sem neighbourhood =
  | searchState -> neighbours g searchState

  sem cost =
  | s ->
    foldl (lam acc. lam edge : TspTourEdge. addi acc edge.2) 0 s

  sem compare (v1 : c) =
  | v2 -> subi v1 v2
end

lang LocalSearchTspSimulatedAnnealing = LocalSearchTsp
                                      + LocalSearchSimulatedAnnealing
                                      + LocalSearchSelectRandomUniform

  sem decay (searchState : SearchState v c) =
  | SimulatedAnnealing ({temp = temp} & t) ->
    SimulatedAnnealing {t with temp = mulf 0.95 temp}
end
mexpr

let terminate = lam state : SearchState TspTour Int.
  geqi state.iter 10 in
let printIter = lam state : SearchState TspTour Int.
  let inc : Solution TspTour Int = state.inc in
  print (join ["Iter: ", int2string state.iter, ", ",
               "Best: ", int2string inc.cost, "\n"]) in

recursive let loop = lam state. lam minimize.
  match state with (searchState, metaState) then
    printIter searchState;
    if terminate searchState then
      (searchState, metaState)
    else
      loop (minimize searchState metaState) minimize
  else never
in

use LocalSearchTspSimulatedAnnealing in

let meta = SimulatedAnnealing {temp = 100.0} in

let searchState = initSearchState initSol in

let endState = loop (searchState, meta) minimize in

()
