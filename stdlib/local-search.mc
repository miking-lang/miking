-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- A generic library for (stochastic) local search algorithms.
-- Includes pre-defined meta-heuristics and allows design of custom dittos.

include "prelude.mc"
include "set.mc"
include "digraph.mc"
include "string.mc"

-- 'v': polymorphic value type
-- 'c': polymorphic cost type
type Assignment v = [v]
type Solution v c = (Assignment v, c)
type SearchState v c = {
  cur : Solution v c,
  inc : Solution v c,
  iter : Int,
  stuck : Bool,
  -- 'cmp c1 c2' is negative if 'c1' < 'c2', positive if 'c1' > 'c2', otherwise 0
  cmp : c -> c -> Int
}

type MetaState v c
con Base               : {}                                             -> MetaState v c
con SimulatedAnnealing : {temp : Float,
                          decayFun : Float -> SearchState v c -> Float} -> MetaState v c
con TabuSearch         : {tabuConvert : Solution v c -> t,
                          tabu : [t],
                          isTabu : t -> [t] -> Bool,
                          tabuAdd : t -> [t] -> [t]}                    -> MetaState v c

type NeighbourhoodFun v c = SearchState v c -> [Assignment v]
type SelectFun v c = [Assignment v] -> SearchState v c -> Option (Solution v c)
type StepFun v c = SearchState v c -> MetaState v c -> (Option (Solution v c), MetaState v c)

type MetaHeuristic v c = (MetaState v c, StepFun v c)

-- Master search algorithm.
--
-- 'minimize stop f state heur' takes a number of steps (by calling the step
-- function 'heur.1') using 'state' as initial state, and returns a tuple
-- ('sstate', 'mstate'), s.t.:
--  'sstate.inc' is the incumbent, i.e. best found, solution.
--  'sstate.iter' is the number of iterations, i.e. steps taken.
--  'sstate.cur' is the current, i.e. last seen, solution.
--  'sstate.stuck' is true iff the search got stuck (no further step possible).
--  'mstate' is the current meta state.
-- The search terminates when 'stop st' is true, where 'st' is the current
-- search state. The function 'f' is called between each iteration. The search
-- can be continued from the resulting state by using 'sstate' and 'mstate' in
-- subsequent calls to 'minimize' (see tests for examples).
let minimize : (SearchState v c -> Bool) -> (SearchState v c -> Unit) -> SearchState v c -> MetaHeuristic v c -> (SearchState v c, MetaState v c) =
  lam terminate. lam callAfterEachIter. lam state. lam metaHeur.
    let step = metaHeur.1 in
    recursive let search = lam sstate. lam mstate.
      if not (terminate sstate) then
        let sstate = {sstate with iter=addi sstate.iter 1} in
        let next = step sstate mstate in
        let newCur = next.0 in
        match newCur with None () then
          ({sstate with stuck = true}, mstate)
        else
          let mstate = next.1 in
          let cur = optionGetOrElse (lam _. error "Expected a solution") newCur in
          -- New best solution?
          let inc = if lti (sstate.cmp cur.1 sstate.inc.1) 0 then cur else sstate.inc in
          let sstate = {{sstate with cur = cur} with inc = inc} in
          let _ = callAfterEachIter sstate in
          search sstate mstate
      else
        (sstate, mstate)
    in search state metaHeur.0

-- 'initSearchState sol cmp' initialises a search state, where 'sol' is to be
-- used as the initial solution in the search and 'cmp' compares the cost of two
-- solutions.
let initSearchState : Solution v c -> (c -> c -> Int) -> SearchState v c =
  lam initSol. lam cmp.
    {cur = initSol,
     inc = initSol,
     iter = 0,
     stuck = false,
     cmp = cmp}

-- 'stepBase ns sel' returns a step function for a Base meta heuristic, using
-- 'ns' as the neighourhood function and 'sel' as the select function.
let stepBase : NeighbourhoodFun v c -> SelectFun v c -> StepFun v c =
  lam neighbourhood. lam select.
    let step = lam state. lam meta.
      (select (neighbourhood state) state, meta)
    in step

-- 'stepSA ns sel' returns a step function for a simulated annealing meta
-- heuristic, using 'ns' as the neighourhood function and 'sel' as the select
-- function.
let stepSA : NeighbourhoodFun v c -> SelectFun v c -> StepFun v c =
  lam neighbourhood. lam select.
    let step = lam state. lam meta.
      match meta with SimulatedAnnealing r then
        let updatedMeta = SimulatedAnnealing {r with temp=r.decayFunc r.temp state} in
        let proposalOpt = select (neighbourhood state) state in
        -- Leave meta unchanged if stuck
        match proposalOpt with None () then (None (), meta) else
        let proposal = optionGetOrElse (lam _. error "Expected a solution") proposalOpt in
        -- Metropolis condition
        if leqi (state.cmp proposal.1 state.cur.1) 0 then
          -- Always accept improving solution
          (Some proposal, updatedMeta)
        else
          -- Accept worsening solution with a probability dependent on temperature
          let pAccept = exp (divf (int2float (subi proposal.1 state.cur.1)) r.temp) in
          let rnd = int2float (randIntU 0 100) in
          let choice = if geqf (mulf pAccept 100.0) rnd then proposal else state.cur in
          (Some choice, updatedMeta)
      else
        error "Expected simulated annealing as meta heuristics"
    in step

-- 'stepTabu ns sel' returns a step function for a tabu search meta heuristic,
-- using 'ns' as the neighourhood function and 'sel' as the select function.
let stepTabu : NeighbourhoodFun v c -> SelectFun v c -> StepFun v c =
  lam neighbourhood. lam select.
    let step : StepFun = lam state. lam meta.
      match meta with TabuSearch r then
        let ns = neighbourhood state in
        let nonTabus = filter (lam n. not (r.isTabu n r.tabu)) ns in
        let choice = select nonTabus state in
        optionMapOr (None (), meta)
                    (lam s. (Some s, TabuSearch {r with tabu=r.tabuAdd (r.tabuConvert s) r.tabu}))
                    (choice)
      else
        error "Expected tabu search as meta heuristics"
    in step

mexpr

-- Enable/disable printing in tests
let printEnabled = false in
let print = if printEnabled then print else identity in

-- Example: Travelling Salesman Problem (TSP)
-- Given a weighted directed graph, find a tour (Hamiltonian circuit) that
-- visits each node exactly once, with minimum path weight.

------------------------
-- Set up the problem --
------------------------

-- Define instance data
let vs = ["Uppsala", "Stockholm", "Kiruna", "Gothenburg"] in
let es = [("Uppsala", "Stockholm", 80), ("Stockholm", "Uppsala", 90),
          ("Uppsala", "Gothenburg", 200), ("Gothenburg", "Uppsala", 250),
          ("Uppsala", "Kiruna", 10), ("Kiruna", "Uppsala", 320),
          ("Kiruna", "Stockholm", 500), ("Stockholm", "Kiruna", 20),
          ("Stockholm", "Gothenburg", 40), ("Gothenburg", "Stockholm", 65),
          ("Kiruna", "Gothenburg", 111), ("Gothenburg", "Kiruna", 321)] in

let g = digraphAddEdges es (digraphAddVertices vs (digraphEmpty eqstr eqi)) in

-- Define initial solution
let initTour = [("Uppsala", "Kiruna", 10),
                ("Kiruna", "Stockholm", 500),
                ("Stockholm", "Gothenburg", 40),
                ("Gothenburg", "Uppsala", 250)] in

let cost = lam s.
  foldl (lam sum. lam edge. addi sum edge.2) 0 s in

let initSol = (initTour, cost initTour) in

-- Neighbourhood: replace 2 edges by two others s.t. tour is still a
-- Hamiltonian circuit
let neighbours = lam g. lam state.
  let curSol = state.cur in
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
        error "Expected at most one edge between any two nodes"
    in res
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

let terminate = lam state. geqi state.iter 3 in
let printIter = lam state. print (join ["Iter: ", int2string state.iter, ", ",
                                              "Best: ", int2string state.inc.1, "\n"]) in
let initState = initSearchState initSol subi in

let minimizeTSP = minimize terminate printIter initState in
-- Custom termination condition
let minimizeTSP1 = lam terminate.
  minimize terminate printIter initState in
-- Custom start solution
let minimizeTSP2 = lam terminate. lam init.
  minimize terminate printIter init in

----------------------------
-- Set up meta-heuristics --
----------------------------

let randElem = lam seq.
  match seq with [] then None ()
  else Some (get seq (randIntU 0 (length seq))) in

-- Select a random best neighbour
let randomBest = lam ns. lam state.
  match ns with [] then None () else
  let costs = map cost ns in
  let minCost = min subi costs in
  let nsCosts = zipWith (lam n. lam c. (n,c)) ns costs in
  let minNs = filter (lam t. eqi t.1 minCost) nsCosts in
  randElem minNs
in

let metaRandBest = (Base {}, stepBase (neighbours g) randomBest) in

-- Select a random improving solution (steepest descent)
let randImproving = lam ns. lam state.
  match ns with [] then None () else
  let curCost = state.cur.1 in
  let nsCosts = map (lam n. (n, cost n)) ns in
  let improvingNs = filter (lam t. lti t.1 curCost) nsCosts in
  randElem improvingNs in

let metaSteepDesc = (Base {}, stepBase (neighbours g) randImproving) in

-- Simulated annealing
let randSol = lam ns. lam state.
  match ns with [] then None () else
  let nRand = get ns (randIntU 0 (length ns)) in
  Some (nRand, cost nRand)
in

let decayFunc = lam temp. lam state.
  mulf temp 0.95
in

let saState = SimulatedAnnealing {temp = 100.0, decayFunc = decayFunc} in
let metaSA = (saState, stepSA (neighbours g) randSol) in

-- Tabu search
let toursEq = lam t1. lam t2.
  setEqual (digraphEdgeEq g) t1 t2 in

let tabuState = TabuSearch {tabu = [initTour],
                            isTabu = lam tour. lam tabu. any (toursEq tour) tabu,
                            tabuAdd = lam assign. lam tabu. cons assign tabu,
                            tabuConvert = lam sol. sol.0} in
let metaTabu = (tabuState, stepTabu (neighbours g) randomBest) in

-----------------------
-- Solve the problem --
-----------------------

let _ = print "Choose a random best solution:\n" in
let _ = printIter initState in
let r = minimizeTSP1 (lam st. geqi st.iter 50) metaRandBest in

let sstate = r.0 in
utest sstate.iter with 50 in
utest sstate.inc.1 with 251 in -- optimum
utest sstate.stuck with false in

let _ = print "Steepest descent:\n" in
let _ = printIter initState in
let r = minimizeTSP1 (lam st. geqi st.iter 100) metaSteepDesc in

let sstate = r.0 in
utest sstate.inc.1 with 251 in
utest sstate.stuck with true in

let _ = print "Simulated annealing:\n" in
let _ = printIter initState in
let r = minimizeTSP metaSA in

let sstate = r.0 in
let mstate = match r.1 with SimulatedAnnealing s then s else error "Not a SimulatedAnnealing" in
utest sstate.iter with 3 in
utest sstate.stuck with false in
utest mstate.temp with mulf 0.95 (mulf 0.95 (mulf 0.95 100.0)) in

let _ = print "Tabu search:\n" in
let _ = printIter initState in
let r = minimizeTSP metaTabu in

let sstate = r.0 in
let mstate = match r.1 with TabuSearch s then s else error "Not a TabuSearch" in
utest sstate.iter with 3 in
utest sstate.stuck with false in
utest length (mstate.tabu) with 4 in
utest mstate.isTabu initTour mstate.tabu with true in
utest mstate.isTabu sstate.cur.0 mstate.tabu with true in
utest mstate.isTabu sstate.inc.0 mstate.tabu with true in

-- Switch between meta-heuristics during search
let _ = print "Start with tabu search:\n" in
let _ = printIter initState in
let r = minimizeTSP2 (lam state. geqi state.iter 5) initState metaTabu in
let _ = print "Switch to simulated annealing:\n" in
let r = minimizeTSP2 (lam state. geqi state.iter 10) r.0 metaSA in

------------------------------------
-- Design a custom meta heuristic --
------------------------------------

con FooMetaState : {foo : Int} -> MetaState v c in

let fooStep : StepFun = lam state. lam mstate.
  match mstate with FooMetaState r then
    (Some state.cur, FooMetaState {r with foo = addi 1 r.foo})
  else "fooStep intended for foo meta heuristic only" in

let metaHeurFoo = (FooMetaState {foo = 0}, fooStep) in

let _ = print "Foo search:\n" in
let _ = printIter initState in
let r = minimizeTSP metaHeurFoo in

let fooVal = match r.1 with FooMetaState s then s.foo else error "Not a FooMetaState" in
utest fooVal with (r.0).iter in
utest (r.0).inc with initSol in

()
