-- Implementation of the Hungarian algorithm using slack variables for maximal
-- matching on weighted bipartite graph G=(U,V,E). Implementation based off
-- https://gist.github.com/KartikTalwar/3158534

include "prelude.mc"
include "matrix.mc"
include "math.mc"

type Slack = {
  val : Int,                    -- value of slack
  u   : Int,                    -- u in U associated with this slack
  v   : Int                     -- v in V associated with this slack
}

type State = {
  w      : [[Int]],             -- weight matrix
  n      : Int,                 -- problem size
  lus    : [Int],               -- labels for U
  lvs    : [Int],               -- labels for V
  mus    : [Int],               -- matched incidence vector of U, (-1) means unmatched
  mvs    : [Int],               -- matched incidence vector of V, (-1) means unmatched
  ss     : [Int],               -- u's in the vertex cover
  vs     : [Int],               -- V's vertices enumerated
  ts     : [Bool],              -- v's in the vertex cover
  slacks : [Slack],             -- slack variables
  preds  : [Int]                -- predecessors of v in V
}

-- Costructs initial state from weight-matrix w.
let preliminaries : [[Int]] -> State =
lam w.
  let d = matrixSize w in
  let n = d.0 in
  if neqi d.1 n then error "Expected square weight matrix"
  else
  let vs = unfoldr (lam a. if eqi a n then None () else Some (a, addi a 1)) 0 in
  let negv = makeSeq n (negi 1) in
  let zerov = makeSeq n 0 in
    {
      w = w,
      n = n,
      lus = map (max subi) w,   -- assign feasible labels, e.g.
      lvs = zerov,              -- lu[u] + lv[v] => w[u][v] for all v in V, u in U
      mus = negv,
      mvs = negv,
      ss = [],
      vs = vs,
      ts = makeSeq n false,
      slacks = [],
      preds = negv
    }

let debugShowState = lam state.
  let _ = printLn "===" in
  let _ = print "lus: " in
  let _ = dprint state.lus in
  let _ = print "lvs: " in
  let _ = dprint state.lvs in
  let _ = print "mus: " in
  let _ = dprint state.mus in
  let _ = print "mvs: " in
  let _ = dprint state.mvs in
  let _ = print "ss: " in
  let _ = dprint state.ss in
  let _ = print "ts: " in
  let _ = dprint state.ts in
  let _ = print "slacks: " in
  let _ = dprint state.slacks in
  let _ = print "preds: " in
  let _ = dprint state.preds in
  ()

------------------------------------------------------------
-- Helper functions and functions to manipulate the state --
------------------------------------------------------------

let cmpSlack = lam l. lam r. subi l.val r.val

let isMatch = lam x. neqi x (negi 1)
let isPerfectMatch = all isMatch

let findNonCovered = lam x.
  optionMapOrElse (index (lam x. not (isMatch x)) x)
                  (lam _. error "All nodes are covered")
                  identity

-- lu[u] + lv[v] - w[u][v]
let slackVal = lam u. lam v. lam state.
  subi (addi (get state.lus u) (get state.lvs v)) (matrixGet state.w u v)

-- T <- {}
let emptyT = lam state. {state with ts = makeSeq state.n false}

-- v in T
let memT = lam v. lam state. get state.ts v

-- T <- T union {v}
let insertT = lam v. lam state. {state with ts = set state.ts v true}

-- S <- {}
let emptyS = lam state. {state with ss = []}

-- S <- S union {u}
let insertS = lam u. lam state. {state with ss = cons u state.ss}

-- all v not in T
let vsNotInT = lam state. filter (lam v. not (memT v state)) state.vs

-- assigns u with v
let assign = lam u. lam v. lam state.
  {{state with mus = set state.mus u v} with mvs = set state.mvs v u}

let updateSlack = lam v. lam f. lam state.
  {state with slacks = set state.slacks v (f (get state.slacks v))}

let updateLu = lam u. lam f. lam state.
  {state with lus = set state.lus u (f (get state.lus u))}

let updateLv = lam v. lam f. lam state.
  {state with lvs = set state.lvs v (f (get state.lvs v))}

let updatePred = lam v. lam u. lam state.
  {state with preds = set state.preds v u}

--------------------
-- Main Algorithm --
--------------------

-- Improve labels and adjusts slack with delta.
let improveLabels = lam delta. lam state.
  let f = lam state. lam u. updateLu u (lam lu. subi lu delta) state in

  let g = lam state. lam v.
    if memT v state then updateLv v (lam lv. addi lv delta) state
    else updateSlack v (lam s. {s with val = subi s.val delta}) state
  in

  (compose (lam state. foldl f state state.ss)
           (lam state. foldl g state state.vs)) state

recursive
  -- Improves matching by flipping edges in the augmenting path ending in v.
  let improveMatching = lam v. lam state.
    let u = get state.preds v in
    let v1 = get state.mus u in
    let state = assign u v state in
    if not (isMatch v1) then state
    else improveMatching v1 state
end

-- Updates slacks according to slackv <- min slackv (slack u v) for v not in
-- T. Applied everytime a new u is inserted in S.
let updateSlacks = lam u. lam state.
  let f = lam state. lam v.
    let s = get state.slacks v in
    let newVal = slackVal u v state in
    if gti s.val newVal then
      updateSlack v (lam s. {{s with val = newVal} with u = u}) state
    else state
  in
  foldl f state (vsNotInT state)

recursive
  -- Search for augmenting paths in the equality graph, possibly updating
  -- labels along the way.
  let augment = lam state.
  let s =
    -- min slack over v's not in T
    min cmpSlack (filter (lam s. not (memT s.v state)) state.slacks)
  in

  -- Since we can only expand the matching in the equality graph, e.g. slack =
  -- 0, to ensure a maximal matching, we might have to improve the labels.
  let maybeImproveLabels = lam state.
    if gti s.val 0 then improveLabels s.val state
    else state
  in

  -- Add minimal node v to T and remember its predecessor.
  let state = updatePred s.v s.u (insertT s.v (maybeImproveLabels state)) in

  let u1 = get state.mvs s.v in
  if not (isMatch u1) then
    improveMatching s.v state   -- v is unmatched and we have an augmenting path.
  else
    augment (updateSlacks u1 (insertS u1 state)) -- update S, slacks, and continue the search.
end

let formatResult = lam state.
  { incidenceU = state.mus
  , incidenceV = state.mvs
  , weight = foldl1 addi (concat state.lus state.lvs) }

-- Find a maximum weight matching on weighted bipartite graph encoded by weight
-- matrix w. This implementation uses slack variables to ensure sub O(n^4) time
-- complexity.
let maxmatchHungarian = lam w.
  recursive let work = lam state. lam k.
    if isPerfectMatch state.mus then formatResult state
    -- We should find a complete matching in at most n steps.
    else if gti k state.n then error "Failed to find maximal matching"
    else
      let u0 = findNonCovered state.mus in -- Find unmatched u in U.
      let slacks0 =
        -- Initial slack variables.
        map (lam v. {val = slackVal u0 v state, v = v, u = u0}) state.vs
      in
      -- S <- {u} and T <- {}.
      let state = insertS u0 (emptyS (emptyT {state with slacks = slacks0})) in
      work (augment state) (addi k 1) -- Each application improves matching by one.
  in
  work (preliminaries w) 0


-- Maximum-weight matching on the bipartite graph G=(U,V,E) encoded by the
-- weight-incidence matrix w. Incidence of U and V after assignment is given by
-- incidenceU and incidenceV. The total weight of the assignment is given by
-- weight.
let maxmatchFindMatch : [[Int]] -> {incidenceU : Int, incidenceV : Int, weight : Int} =
lam w. maxmatchHungarian w

mexpr

let w = [[1]] in

utest (maxmatchHungarian w).weight with 1 in

let w = [[7, 5, 11],
         [5, 4, 1],
         [9, 3, 2]]
in

utest (maxmatchHungarian w).weight with 24 in


let w = [[1, 2],
         [1, 3]] in

utest (maxmatchHungarian w).weight with 4 in


let neginf = negi 100000 in


let w = [[neginf]] in

utest (maxmatchHungarian w).weight with neginf in


let w = [[2     , neginf, 0]
        ,[neginf, 2     , 0]
        ,[0     , 0     , neginf]]
in

utest (maxmatchHungarian w).weight with 2 in


let w = [[1     , 0     , neginf]
        ,[neginf, 1     , 0]
        ,[0     , neginf, neginf]]
in

utest (maxmatchHungarian w).weight with 0 in


let w = [[0, 0     , neginf, neginf]
        ,[0, 0     , 0     , neginf]
        ,[0, neginf, 1     , 0]
        ,[2, 2     , 2     , 1]]
in

utest (maxmatchHungarian w).weight with 2 in

()
