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
  luv    : [Int],               -- labels for V
  uM     : [Int],               -- match incidence vector of U, (-1) means unmatched
  vM     : [Int],               -- match incidence vector of V, (-1) means unmatched
  ss     : [Int],               -- represents S set, holding candidates in U of augmenting path
  vs     : [Int],               -- V's vertices enumerated
  ts     : [Bool],              -- represents T set, holding candidates in V of augmenting path
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
      uM = negv,
      vM = negv,
      ss = [],
      vs = vs,
      ts = makeSeq n false,
      slacks = [],
      preds = negv
    }

let debugShowState = lam state.
  let _ = printLn "===" in
  let _ = print "lus: " in
  let _ = debugShow state.lus in
  let _ = print "lvs: " in
  let _ = debugShow state.lvs in
  let _ = print "uM: " in
  let _ = debugShow state.uM in
  let _ = print "vM: " in
  let _ = debugShow state.vM in
  let _ = print "ss: " in
  let _ = debugShow state.ss in
  let _ = print "ts: " in
  let _ = debugShow state.ts in
  let _ = print "slacks: " in
  let _ = debugShow state.slacks in
  let _ = print "preds: " in
  let _ = debugShow state.preds in
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

-- match u with v
let doMatch = lam u. lam v. lam state.
  {{state with uM = set state.uM u v} with vM = set state.vM v u}

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
    let v1 = get state.uM u in
    let state = doMatch u v state in
    if not (isMatch v1) then state
    else improveMatching v1 state
end

-- Updates slacks according to slackv = min slackv (slack u v) for v not in
-- T. Called everytime a new u is inserted in S.
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
  -- 0, to ensure a maximal matching, we might have to update the labels.
  let maybeImproveLabels = lam state.
    if gti s.val 0 then improveLabels s.val state
    else state
  in

  -- Add minimal node v to T and remember its predecessor.
  let state = updatePred s.v s.u (insertT s.v (maybeImproveLabels state)) in

  let u1 = get state.vM s.v in
  if not (isMatch u1) then
    improveMatching s.v state   -- v is unmatched and we have an augmenting path.
  else
    augment (updateSlacks u1 (insertS u1 state)) -- update slacks and continue the search.
end

let formatResult = lam state.
  {uM = state.uM, vM = state.vM, val = foldl1 addi (concat state.lus state.lvs)}

-- Find a maximum weight matching on weighted bipartite graph encoded by weight
-- matrix w. This implementation uses slack variables to ensure sub O(n^4) time
-- complexity.
let maxmatchHungarian = lam w.
  recursive let work = lam state. lam k.
    if isPerfectMatch state.uM then formatResult state
    -- We should find complete matching in at most n steps.
    else if gti k state.n then error "Failed to find maximal matching"
    else
      let u0 = findNonCovered state.uM in -- Find unmatched u in U.
      let slacks0 =
        -- Initial slack variables.
        map (lam v. {val = slackVal u0 v state, v = v, u = u0}) state.vs
      in
      -- S = {u} and T = {}.
      let state = insertS u0 (emptyS (emptyT {state with slacks = slacks0})) in
      work (augment state) (addi k 1) -- Each application improves matching by one.
  in
  work (preliminaries w) 0


-- Maximum weight matching on the bipartite graph G=(U,V,E) encoded by the
-- weight incidence matrix w. Incidence of U and V after Matching is given by uM
-- and vM, respectively, and val holds the value of the matching.
let maxmatchFindMatch : [[Int]] -> {uM : Int, vM : Int, val : Int} =
lam w. maxmatchHungarian w

mexpr

let w = [[7, 5, 11],
         [5, 4, 1],
         [9, 3, 2]]
in

utest (maxmatchHungarian w).val with 24 in

let w = [[1, 2],
         [1, 3]] in

utest (maxmatchHungarian w).val with 4 in

()
