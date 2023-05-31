-- Implementation of the Hungarian algorithm using slack variables for maximal
-- matching on weighted bipartite graph G=(U,V,E). Implementation based off
-- https://gist.github.com/KartikTalwar/3158534

include "math.mc"
include "tensor.mc"
include "common.mc"

type Slack = {
  val : Int,                    -- value of slack
  u   : Int,                    -- u in U associated with this slack
  v   : Int                     -- v in V associated with this slack
}

let slackToString = lam slack : Slack.
  match slack with {val = val, u = u, v = v} in
  join [
    "{ val = ", int2string val,
    ", u = ", int2string u,
    ", v = ", int2string v, "}"
  ]

-- Find a maximum weight matching on weighted bipartite graph encoded by weight
-- matrix w. This implementation uses slack variables to ensure sub O(n^3) time
-- complexity.
let maxmatchHungarian = lam w : Tensor[Int].

  -- For brevity
  let tget = tensorGetExn in
  let tset = tensorSetExn in
  let tcreate = tensorCreateDense in

  if or (neqi (tensorRank w) 2) (not (tensorDimsEqual w)) then
    error "Expected square weight matrix"
  else
    ------------------
    -- Preliminares --
    ------------------

    -- problem size
    let n : Int = head (tensorShape w) in

    -- labels for U
    let lus : Tensor[Int] = tcreate [n] (lam. 0) in

    -- We assign these feasable labels, e. g. lu[u] + lv[v] => w[u][v] for all
    -- v in V, u in U
    tensorMapiInplace
      (lam i. lam.
        optionGetOrElse
          (lam. error "maxmatchHungarian: Invalid input")
          (tensorMax subi (tensorSliceExn w i)))
      lus;

    -- labels for V
    let lvs : Tensor[Int] = tcreate [n] (lam. 0) in

    -- matched incidence vector of U, (-1) means unmatched
    let mus : Tensor[Int] = tcreate [n] (lam. negi 1) in

    -- matched incidence vector of V, (-1) means unmatched
    let mvs : Tensor[Int] = tcreate [n] (lam. negi 1) in

    -- u's in the vertex cover
    let ss : Ref [Int] = ref [] in

    -- V's vertices enumerated
    let vs : [Int] = range 0 n 1 in

    -- v's in the vertex cover
    let ts : Tensor[Bool] = tcreate [n] (lam. false) in

    -- slack variables
    let slacks : Tensor[Slack] =
      tcreate [n] (lam. {val = negi 1, u = negi 1, v = negi 1})
    in

    -- predecessors of v in V
    let preds : Tensor[Int] = tcreate [n] (lam. negi 1) in

    ------------------------------------
    -- Helper functions and functions --
    ------------------------------------

    let cmpSlack = lam l : Slack. lam r : Slack. subi l.val r.val in

    let isMatch = neqi (negi 1) in
    let isPerfectMatch = lam. tensorAll isMatch mus in

    -- lu[u] + lv[v] - w[u][v]
    let slackVal = lam u. lam v.
      subi (addi (tget lus [u]) (tget lvs [v])) (tget w [u, v])
    in

    -- T <- {}
    let emptyT = lam. tensorMapInplace (lam. false) ts in

    -- v in T
    let memT = lam v. tget ts [v] in

    -- T <- T union {v}
    let insertT = lam v. tset ts [v] true in

    -- S <- {}
    let emptyS = lam. modref ss [] in

    -- S <- S union {u}
    let insertS = lam u. modref ss (cons u (deref ss)) in

    -- all v not in T
    let vsNotInT = lam. filter (lam v. not (memT v)) vs in

    -- assigns u with v
    let assign = lam u. lam v. tset mus [u] v; tset mvs [v] u in

    -- Finds unmatched u in U.
    let findUnmatchedU = lam.
      let u = tensorIndex (lam x. not (isMatch x)) mus in
      match u with Some ([u]) then u
      else match u with None _ then error "All nodes are covered"
      else match u with Some _ then error "impossible"
      else never
    in

    -- Debug state
    let debugShowState = lam.
      printLn "===";
      printLn "lus: ";
      printLn (tensor2string int2string lus);
      printLn "lvs: ";
      printLn (tensor2string int2string lvs);
      printLn "mus: ";
      printLn (tensor2string int2string mus);
      printLn "mvs: ";
      printLn (tensor2string int2string mvs);
      printLn "ss: ";
      printLn (strJoin " ," (map int2string (deref ss)));
      printLn "ts: ";
      printLn (tensor2string (lam x. if x then "true" else "false") ts);
      printLn "slacks: ";
      printLn (tensor2string slackToString slacks);
      printLn "preds: ";
      printLn (tensor2string int2string preds);
      ()
    in

    --------------------
    -- Main Algorithm --
    --------------------

    -- Improve labels and adjusts slack with delta.
    let improveLabels = lam delta.
      iter (lam u. tset lus [u] (subi (tget lus [u]) delta)) (deref ss);

      iter
        (lam v.
          if memT v then tset lvs [v] (addi (tget lvs [v]) delta)
          else
            let s : Slack = tget slacks [v] in
            tset slacks [v] { s with val = subi s.val delta } )
        vs
    in

    -- Improves matching by flipping edges in the augmenting path ending in v.
    recursive let improveMatching = lam v.
        let u = tget preds [v] in
        let v1 = tget mus [u] in
        assign u v;
        if not (isMatch v1) then ()
        else improveMatching v1
    in

    -- Updates slacks according to slackv <- min slackv (slack u v) for v not
    -- in T. Applied everytime a new u is inserted in S.
    let updateSlacks = lam u.
      let f = lam v.
        let s : Slack = tget slacks [v] in
        let newVal = slackVal u v in
        if gti s.val newVal then
          tset slacks [v] { { s with val = newVal } with u = u }
        else ()
      in
      iter f (vsNotInT ())
    in

    -- Search for augmenting paths in the equality graph, possibly updating
    -- labels along the way.
    recursive let augment = lam.
      let s : Slack =
        -- min slack over v's not in T
        minOrElse (lam. error "undefined")
                  cmpSlack
                  (tensorFilter (lam s : Slack. not (memT s.v)) slacks)
      in

      -- Since we can only expand the matching in the equality graph,
      -- e.g. slack = 0, to ensure a maximal matching, we might have to improve
      -- the labels.
      (if gti s.val 0 then improveLabels s.val else ());

      -- Add minimal node v to T and remember its predecessor.
      insertT s.v;
      tset preds [s.v] s.u;

      let u1 = tget mvs [s.v] in
      if not (isMatch u1) then
        improveMatching s.v   -- v is unmatched and we have an augmenting path.
      else
        insertS u1;
        updateSlacks u1;
        augment ()              -- update S, slacks, and continue the search.
    in

    recursive let work = lam k.
      if isPerfectMatch () then
        { incidenceU = mus
        , incidenceV = mvs
        , weight = addi (tensorFold addi 0 lus) (tensorFold addi 0 lvs) }
      -- We should find a complete matching in at most n steps.
      else if gti k n then error "Failed to find maximal matching"
      else
        -- Find unmatched u in U.
        let u0 = findUnmatchedU () in

        -- Set Initial slack variables.
        iter (lam v. tset slacks [v] { val = slackVal u0 v, v = v, u = u0 }) vs;

        -- T <- {}
        emptyT ();

        -- S <- {u0}
        emptyS ();
        insertS u0;

        augment ();
        work (addi k 1)
    in
    work 0

-- Maximum-weight matching on the bipartite graph G=(U,V,E) encoded by the
-- weight-incidence matrix w. Incidence of U and V after assignment is given by
-- incidenceU and incidenceV. The total weight of the assignment is given by
-- weight.
let maxmatchFindMatch
  : Tensor[Int] -> {
      incidenceU : Tensor[Int],
      incidenceV : Tensor[Int],
      weight : Int
    } =
  lam w. maxmatchHungarian w

mexpr

-- let w = tensorOfSeqExn tcreate [1, 1] [1] in

-- utest (maxmatchHungarian w).weight with 1 in

let w =
  tensorOfSeqExn tensorCreateDense [3, 3]
    [7, 5, 11
    ,5, 4, 1
    ,9, 3, 2]
in

utest (maxmatchHungarian w).weight with 24 in


let w =
  tensorOfSeqExn tensorCreateDense [2, 2]
    [1, 2
    ,1, 3]
in

utest (maxmatchHungarian w).weight with 4 in


let neginf = negi 100000 in


let w = tensorOfSeqExn tensorCreateDense [1, 1] [neginf] in

utest (maxmatchHungarian w).weight with neginf in


let w =
  tensorOfSeqExn tensorCreateDense [3, 3]
    [2     , neginf, 0
    ,neginf, 2     , 0
    ,0     , 0     , neginf]
in

utest (maxmatchHungarian w).weight with 2 in


let w =
  tensorOfSeqExn tensorCreateDense [3, 3]
    [1     , 0     , neginf
    ,neginf, 1     , 0
    ,0     , neginf, neginf]
in

utest (maxmatchHungarian w).weight with 0 in


let w =
  tensorOfSeqExn tensorCreateDense [4, 4]
    [0, 0     , neginf, neginf
    ,0, 0     , 0     , neginf
    ,0, neginf, 1     , 0
    ,2, 2     , 2     , 1]
in

utest (maxmatchHungarian w).weight with 2 in

()
