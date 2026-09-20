-- A variant type with 20 constructors, matched via one flat chain of
-- `match`/`else match` on a single scrutinee, at a scale `tree-pattern.mc`'s
-- 2-constructor type never reaches.
--
-- Exercises: `con`/`TmConApp` across 20 constructors and `PatCon` dispatch
-- through a single 20-arm chain on one target variable. `eval-fast.mc`'s
-- `MatchEvalFEagerPatConMap` only builds its constructor -> branch dispatch
-- map once a chain has at least `minPatConChain` (5) arms on the same
-- variable; below that it falls back to a linear tag-compare per arm. This
-- chain comfortably crosses that threshold, so it exercises the map-based
-- dispatch path instead of the fallback.
--
-- Scales linearly in `scale` (loop iterations); each iteration builds one
-- value cycling through all 20 constructors and dispatches it through the
-- full 20-arm match chain.

mexpr

let scale = 800000 in -- SCALE

type V in
con V0 : Int -> V in
con V1 : Int -> V in
con V2 : Int -> V in
con V3 : Int -> V in
con V4 : Int -> V in
con V5 : Int -> V in
con V6 : Int -> V in
con V7 : Int -> V in
con V8 : Int -> V in
con V9 : Int -> V in
con V10 : Int -> V in
con V11 : Int -> V in
con V12 : Int -> V in
con V13 : Int -> V in
con V14 : Int -> V in
con V15 : Int -> V in
con V16 : Int -> V in
con V17 : Int -> V in
con V18 : Int -> V in
con V19 : Int -> V in

let mkVariant = lam k. lam x.
  if eqi k 0 then V0 x
  else if eqi k 1 then V1 x
  else if eqi k 2 then V2 x
  else if eqi k 3 then V3 x
  else if eqi k 4 then V4 x
  else if eqi k 5 then V5 x
  else if eqi k 6 then V6 x
  else if eqi k 7 then V7 x
  else if eqi k 8 then V8 x
  else if eqi k 9 then V9 x
  else if eqi k 10 then V10 x
  else if eqi k 11 then V11 x
  else if eqi k 12 then V12 x
  else if eqi k 13 then V13 x
  else if eqi k 14 then V14 x
  else if eqi k 15 then V15 x
  else if eqi k 16 then V16 x
  else if eqi k 17 then V17 x
  else if eqi k 18 then V18 x
  else V19 x
in

let classify = lam v.
  match v with V0 x then addi x 0
  else match v with V1 x then addi x 1
  else match v with V2 x then addi x 2
  else match v with V3 x then addi x 3
  else match v with V4 x then addi x 4
  else match v with V5 x then addi x 5
  else match v with V6 x then addi x 6
  else match v with V7 x then addi x 7
  else match v with V8 x then addi x 8
  else match v with V9 x then addi x 9
  else match v with V10 x then addi x 10
  else match v with V11 x then addi x 11
  else match v with V12 x then addi x 12
  else match v with V13 x then addi x 13
  else match v with V14 x then addi x 14
  else match v with V15 x then addi x 15
  else match v with V16 x then addi x 16
  else match v with V17 x then addi x 17
  else match v with V18 x then addi x 18
  else match v with V19 x then addi x 19
  else never
in

recursive let loop = lam i. lam acc.
  if geqi i scale then acc
  else
    let v = mkVariant (modi i 20) i in
    let r = classify v in
    loop (addi i 1) (modi (addi acc r) 1000003)
in

exit (modi (loop 0 0) 251)
