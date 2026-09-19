-- A balanced binary search tree built and folded via real `con`/`PatCon`
-- constructor pattern matching, not the closure-based encoding church-list.mc
-- needs to work around the lack of it.
--
-- Exercises: `con`/`TmConApp` (constructor application) and `PatCon`
-- (constructor pattern matching), now that `eval-fast.mc` supports the
-- latter directly. `Node`'s three-field payload is destructured through a
-- single `PatCon` whose subpattern is a tuple, so every visited node
-- exercises `PatCon` together with the tuple `PatRecord`, and every
-- traversal also exercises `PatCon`'s failure path at every `Leaf`.
--
-- Scales linearly in `scale` (tree size); the tree is built once, balanced by
-- construction, and then folded three times (sum, count, max).

mexpr

let scale = 200000 in -- SCALE

type Tree in
con Leaf : () -> Tree in
con Node : (Int, Tree, Tree) -> Tree in

recursive let build = lam lo. lam hi.
  if gti lo hi then Leaf ()
  else
    let mid = divi (addi lo hi) 2 in
    Node (mid, build lo (subi mid 1), build (addi mid 1) hi)
in

recursive let sumTree = lam t.
  match t with Leaf _ then 0
  else match t with Node (x, l, r) then
    modi (addi x (addi (sumTree l) (sumTree r))) 1000003
  else never
in

recursive let countTree = lam t.
  match t with Leaf _ then 0
  else match t with Node (_, l, r) then
    addi 1 (addi (countTree l) (countTree r))
  else never
in

recursive let maxTree = lam t.
  match t with Leaf _ then 0
  else match t with Node (x, l, r) then
    let lm = maxTree l in
    let rm = maxTree r in
    let m = if gti lm x then lm else x in
    if gti rm m then rm else m
  else never
in

let t = build 1 scale in

let s = sumTree t in
let c = countTree t in
let m = maxTree t in

exit (modi (addi s (addi c m)) 251)
