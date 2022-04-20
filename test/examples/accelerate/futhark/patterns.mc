-- Example showing the implicit discovery of some parallel patterns by the
-- compiler, and also the explicit use of parallel pattern keywords.

include "seq.mc" -- eqSeq

-- This recursive function will be translated into a fold.
recursive let foldAdd : Int -> [Int] -> Int = lam acc. lam s.
  match s with [h] ++ t then
    foldAdd (addi acc h) t
  else acc
end

mexpr

let s : [Int] = create 100 (lam i. i) in

-- Any use of the map intrinsic, within an accelerate expression, will be
-- translated into a parallel map.
let s1 : [Int] = accelerate (map (muli 2) s) in

-- If used outside accelerate, it becomes a sequential map
let s2 : [Int] = map (muli 2) s in

(if eqSeq eqi s1 s2 then print "map OK\n" else error "map failed");

-- The initial accumulator value we pass here is 0. This is the neutral element
-- of the addi function, which is the function applied on each element.
-- Therefore, this fold will be translated into a parallel reduce term.
let tot1 : Int = accelerate (foldAdd 0 s) in

-- We can also explicitly make use of the parallelReduce keyword to get the
-- same effect.
let tot2 : Int = accelerate (parallelReduce addi 0 s) in

(if eqi tot1 tot2 then print "reduce OK\n" else error "reduce failed");

()
