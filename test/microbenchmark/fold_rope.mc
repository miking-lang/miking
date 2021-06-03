
include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"
include "fold.ml"

recursive
  let foldl = lam f. lam acc. lam seq.
  if null seq then acc
  else foldl f (f acc (head seq)) (tail seq)
end

mexpr

let foldf = lam n.
  foldl addi 0 (createRope n (lam i. i))
in

-- printLn (int2string (foldf n));

repeat (lam. foldf n)
