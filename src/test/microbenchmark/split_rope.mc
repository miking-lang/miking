
include "benchmarkcommon.mc"

mexpr

recursive let sum = lam acc. lam s.
  if null s then acc
  else
    let h = head s in
    let t = tail s in
    sum (addi acc h) t
in

let s = create 1000 (lam i. i) in
bc_repeat (lam. sum 0 s)
