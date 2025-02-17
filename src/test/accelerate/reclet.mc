include "common.mc"
include "string.mc"

mexpr

recursive let fn = lam n.
  if lti n 0 then 0
  else
    let a = accelerate (seqLoopAcc 0 n (lam acc. lam i. addi acc i)) in
    addi a (fn (subi n 1))
in

let x = fn 4 in
utest x with 10 in
()
