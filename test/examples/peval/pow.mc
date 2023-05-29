include "common.mc"
include "string.mc"

mexpr

recursive let pow = lam n. lam x.
  if eqi n 0 then 1
  else
    if eqi (modi n 2) 0 then
      let r = pow (divi n 2) x in
      muli r r
    else
      let r = pow (subi n 1) x in
      muli x r
in

let x = pow 2 3 in

let pow2 = specialize (pow 2) in

let z = pow2 3 in

printLn (int2string z)
