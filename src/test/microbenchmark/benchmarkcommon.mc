
include "string.mc"

recursive
  let bc_work : all a. (() -> a) -> Int -> () = lam f. lam n.
    if eqi n 0 then
      ()
    else
      f();
      bc_work f (subi n 1)
end

let bc_repeat = lam f. bc_work f (string2int (get argv 1))
