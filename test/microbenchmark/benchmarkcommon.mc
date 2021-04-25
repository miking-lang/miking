
include "string.mc"

recursive
  let work = lam f. lam n.
    if eqi n 0 then
      ()
    else
      f();
      work f (subi n 1) 
end

let repeat = lam f. work f (string2int (get argv 1))
