include "string.mc"
include "common.mc"

recursive let work: all a. (() -> a) -> Int -> a -> a = lam f. lam n. lam prev.
  if lti n 1 then prev else work f (subi n 1) (f ())
end

let repeat: all a. (() -> a) -> a = lam f. work f (subi (string2int (get argv 1)) 1) (f ())
