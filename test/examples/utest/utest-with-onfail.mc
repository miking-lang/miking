include "string.mc"

mexpr

let eq = lam l. lam r. eqi 0 (string2int r) in
let toString = lam l. lam r.
  lam l. lam r.
    join ["left hand: ", int2string l, ", right hand: \"", r, "\""]
in

-- FAILING TESTS

-- Utest with default equality function and onfail function
utest 0 with 1 in

-- Utest with custom equality function
utest 0 with "1" using eq in

-- Utest with custom equality function and custom onfail function
utest 0 with "1" using eq else toString in

-- PASSING TESTS

-- Utest with default equality function and onfail function
utest 0 with 0 in

-- Utest with custom equality function
utest 0 with "0" using eq in

-- Utest with custom equality function and custom onfail function
utest 0 with "0" using eq else toString in

()
