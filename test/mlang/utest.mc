-- Top-level utest with using function
include "bool.mc"

utest 15 with 15 using eqi
utest 12 with 7 using gti
utest addi 1 5 with addi 4 2 using lam x. lam y. not (lti x y)


-- Utest where one of the compared values is under a type variable
-- (here `a = {foo : Int}`)
type Option a
con Some : a -> Option a
con None : () -> Option a

utest Some {foo = 1} with Some {foo = 1}
