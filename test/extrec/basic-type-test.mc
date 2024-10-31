include "basic-types.mc"

mexpr
let x = Some 10 in 
(match x with Some y 
 then utest y with 10 in ()
 else utest false with true in ())