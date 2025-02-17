include "../sum-contraction-inferred-types.mc"

mexpr
use SugarArith in 

let expr = TmIncr {TmIncrType of e = TmInt {TmIntType of val = 10}} in 

utest eval expr with 11 in 
()