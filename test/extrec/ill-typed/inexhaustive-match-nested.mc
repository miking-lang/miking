include "../sum-contraction-inferred-types.mc"

mexpr
use SugarArith in 

let incr = TmIncr {TmIncrType of e = TmInt {TmIntType of val = 10}} in 

let expr = TmAdd {TmAddType of lhs = incr, 
                               rhs = TmInt {TmIntType of val = 12}} in 

print "eval : ";
print "\n";
print "expr : ";
print "\n";
utest eval expr with 11 in 
()