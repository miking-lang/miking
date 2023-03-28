
include "string.mc"

mexpr

let foo =
  print "During runtime\n"
in

let bar =
  let x = addi 3 2 in
  print "In bar: "; print (int2string x); print "\n";
  x
in
let a = lam x1.
  (prerun
     (print "prerun A\n"; print (int2string (addi bar 10)); print "\n"); 2) in

let b = lam x2.
   (prerun
     (print "prerun B\n"; print (int2string (addi bar 20)); print "\n"); 3) in

print "Final: "; print (int2string bar); print "\n"

print "hi\n"
