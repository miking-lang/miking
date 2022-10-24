mexpr
let r = {
  a = tensorCreateCArrayInt [5] (lam. 0),
  b = tensorCreateCArrayFloat [2] (lam. 0.0)
} in
accelerate (
  loop 1 (lam.
    tensorSetExn r.a [3] 7;
    tensorSetExn r.b [1] 2.5;
    tensorSetExn r.b [0] 1.25)
);
let x = tensorGetExn r.a [3] in
let y = tensorGetExn r.b [1] in
if eqf (addf (int2float x) y) 9.5 then
  print "OK\n"
else error "Unexpected result"
