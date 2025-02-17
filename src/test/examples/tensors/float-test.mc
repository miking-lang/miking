include "string.mc"

mexpr
let t = tensorCreateCArrayFloat [] (lam. 12.) in
print (float2string (tensorGetExn t []))
