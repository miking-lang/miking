include "common.mc" -- printLn
mexpr
let addOne : Float -> Float = lam x. addf x 1.0 in

-- Regular function application
printLn (float2string (addOne 25.0));

-- Accelerated function application, running on the GPU
printLn (float2string (accelerate (addOne 25.0)))
