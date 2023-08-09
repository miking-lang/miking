include "common.mc" -- printLn
mexpr
let addOne : Float -> Float = lam x. addf x 1.0 in

-- Regular function application
let a = addOne 25.0 in

-- Accelerated function application, running on the GPU
let b = accelerate (head (map addOne [25.0])) in

utest a with b in
()
