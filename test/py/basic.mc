-- We have no equality checks for Python values at the moment.
-- This only checks that the intrinsics are available and interpretable.

mexpr

let builtins = pyimport "builtins" in
let x = [1, 2, 3, 4, 5] in
let sum_x = pycall builtins "sum" (x,) in
utest sum_x with sum_x in
()
