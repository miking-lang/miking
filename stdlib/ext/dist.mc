

include "seq.mc"
include "string.mc"

-- gaussianSample mu sigma
external gaussianSample ! : Float -> Float -> Float


mexpr


let str = join [
"gaussianSample: ", float2string (gaussianSample 3. 0.5), "\n"
] in

print str;

utest gti (length str) 0 with true in

()
