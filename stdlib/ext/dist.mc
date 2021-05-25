

include "seq.mc"
include "string.mc"

-- gaussianSample mu sigma
external gaussianSample ! : Float -> Float -> Float

-- gaussianPDF x mu sigma
external gaussianPDF : Float -> Float -> Float -> Float

-- gaussianLogPDF x mu sigma
external gaussianLogPDF : Float -> Float -> Float -> Float


mexpr


let str = join [
"gaussianSample: ", float2string (gaussianSample 3. 0.5), "\n",
"gaussianPDF: ", float2string (gaussianPDF 2. 3. 0.5), "\n",
"gaussianLogPDF: ", float2string (gaussianLogPDF 2. 3. 0.5), "\n",
"\n"
] in

print str;

utest gti (length str) 0 with true in

()
