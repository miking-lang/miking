

include "seq.mc"
include "string.mc"

-- gaussianSample mu sigma
external gaussianSample ! : Float -> Float -> Float

-- gaussianPDF x mu sigma
external gaussianPDF : Float -> Float -> Float -> Float

-- gaussianLogPDF x mu sigma
external gaussianLogPDF : Float -> Float -> Float -> Float



-- bernoulliSample p
external bernoulliSample ! : Float -> Int

-- bernoulliPDF x p
external bernoulliPDF : Int -> Float -> Float

-- bernoulliPDF x p
external bernoulliLogPDF : Int -> Float -> Float




mexpr


let str = join [
"gaussianSample: ", float2string (gaussianSample 3. 0.5), "\n",
"gaussianPDF: ", float2string (gaussianPDF 2. 3. 0.5), "\n",
"gaussianLogPDF: ", float2string (gaussianLogPDF 2. 3. 0.5), "\n",

"bernoulliSample: ", int2string (bernoulliSample 0.7), "\n",
"bernoulliPDF: ", float2string (bernoulliPDF 0 0.7), "\n",
"bernoulliLogPDF: ", float2string (bernoulliLogPDF 0 0.7), "\n",
"\n"
] in

print str;

utest gti (length str) 0 with true in

()
