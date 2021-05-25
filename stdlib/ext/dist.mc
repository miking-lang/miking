

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

-- bernoulliLogPDF x p
external bernoulliLogPDF : Int -> Float -> Float



-- binomialSample p n
external binomialSample ! : Float -> Int -> Int

-- binomialPDF x p n
external binomialPDF : Int -> Float -> Int -> Float

-- binomialLogPDF x p n
external binomialLogPDF : Int -> Float -> Int -> Float




mexpr


let str = join [
"gaussianSample: ", float2string (gaussianSample 3. 0.5), "\n",
"gaussianPDF: ", float2string (gaussianPDF 2. 3. 0.5), "\n",
"gaussianLogPDF: ", float2string (gaussianLogPDF 2. 3. 0.5), "\n",
"\n",
"bernoulliSample: ", int2string (bernoulliSample 0.7), "\n",
"bernoulliPDF: ", float2string (bernoulliPDF 0 0.7), "\n",
"bernoulliLogPDF: ", float2string (bernoulliLogPDF 0 0.7), "\n",
"\n",
"binomialSample: ", int2string (binomialSample 0.7 3), "\n",
"binomialPDF: ", float2string (binomialPDF 0 0.7 3), "\n",
"binomialLogPDF: ", float2string (binomialLogPDF 0 0.7 3), "\n",
"\n"
] in

print str;

utest gti (length str) 0 with true in

()
