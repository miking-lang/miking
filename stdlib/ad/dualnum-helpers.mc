include "dualnum-tree.mc"

let num = dualnumNum
let dnum = dualnumDNum
let genEpsilon = dualnumGenEpsilon

let num0 = num 0.
let num1 = num 1.
let num2 = num 2.
let num3 = num 3.
let num4 = num 4.
let num6 = num 6.
let num8 = num 8.
let num10 = num 10.

let e0 = genEpsilon ()
let e1 = genEpsilon ()
let e2 = genEpsilon ()
let e3 = genEpsilon ()

let dnum0 = dnum e0
let dnum1 = dnum e1
let dnum010 = dnum0 num1 num0
let dnum011 = dnum0 num1 num1
let dnum012 = dnum0 num1 num2
let dnum020 = dnum0 num2 num0
let dnum021 = dnum0 num2 num1
let dnum022 = dnum0 num2 num2
let dnum031 = dnum0 num3 num1
let dnum034 = dnum0 num3 num4
let dnum036 = dnum0 num3 num6
let dnum040 = dnum0 num4 num0
let dnum044 = dnum0 num4 num4
let dnum048 = dnum0 num4 num8
let dnum111 = dnum1 num1 num1
let dnum112 = dnum1 num1 num2
let dnum122 = dnum1 num2 num2
let dnum134 = dnum1 num3 num4
