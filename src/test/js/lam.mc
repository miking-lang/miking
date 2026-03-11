include "common.mc"
include "string.mc"

mexpr
    let f = lam x. lam y. addi (addi x (muli y 2)) 5 in
    let g = (f 3) in
    let h = (g 4) in
    printLn (int2string h);
    printLn (int2string (f 3 4))
