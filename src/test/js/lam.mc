include "common.mc"

mexpr
    let f = lam x. lam y. addi (addi x (muli y 2)) 5 in
    let g = (f 3) in
    let h = (g 4) in
    -- print (int2string h)
    dprintLn h;
    dprintLn (f 3 4)
