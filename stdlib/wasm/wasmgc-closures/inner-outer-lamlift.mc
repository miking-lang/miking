-- mexpr 
-- let inner = lam x. lam a. lam y. addi (addi x a) y in
-- let outer = lam x. 
--     let a = addi x 1 in
--     inner x a
-- in
-- utest outer 1 2 with 5 in ()

mexpr 
let inner2 = lam env. lam y. addi (addi env.0 env.1) y in
let inner1 = lam env. lam a. inner2 (env.0, a) in
let inner = lam x. inner1 (x) in
let outer = lam x. 
    let a = addi x 1 in
    (inner x) in
utest outer 1 2 with 5 in ()

-- mexpr 
-- let g = addi 10 in
-- utest g 20 with 30 in ()
