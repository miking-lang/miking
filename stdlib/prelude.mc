-- Includes to be re-exported
include "seq.mc"

let id = lam x. x
let apply = lam f. lam x. f x
let compose = lam f. lam g. lam x. f (g x)
let curry = lam f. lam x. lam y. f(x, y)
let uncurry = lam f. lam t. f t.0 t.1
main

utest apply id 42 with id 42 in
utest apply (compose id (apply id)) 42 with 42 in
()