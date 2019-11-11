-- Includes to be re-exported
include "seq.mc"
include "option.mc"

-- Function stuff
let id = lam x. x
let const = lam x. lam _. x
let apply = lam f. lam x. f x
let compose = lam f. lam g. lam x. f (g x)
let curry = lam f. lam x. lam y. f(x, y)
let uncurry = lam f. lam t. f t.0 t.1

-- Printing stuff
let print_ln = lam s. print (concat s "\n")

main

utest apply id 42 with id 42 in
utest apply (compose id (apply id)) 42 with 42 in

let sum_tuple = lam t. addi t.0 t.1 in

utest (curry sum_tuple) 3 2 with 5 in
utest (uncurry addi) (3,2) with 5 in
utest curry (uncurry addi) 3 2 with (uncurry (curry sum_tuple)) (3,2) in
()