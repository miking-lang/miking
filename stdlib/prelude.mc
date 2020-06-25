-- Includes to be re-exported
include "seq.mc"
include "option.mc"


-- Function stuff
let identity = lam x. x
let const = lam x. lam _. x
let apply = lam f. lam x. f x
let compose = lam f. lam g. lam x. f (g x)
let curry = lam f. lam x. lam y. f(x, y)
let uncurry = lam f. lam t. f t.0 t.1

recursive
  let fix = lam f. lam e. f (fix f) e
end

-- Fixpoint computation for mutual recursion. Thanks Oleg Kiselyov!
-- (http://okmij.org/ftp/Computation/fixed-point-combinators.html)
let fix_mutual =
  lam l. fix (lam self. lam l. map (lam li. lam x. li (self l) x) l) l

-- Printing stuff
let printLn = lam s. print (concat s "\n")

mexpr

utest apply identity 42 with identity 42 in
utest apply (compose identity (apply identity)) 42 with 42 in

let sum_tuple = lam t. addi t.0 t.1 in

utest (curry sum_tuple) 3 2 with 5 in
utest (uncurry addi) (3,2) with 5 in
utest curry (uncurry addi) 3 2 with (uncurry (curry sum_tuple)) (3,2) in
()
