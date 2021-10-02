
include "seq.mc"

-- Function stuff
let identity = lam x. x
let const = lam x. lam. x
let apply = lam f. lam x. f x
let compose = lam f. lam g. lam x. f (g x)
let curry = lam f. lam x. lam y. f(x, y)
let uncurry = lam f. lam t : (a, b). f t.0 t.1
let flip = lam f. lam x. lam y. f y x

-- Printing stuff
let printLn = lam s. print (concat s "\n"); flushStdout ()

let dprintLn = lam x. dprint x; printLn ""


recursive
  let fix = lam f. lam e. f (fix f) e
end

-- Fixpoint computation for mutual recursion. Thanks Oleg Kiselyov!
-- (http://okmij.org/ftp/Computation/fixed-point-combinators.html)
let fixMutual =
  lam l.
    let l = map (lam li. (li,)) l in
    fix (lam self. lam l. map (lam li : {#label"0": a -> b -> c}. lam x. li.0 (self l) x) l) l


mexpr

utest apply identity 42 with identity 42 using eqi in
utest apply (compose identity (apply identity)) 42 with 42 in

let sum_tuple = lam t : (Int, Int). addi t.0 t.1 in

utest (curry sum_tuple) 3 2 with 5 in
utest (uncurry addi) (3,2) with 5 in
utest curry (uncurry addi) 3 2 with (uncurry (curry sum_tuple)) (3,2) using eqi in
()
