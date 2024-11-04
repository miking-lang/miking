
include "seq.mc"

-- Function stuff
let identity = lam x. x
let const = lam x. lam. x
let apply = lam f. lam x. f x
let compose = lam f. lam g. lam x. f (g x)
let curry = lam f. lam x. lam y. f(x, y)
let uncurry : all a. all b. all c. (a -> b -> c) -> (a, b) -> c =
  lam f. lam t : (a, b). f t.0 t.1
let flip = lam f. lam x. lam y. f y x

-- Printing stuff
let printLn = lam s. print (concat s "\n"); flushStdout ()
let printErrorLn = lam s. printError (concat s "\n"); flushStderr ()
let printSeq = lam s. print (join s)
let printSeqLn = lam s. printSeq s; print "\n"; flushStdout ()
let dprintLn = lam x. dprint x; printLn ""

recursive
  let fix : all a. all b. ((a -> b) -> a -> b) -> a -> b =
    lam f. lam e. f (fix f) e
end

-- Function repetition (for side-effects)
let repeat : (() -> ()) -> Int -> () = lam f. lam n.
  recursive let rec = lam n.
    if leqi n 0 then () else (f (); rec (subi n 1))
  in rec n

-- Function repetition (for side-effects)
let repeati : (Int -> ()) -> Int -> () = lam f. lam n.
  recursive let rec = lam i.
    if geqi i n then () else (f i; rec (addi i 1))
  in rec 0

-- Fixpoint computation for mutual recursion. Thanks Oleg Kiselyov!
-- (http://okmij.org/ftp/Computation/fixed-point-combinators.html)
let fixMutual : all a. all b. [[a -> b] -> a -> b] -> [a -> b] =
  lam l.
    let l = map (lam li. (li,)) l in
    fix (lam self. lam l.
      map (lam li : {#label"0" : [a -> b] -> a -> b}. lam x. li.0 (self l) x) l) l


mexpr

utest apply identity 42 with identity 42 using eqi in
utest apply (compose identity (apply identity)) 42 with 42 in

let sum_tuple = lam t : (Int, Int). addi t.0 t.1 in

utest (curry sum_tuple) 3 2 with 5 in
utest (uncurry addi) (3,2) with 5 in
utest curry (uncurry addi) 3 2 with (uncurry (curry sum_tuple)) (3,2) using eqi in

let r = ref 0 in
let f = lam. modref r (addi (deref r) 1) in
utest modref r 0; repeat f 4; deref r with 4 in
utest modref r 0; repeat f 0; deref r with 0 in
utest modref r 0; repeat f (negi 5); deref r with 0 in

()
