-- MExpr-native alternative implementations of higher-order functions over
-- sequences. The below versions are slower than their intrisic counterparts.

let map = lam f. lam s.
  recursive let rec = lam s.
    match s with [] then []
    else match s with [a] then [f a]
    else match s with [a] ++ ss then cons (f a) (rec ss)
    else never
  in rec s

let iter = lam f. lam s.  map f s; ()

utest map (lam x. addi x 1) [3,4,8,9,20] with [4,5,9,10,21]
utest map (lam x. addi x 1) [] with []

let mapi = lam f. lam s.
  recursive let rec = lam i. lam s.
    match s with [] then []
    else match s with [a] then [f i a]
    else match s with [a] ++ ss then cons (f i a) (rec (addi i 1) ss)
    else never
  in rec 0 s

let iteri = lam f. lam s. mapi f s; ()

utest mapi (lam i. lam x. i) [3,4,8,9,20] with [0,1,2,3,4]
utest mapi (lam i. lam x. i) [] with []

let foldl = lam f. lam acc. lam s.
  recursive let rec = lam acc. lam s.
    match s with [] then acc
    else match s with [a] ++ ss then rec (f acc a) ss
    else never
  in rec acc s

utest foldl addi 0 [1,2,3,4,5] with 15
utest foldl addi 0 [] with 0
utest map (foldl addi 0) [[1,2,3], [], [1,3,5,7]] with [6, 0, 16]

let foldr = lam f. lam acc. lam s.
  recursive let rec = lam acc. lam s.
    match s with [] then acc
    else match s with [a] ++ ss then f a (rec acc ss)
    else never
  in rec acc s

utest foldr (lam x. lam acc. x) 0 [1,2] with 1
utest foldr (lam acc. lam x. x) 0 [] with 0
utest foldr cons [] [1,2,3] with [1,2,3]

let create = lam l. lam f.
  recursive let rec = lam i. lam acc.
    if geqi i 0 then rec (subi i 1) (cons (f i) acc)
    else acc
  in rec (subi l 1) []

utest create 3 (lam. 10) with [10,10,10]
utest create 8 (lam. 'a') with ['a','a','a','a','a','a','a','a']
utest create 4 (lam i. muli 2 i) with [0,2,4,6]
utest create 0 (lam i. i) with []
