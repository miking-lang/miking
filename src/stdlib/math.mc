include "ext/math-ext.mc"
include "bool.mc"
include "float.mc"
include "int.mc"

-- Inefficient version of logFactorial
let logFactorial : Int -> Float = lam n.
  recursive let work = lam acc. lam n.
    if gti n 0 then work (addf (log (int2float n)) acc) (subi n 1)
    else acc
  in work 0.0 n

utest roundfi (exp (logFactorial 3)) with 6
utest roundfi (exp (logFactorial 4)) with 24

-- `fact n` returns the factorial !n. Gives an error on negative `n`.
let fact : Int -> Int = lam n.
  if lti n 0 then error "fact: undefined"
  else
    recursive let recur = lam acc. lam n.
      if lti n 2 then acc
      else recur (muli acc n) (pred n)
    in
    recur 1 n

utest fact 0 with 1
utest fact 1 with 1
utest fact 2 with 2
utest fact 3 with 6
utest fact 4 with 24

-- `binomial n k` returns the binomial number: `n` choose `k`.
let binomial : Int -> Int -> Int
  = lam n. lam k.
    if or (or (lti n 0) (lti k 0)) (gti k n) then 0
    else
      divi (fact n) (muli (fact k) (fact (subi n k)))

utest binomial 1 (negi 1) with 0
utest binomial (negi 1) 1 with 0
utest binomial 0 1 with 0
utest binomial 0 0 with 1
utest binomial 1 0 with 1
utest binomial 1 1 with 1
utest binomial 2 0 with 1
utest binomial 2 1 with 2
utest binomial 2 2 with 1
utest binomial 3 0 with 1
utest binomial 3 1 with 3
utest binomial 3 2 with 3
utest binomial 3 3 with 1
utest binomial 4 0 with 1
utest binomial 4 1 with 4
utest binomial 4 2 with 6
utest binomial 4 3 with 4
utest binomial 4 4 with 1

-- `pascal n` returns the n first rows in Pascals triangle of binomial numbers.
let pascal : Int -> [[Int]] = lam n.
  let nextRow = lam row.
    recursive let recur = lam acc. lam cs.
      switch cs
      case [] then [1]
      case [1] then [1, 1]
      case [c1, c2] then snoc (cons 1 (snoc acc (addi c1 c2))) 1
      case [c1, c2] ++ cs then recur (snoc acc (addi c1 c2)) (cons c2 cs)
      case _ then error "impossible"
      end
    in
    recur [] row
  in
  recursive let recur = lam acc. lam prow. lam n.
    if lti n 0 then acc
    else
      let row = nextRow prow in
      recur (snoc acc row) row (pred n)
  in
  recur [] [] (pred n)

utest pascal 0 with []
utest pascal 1 with [[1]]
utest pascal 2 with [[1], [1, 1]]
utest pascal 3 with [
  [1],
  [1, 1],
  [1, 2, 1]
]
utest pascal 4 with [
  [1],
  [1, 1],
  [1, 2, 1],
  [1, 3, 3, 1]
]
utest pascal 5 with [
  [1],
  [1, 1],
  [1, 2, 1],
  [1, 3, 3, 1],
  [1, 4, 6, 4, 1]
]

-- `pascalrow n` returns the n'th row (0-indexed) in Pascals triangle of
-- binomial numbers.
let pascalrow : Int -> [Int] = lam n.
  if lti n 0 then []
  else
    let k = divi n 2 in
    let row = create (succ k) (binomial n) in
    let rrow = reverse row in
    if isEven n then
      concat row (tail rrow)
    else
      concat row rrow

utest pascalrow 0 with [1]
utest pascalrow 1 with [1, 1]
utest pascalrow 2 with [1, 2, 1]
utest pascalrow 3 with [1, 3, 3, 1]
utest pascalrow 4 with [1, 4, 6, 4, 1]
utest pascalrow 5 with [1, 5, 10, 10, 5, 1]
