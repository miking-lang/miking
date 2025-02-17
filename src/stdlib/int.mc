include "bool.mc"

let maxi = lam a. lam b. if gti a b then a else b
let mini = lam a. lam b. if lti a b then a else b
let absi = lam i. maxi i (negi i)

utest maxi 0 0 with 0
utest maxi 1 0 with 1
utest maxi 0 1 with 1

utest mini 0 0 with 0
utest mini 1 0 with 0
utest mini 0 1 with 0

utest absi 0 with 0
utest absi 1 with 1
utest absi (negi 1) with 1

utest addi 1 (negi 1) with 0

let succ = lam x. addi x 1

utest succ 0 with 1

let pred = lam x. subi x 1

utest pred 1 with 0

-- `isEven n` returns `true` if `n` is even and `false` otherwise
let isEven : Int -> Bool = lam n. eqi (modi n 2) 0

utest isEven (negi 2) with true
utest isEven (negi 1) with false
utest isEven 0 with true
utest isEven 1 with false
utest isEven 2 with true
utest isEven 3 with false
utest isEven 4 with true

-- `eqSign a b` returns true iff the sign of both `a` and `b` are equal
let eqSign : Int -> Int -> Bool = lam a. lam b.
  if lti a 0 then lti b 0
  else if gti a 0 then gti b 0
  else eqi b 0

utest eqSign 0 0 with true
utest eqSign 0 2 with false
utest eqSign 3 0 with false
utest eqSign 1 4 with true
utest eqSign 0 (negi 2) with false
utest eqSign (negi 3) 0 with false
utest eqSign (negi 1) (negi 4) with true
utest eqSign 1 (negi 2) with false
utest eqSign (negi 3) 4 with false

-- `neqSign a b` returns true iff the sign of both `a` and `b` are different
let neqSign : Int -> Int -> Bool = lam a. lam b. not (eqSign a b)

utest neqSign 0 0 with false
utest neqSign 0 2 with true
utest neqSign 3 0 with true
utest neqSign 1 4 with false
utest neqSign 0 (negi 2) with true
utest neqSign (negi 3) 0 with true
utest neqSign (negi 1) (negi 4) with false
utest neqSign 1 (negi 2) with true
utest neqSign (negi 3) 4 with true
