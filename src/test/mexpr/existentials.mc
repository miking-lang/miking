-- Existential types via constructors: a quantified type variable that
-- does not occur in the constructor's result type is abstract inside
-- each match on the constructor. See src/test/examples/existentials
-- for programs that must be rejected.

type Ex
con MkEx : all x. (x, x -> Int) -> Ex

type Wrap a
con MkWrap : all x. all a. (x, x -> a) -> Wrap a

let useEx : Ex -> Int = lam e. match e with MkEx (v, f) in f v
let unwrap : all a. Wrap a -> a = lam w. match w with MkWrap (v, f) in f v
let unwrapU = lam w. match w with MkWrap (v, f) in f v

-- Local polymorphic definitions inside the arm
let useLocal = lam e. match e with MkEx (v, f) in
  let g = lam y. (f v, y) in
  addi (g 1).0 (g "a").0

-- Existentials nested in record and sequence patterns
let useRec = lam p. match p with {a = MkEx (v, f), b = n} in addi n (f v)
let useSeq = lam s. match s with [MkEx (v, f)] ++ _ then f v else 0

lang ExLang
  syn Foo = | Foo Ex
  sem useFoo : Foo -> Int
  sem useFoo = | Foo (MkEx (v, f)) -> f v
end

mexpr

use ExLang in

let e1 = MkEx (1, lam x. addi x 1) in
let e2 = MkEx ("abc", length) in

utest useEx e1 with 2 in
utest useEx e2 with 3 in
utest unwrap (MkWrap ('a', lam c. [c])) with "a" in
utest unwrapU (MkWrap (1, lam x. addi x 1)) with 2 in
utest useLocal e1 with 4 in
utest useRec {a = e2, b = 1} with 4 in
utest useSeq [e1, e2] with 2 in
utest useFoo (Foo e2) with 3 in

()
