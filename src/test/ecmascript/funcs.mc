-- Lambdas and application.
--
-- A named function of known arity should compile to a plain n-ary call rather
-- than a curried chain; partial application and bare references still have to
-- behave, which is what the rest of this exercises.
mexpr
let add = lam x. lam y. addi x y in
let inc = add 1 in
let apply = lam f. lam v. f v in
let twice = lam f. lam v. f (f v) in
let alias = add in

utest add 2 3 with 5 in
utest inc 41 with 42 in
utest apply (add 10) 5 with 15 in
utest twice inc 0 with 2 in
utest alias 20 22 with 42 in
utest (lam x. muli x x) 7 with 49 in

-- Over-application: a function returning a function, then applied again.
let mkAdder = lam x. lam y. addi x y in
utest mkAdder 3 4 with 7 in
utest (mkAdder 3) 4 with 7 in

-- A constant used as a value rather than applied directly.
let combine = lam op. lam a. lam b. op a b in
utest combine addi 5 6 with 11 in
utest combine muli 5 6 with 30 in
()
