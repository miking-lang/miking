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

dprint (add 2 3);
dprint (inc 41);
dprint (apply (add 10) 5);
dprint (twice inc 0);
dprint (alias 20 22);
dprint ((lam x. muli x x) 7);

-- Over-application: a function returning a function, then applied again.
let mkAdder = lam x. lam y. addi x y in
dprint (mkAdder 3 4);
dprint ((mkAdder 3) 4);

-- A constant used as a value rather than applied directly.
let combine = lam op. lam a. lam b. op a b in
dprint (combine addi 5 6);
dprint (combine muli 5 6)
