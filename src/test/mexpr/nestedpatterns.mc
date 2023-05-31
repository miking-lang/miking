mexpr

let classify = lam x : (Bool, Bool).
  match x with (true, true) then "one" else
  match x with (true, false) then "two" else
  match x with (false, true) then "three" else
  match x with (false, false) then "four"
  else "five" in
utest classify (true, true) with "one" in
utest classify (true, false) with "two" in
utest classify (false, true) with "three" in
utest classify (false, false) with "four" in

-- TODO(?,?): in the future when we have static type checking,
-- the following expression should give a type error.
-- utest classify (true, true, true) with "five" in

let uncurry = lam f. lam x : (a, b).
  match x with (a, b) then f a b else error "bad" in
utest uncurry addi (1, 2) with 3 in

let weird = lam x : (([a], [a]), ([a], [a])).
  match x with ((a, b), (c, d)) then
    concat (concat a b) (concat c d)
  else error "bad" in
utest weird (("a", "b"), ("c", "d")) with "abcd" in

utest match 'a' with 'a' then true else false with true in

()
