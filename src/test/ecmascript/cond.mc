-- Pattern matching on scalars.
mexpr
let classify = lam n.
  match n with 0 then 100
  else match n with 1 then 200
  else match n with 2 then 300
  else 999
in
utest classify 0 with 100 in
utest classify 1 with 200 in
utest classify 2 with 300 in
utest classify 7 with 999 in

let letter = lam c.
  match c with 'a' then 1
  else match c with 'b' then 2
  else 0
in
utest letter 'a' with 1 in
utest letter 'b' with 2 in
utest letter 'z' with 0 in

let flag = lam b. match b with true then 10 else 20 in
utest flag true with 10 in
utest flag false with 20 in

-- A branch that needs statements of its own, rather than folding to a ternary.
let stepped = lam n.
  if lti n 10 then
    let doubled = muli n 2 in
    addi doubled 1
  else
    0
in
utest stepped 4 with 9 in
utest stepped 40 with 0 in

-- Nested conditions, to check the `else if` chaining stays flat.
let sign = lam n. if lti n 0 then negi 1 else if eqi n 0 then 0 else 1 in
utest sign (negi 5) with negi 1 in
utest sign 0 with 0 in
utest sign 5 with 1 in
()
