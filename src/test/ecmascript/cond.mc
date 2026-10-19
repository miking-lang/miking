-- Pattern matching on scalars.
mexpr
let classify = lam n.
  match n with 0 then 100
  else match n with 1 then 200
  else match n with 2 then 300
  else 999
in
dprint (classify 0);
dprint (classify 1);
dprint (classify 2);
dprint (classify 7);

let letter = lam c.
  match c with 'a' then 1
  else match c with 'b' then 2
  else 0
in
dprint (letter 'a');
dprint (letter 'b');
dprint (letter 'z');

let flag = lam b. match b with true then 10 else 20 in
dprint (flag true);
dprint (flag false);

-- A branch that needs statements of its own, rather than folding to a ternary.
let stepped = lam n.
  if lti n 10 then
    let doubled = muli n 2 in
    addi doubled 1
  else
    0
in
dprint (stepped 4);
dprint (stepped 40);

-- Nested conditions, to check the `else if` chaining stays flat.
let sign = lam n. if lti n 0 then negi 1 else if eqi n 0 then 0 else 1 in
dprint (sign (negi 5));
dprint (sign 0);
dprint (sign 5)
