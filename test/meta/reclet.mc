-- Tests that recursive lets can have expressions that evaluates
-- to closures.

mexpr

let foo = lam b. lam x.
    recursive
    let f = if b then lam x. fact x else lam x. x
    let fact = lam n. if eqi n 0 then 1 else muli (fact (subi n 1)) n
    in
    f x
in

utest foo false 4 with 4 in
utest foo false 10 with 10 in
utest foo true 4 with 24 in
utest foo true 5 with 120 in
()
