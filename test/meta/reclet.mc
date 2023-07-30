
-- Tests the feature of having expressions in recursive lets

mexpr

-- Makes the false choice if an argument is supplied to the program
let choice = eqi (length argv) 1 in

recursive
let f = if choice then lam x. x else lam x. fact x
let fact = lam n. if eqi n 0 then 1 else muli (fact (subi n 1)) n
in


dprint (f 4); print "\n"
