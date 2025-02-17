
-- Tricky example that show that you need to be careful with name bindings
-- when using dive. It is not enough to have unique names of all
-- lambdas, statically. You need to use a readback function.



mexpr


dprint (dive ((lam f. f f) (lam y. lam x. y x)));

print "\n"

/--

**** Simple incorrect term, if lambda names are not statically unique ****

* The following term generates a wrong term

  dive (lam x. (lam y. lam x. y) x)



**** Statically unique lambda terms, still incorrec ****

* We can actually generate the same term, even if all names of lambdas
* are unique, statically:

dive ((lam f. f f) (lam y. lam x. y x))

==> dive ((lam y. lam x. y x) (lam y. lam x. y x))

==> dive (lam x. (lam y. lam x. y x) x)

* Incorrect evaluation *

lam x. (lam x. x x)

* Correct evaluation, where out x has a new name *

lam x'. (lam x. x' x)



**** Running with closures, clos t [env]


dive ((lam f. f f) (lam y. lam x. y x))
: ENV []

dive f f
: ENV [f -> (clos y. lam x. y x)[] ]

dive (clos y. lam x. y x)[] (clos y. lam x. y x)[]
: ENV [f -> (clos y. lam x. y x)[] ]

dive lam x. y x
: ENV [y -> (clos y. lam x. y x)[],
       f -> (clos y. lam x. y x)[] ]

lam x. (clos y. lam x. y x) x
: ENV [y -> (clos y. lam x. y x)[],
       f -> (clos y. lam x. y x)[] ]

lam x. lam x. y x
: ENV [y -> x
       y -> (clos y. lam x. y x)[],
       f -> (clos y. lam x. y x)[] ]

* Also incorrect.

** Conclusion: we need to rename variables, and use PE symbols

--/
