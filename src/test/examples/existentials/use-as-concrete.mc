-- Should fail: an existential is not the type it was constructed with
type Ex
con MkEx : all x. (x, x -> Int) -> Ex

mexpr
match MkEx (1, lam x. x) with MkEx (v, _) in addi v 1
