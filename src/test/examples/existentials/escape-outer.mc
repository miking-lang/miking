-- Should fail: an existential escapes by unifying with a variable from outside the match
type Ex
con MkEx : all x. (x, x -> Int) -> Ex

mexpr
let f = lam e. lam y. match e with MkEx (v, _) in if true then v else y in
f (MkEx (1, lam x. x)) 2
