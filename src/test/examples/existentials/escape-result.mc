-- Should fail: an existential escapes through the result of the match
type Ex
con MkEx : all x. (x, x -> Int) -> Ex

mexpr
let leak = lam e. match e with MkEx (v, _) in v in
leak (MkEx (1, lam x. x))
