-- Should fail: an existential escapes through a reference
type Ex
con MkEx : all x. (x, x -> Int) -> Ex

mexpr
let r = ref [] in
let f = lam e. match e with MkEx (v, _) in modref r [v] in
f (MkEx (1, lam x. x))
