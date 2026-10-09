-- Should fail: existentials from different matches are distinct
type Ex
con MkEx : all x. (x, x -> Int) -> Ex

mexpr
let mix = lam e1. lam e2.
  match (e1, e2) with (MkEx (v, _), MkEx (_, f)) in f v in
mix (MkEx (1, lam x. x)) (MkEx (1, lam x. x))
