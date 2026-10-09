-- Should fail: an existential is not the type it was constructed with (in a sem)
type Ex
con MkEx : all x. (x, x -> Int) -> Ex

lang L
  syn Foo = | Foo Ex
  sem leak : Foo -> Int
  sem leak = | Foo (MkEx (v, _)) -> addi v 1
end

mexpr
use L in leak (Foo (MkEx (1, lam x. x)))
