




type Promise

external asyncSleep ! : Float -> Promise a
let asyncSleep = lam t. asyncSleep t

external asyncRun ! : Promise a -> a
let asyncRun = lam p. asyncRun p

external asyncBind ! : Promise a -> (a -> Promise b) -> Promise b
let asyncBind = lam p. lam f. asyncBind p f

external asyncPrint ! : String -> Promise ()
let asyncPrint = lam x. asyncPrint x

external asyncReturn ! : a -> Promise a
let asyncReturn = lam x. asyncReturn x

mexpr

utest asyncRun (asyncBind (asyncSleep 0.1) asyncReturn); () with () in
utest asyncRun (asyncPrint ""); () with () in
()
