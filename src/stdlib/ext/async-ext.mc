


type Promise a

external asyncSleepSec ! : Float -> Promise ()
let asyncSleepSec = lam t. asyncSleepSec t

external asyncRun ! : all a. Promise a -> a
let asyncRun = lam p. asyncRun p

external asyncBind ! : all a. all b. Promise a -> (a -> Promise b) -> Promise b
let asyncBind = lam p. lam f. asyncBind p f

external asyncPrint ! : String -> Promise ()
let asyncPrint = lam x. asyncPrint x

external asyncReturn ! : all a. a -> Promise a
let asyncReturn = lam x. asyncReturn x

mexpr

utest asyncRun (asyncBind (asyncSleepSec 0.1) asyncReturn); () with () in
utest asyncRun (asyncPrint ""); () with () in
()
