




type Promise

external asyncSleep ! : Float -> Promise a
external asyncRun ! : Promise a -> a

external externalAsyncBind ! : Promise a -> (a -> Promise b) -> Promise b
let asyncBind = lam p. lam f. externalAsyncBind p f

mexpr

utest asyncRun (asyncBind (asyncSleep 0.1) (lam. asyncSleep 0.1)); () with () in

()
