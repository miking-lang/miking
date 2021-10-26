




type Promise

external asyncSleep ! : Float -> Promise a
external asyncRun ! : Promise a -> a


mexpr

utest asyncRun (asyncSleep 0.1); () with () in
()
