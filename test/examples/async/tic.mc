

include "ext/async-ext.mc"

recursive let tic = lam text. lam time.
  asyncBind (asyncPrint text) (lam.
  asyncBind (asyncSleep time) (lam.
  tic text time
  ))

end

mexpr

tic "-- two seconds --\n" 2.0;
asyncRun (tic "tic\n" 0.5)
