

include "ext/async-ext.mc"

recursive let tic = lam str. lam time.
  asyncBind (asyncPrint str) (lam.
  asyncBind (asyncSleep time) (lam.
  tic str time
  ))

end

mexpr

tic "-- two seconds --\n" 2.0;
asyncRun (tic "tic\n" 0.5)
