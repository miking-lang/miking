

include "ext/async-ext.mc"

recursive let tick = lam str. lam time.
  asyncBind (asyncPrint str) (lam.
  asyncBind (asyncSleepSec time) (lam.
  tick str time
  ))

end

mexpr

tick "-- two seconds --\n" 2.0;
asyncRun (tick "tick\n" 0.5)
