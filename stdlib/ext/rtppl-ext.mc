
type Port = Int
type TimeStampedValue = (Int, Float)

-- Functions for reading and writing time-stamped values (a tuple containing a
-- time-stamp and a value), using a latest-value semantics.
external lvRead : Port -> TimeStampedValue
external lvWrite : Port -> TimeStampedValue -> ()

type Signal = Int

external setSignalHandler : Signal -> (Signal -> ()) -> ()

mexpr

utest setSignalHandler 0 (lam. ()) with true using lam. lam. true in

()
