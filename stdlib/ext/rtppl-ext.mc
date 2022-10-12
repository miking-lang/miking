
type Port = Int
type TimeStampedValue = (Int, Float)

-- Functions for reading and writing time-stamped values (a tuple containing a
-- time-stamp and a value), using a latest-value semantics.
external lvRead : Port -> TimeStampedValue
external lvWrite : Port -> TimeStampedValue -> ()

type Signal = Int

-- Overrides the signal handler for a particular signal (for simplicity, the
-- signal is simply encoded as an integer).
external setSignalHandler : Signal -> (Signal -> ()) -> ()

-- External functions used for supporting the 'sdelay' keyword
external clockGetTime : () -> (Int, Int)
external clockNanosleep : (Int, Int) -> ()

mexpr

utest setSignalHandler 1 (lam. print "hello") with true using lam. lam. true in

()
