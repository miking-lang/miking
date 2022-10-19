include "ext/file-ext.mc"

type Opaque
type TimeStampedValue = (Int, Opaque)

let toTimestampedValue : all a. (Int, a) -> (Int, Opaque) = lam tuple.
  match tuple with (ts, value) in
  (ts, unsafeCoerce value)

let timestampValue : all a. Opaque -> a = lam tsv.
  match tsv with (ts, value) in
  unsafeCoerce value

-- Functions for reading and writing time-stamped values (a tuple containing a
-- time-stamp and an opaque value), using a latest-value semantics.
external lvRead : Int -> TimeStampedValue
external lvWrite : Int -> TimeStampedValue -> ()

external readBinary : ReadChannel -> Opaque
let readBinary : all a. ReadChannel -> a =
  lam inChannel.
  unsafeCoerce (readBinary inChannel)

external writeBinary : WriteChannel -> Opaque -> ()
let writeBinary : all a. WriteChannel -> a -> () =
  lam outChannel. lam v.
  writeBinary outChannel (unsafeCoerce v)

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
