type Signal = Int

-- Overrides the signal handler for the SIGINT signal.
external setSigintHandler : (Signal -> ()) -> ()

-- Functions for accessing different the time according to different clocks and
-- using this to sleep until an absolute point in time. The timespec contains
-- a specification of the time of the format (seconds, nanoseconds).
type Timespec = (Int, Int)
external getMonotonicTime : () -> Timespec
external getWallClockTime : () -> Timespec
external getProcessCpuTime : () -> Timespec
external clockNanosleep : Timespec -> ()

-- Sets the priority of the process, returning the previous priority
external rtpplSetMaxPriority : () -> Int
external rtpplSetPriority : Int -> Int

-- Opens and closes file descriptors
external rtpplOpenFileDescriptor : String -> Int
external rtpplCloseFileDescriptor : Int -> ()

type Opaque

-- Writing and reading RTPPL data types to and from a given file descriptor.
external rtpplReadFloat : Int -> [(Timespec, Float)]
external rtpplWriteFloat : Int -> (Timespec, Float) -> ()
external rtpplReadDistFloat : Int -> [(Timespec, [(Float, Float)])]
external rtpplWriteDistFloat : Int -> (Timespec, ([Float], [Float])) -> ()
external rtpplReadDistFloatRecord : Int -> Int -> [(Timespec, [(Float, Opaque)])]
external rtpplWriteDistFloatRecord : Int -> Int -> (Timespec, ([Opaque], [Float])) -> ()

external rtpplBatchedInference : (() -> Opaque) -> Timespec -> [Opaque]

mexpr

utest setSigintHandler (lam. print "hello") with true using lam. lam. true in

()
