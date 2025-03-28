-- Prints the number of CUDA devices on the system.

include "common.mc"
include "string.mc"
include "cuda/sys.mc"

mexpr

let dc: Option Int = cudaGetDeviceCount () in

match cudaGetDeviceCount () with Some c then
    printLn (join [
        "Found ", int2string c, " CUDA devices on your system."
    ])
else
    printLn "Could not compile and run CUDA programs in your environment."
