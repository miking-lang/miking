-- Minimal logging API
-- NOTE: Warnings cannot be selectively disabled. Supporting this would require
-- either a global state or propagating a flag throughout the codebase, which
-- would add significant verbosity. If you wish to suppress a specific warning,
-- the recommended approach is to comment it out at the call site. You are free
-- to modify this design and introduce a flag if needed.

include "util.mc"
include "format.mc"

type Logger = String -> ()

-- Print a log message with a given kind, namespace, and message.
let message : String -> String -> Logger = lam kind. lam namespace. lam message.
    printLn (join [kind, " from ", namespace, ": ", message])

-- Display a warning message.
let createWarner : String -> Logger = lam m1. lam m2. message "[WARN]" m1 m2

let parsingWarn : Logger = createWarner "Parsing"
let labelingWarn : Logger = createWarner "Labeling"
let namingWarn : Logger = createWarner "Naming"
let renderingWarn : Logger = createWarner "Rendering"

let warn : Logger = lam w. printLn (concat "[WARN] " w)
