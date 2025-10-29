include "util.mc"
include "format.mc"

type Logger = String -> ()

-- Print a log message with a given kind, namespace, and message.
let message : String -> String -> Logger = lam kind. lam namespace. lam message.
    printLn (join [kind, " from ", namespace, ": ", message])

-- Display a warning message.
let warn : String -> Logger = lam m1. lam m2. message "WARNING" m1 m2

let parsingWarn : Logger = warn "Parsing"
let extractingWarn : Logger = warn "Extracting"
let renderingWarn : Logger = warn "Rendering"
let labelingWarn : Logger = warn "Labeling"
