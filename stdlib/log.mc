include "seq.mc"
/-
  A simple logging library.

  NOTE(oerikss, 2021-09-28): Uses of this library should not be commited into
  the main Miking repos as logging introduces overhead even though the loglevel
  is set to off.
-/

type LogLevel = Int
let logLevel = {
  off = 0,
  error = 1,
  warning = 2,
  info = 3,
  debug = 4
}

-- Reference to that keeps track of loglevel
let _logLevel = ref logLevel.info

let _logLevelToString = lam lvl : LogLevel.
  if eqi lvl logLevel.error then "ERROR"
  else if eqi lvl logLevel.warning then "WARNING"
  else if eqi lvl logLevel.info then "INFO"
  else if eqi lvl logLevel.debug then "DEBUG"
  else ""

-- Sets the log level
let logSetLogLevel = lam lvl : LogLevel. modref _logLevel lvl

-- Checks if given level is printed under the current log level
let logLevelPrinted = lam lvl. leqi lvl (deref _logLevel)

-- `log lvl msg` logs the message `msg` at the log level `lvl`.
let logMsg = lam lvl : LogLevel. lam msg : () -> String.
  if eqi lvl logLevel.off then ()
  else if logLevelPrinted lvl then
    printError (join ["LOG ", _logLevelToString lvl, ":\t", msg (), "\n"]);
    flushStderr ()
  else ()

let logInfo = logMsg logLevel.info
let logError = logMsg logLevel.error
let logWarning = logMsg logLevel.warning
let logDebug = logMsg logLevel.debug

mexpr

-- logSetLogLevel logLevel.error;

-- logError "Some error!";
-- logWarning "Some warning!";
-- logInfo "Some info!";
-- logDebug "Some debug info!";

()
