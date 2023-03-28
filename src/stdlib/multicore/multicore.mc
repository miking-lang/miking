-- A collection of useful functions for multicore programming.

include "sys.mc"
include "string.mc"

-- Get the available number of processing units, as reported by the command
-- 'nproc'.
let multicoreNbrOfCores : () -> Int = lam.
    let res = sysRunCommand ["nproc"] "" "." in
    if eqi res.returncode 0 then
      let nprocStr = strTrim res.stdout in
      string2int nprocStr
    else error "Command 'nproc' exited with failure, is it installed?"

mexpr

let debug = false in

utest
  if debug then
    print (int2string (multicoreNbrOfCores ())); print "\n"
  else ()
with () in

()
