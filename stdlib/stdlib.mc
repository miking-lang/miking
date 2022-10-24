-- Mimics the approach used to find the stdlib location in
-- src/boot/lib/parserutils.ml

include "sys.mc"

let stdlibCwd = join [sysGetCwd (), "/stdlib"]

let stdlibLocUnix =
  match sysGetEnv "HOME" with Some path then
    join [path, "/.local/lib/mcore/stdlib"]
  else stdlibCwd

let stdlibLoc =
  match sysGetEnv "MCORE_STDLIB" with Some path then path
  else
    -- NOTE(dlunde,2022-05-04) The boot parser also checks if the OS type is
    -- "Unix" here
    if sysFileExists stdlibLocUnix then stdlibLocUnix else stdlibCwd
