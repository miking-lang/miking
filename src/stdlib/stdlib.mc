-- Mimics the approach used to find the stdlib location in
-- src/boot/lib/parserutils.ml

include "sys.mc"
include "option.mc"

let stdlibCwd = join [sysGetCwd (), "/stdlib"]

let stdlibLocUnix =
  match sysGetEnv "HOME" with Some path then
    join [path, "/.local/lib/mcore/stdlib"]
  else stdlibCwd

let stdlibLoc =
  optionGetOrElse
    (lam.
      -- NOTE(dlunde,2022-05-04) The boot parser also checks if the OS type is
      -- "Unix" here
      if sysFileExists stdlibLocUnix then stdlibLocUnix else stdlibCwd)
    (optionBind
       (sysGetEnv "MCORE_LIBS")
       (lam path.
         let libs = strSplit ":" path in
         findMap
           (lam str.
             match splitAt str 7 with ("stdlib=", loc)
             then Some loc else None ())
           libs))
