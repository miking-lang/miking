-- Mimics the approach used to find the stdlib location in
-- src/boot/lib/parserutils.ml

include "sys.mc"
include "option.mc"
include "map.mc"
include "error.mc"
include "fileutils.mc"

-- Helpers

let parseMCoreLibs : String -> Map String String = lam str.
  match str with "" then mapEmpty cmpString else
  let processBinding = lam acc. lam str.
    match strSplit "=" str with [lib, path] ++ paths
    then mapInsert lib (strJoin "=" (cons path paths)) acc
    else
      warnSingle [] (join
        [ "Invalid element of MCORE_LIBS: \""
        , str
        , "\"\nShould be a lib=path/to/lib pair"]);
      acc in
  foldl processBinding (mapEmpty cmpString) (strSplit ":" str)

utest parseMCoreLibs "" with mapEmpty cmpString using mapEq eqString
utest parseMCoreLibs "stdlib=a/b/c"
  with mapFromSeq cmpString [("stdlib", "a/b/c")]
  using mapEq eqString
utest parseMCoreLibs "stdlib=a/b/c:foo=bar"
  with mapFromSeq cmpString [("stdlib", "a/b/c"), ("foo", "bar")]
  using mapEq eqString

let addCWDtoLibs : Map String String -> Map String String = lam libs.
  mapInsert "cwd" (sysGetCwd ()) libs

-- Side-effecting computation of the stdlib location as well as the
-- location of other libraries

let stdlibCwd = join [sysGetCwd (), "/src/stdlib"]

let stdlibLocUnix =
  match sysGetEnv "HOME" with Some path then
    join [path, "/.local/lib/mcore/stdlib"]
  else stdlibCwd

let stdlibMCoreLibs =
  let map = optionMapOr
    (mapEmpty cmpString)
    parseMCoreLibs
    (sysGetEnv "MCORE_LIBS") in
  mapInsertWith (lam prev. lam. prev)
    "stdlib"
    (if sysFileExists stdlibLocUnix then stdlibLocUnix else stdlibCwd)
    map

let stdlibLoc = mapFindExn "stdlib" stdlibMCoreLibs


-- Resolves a path specified in a file in directory
-- `relativeTo`. Applies path normalization. The `doError` function
-- will be called with an error message if an error occurs. Follows
-- these rules:
-- - If path has the form "/absolute/path/to/file", return the path
--   unchanged
-- - If path has the form "lib::path/to/file" and MCORE_LIBS contains
--   "lib=path/to/lib", return "path/to/lib/path/to/file".
-- - If path has the form "./path/to/file" or "../path/to/file",
--   return path relative to the `relativeTo` path.
-- - If path has the form "path/to/file", return a path relative to
--   the given directory or in the stdlib. Checks for ambiguity,
--   errors if both exist. Priority: existing file, then local file.
let stdlibResolveFileOr : (String -> String) -> String -> String -> String = lam doError. lam relativeTo. lam path.
  match path with "/" ++ _ then
    path
  else match strSplit "::" path with [lib, path] ++ paths then
    -- Explicit library use
    match mapLookup lib stdlibMCoreLibs with Some libPath
    then fileutilsNormalize (filepathConcat libPath (strJoin "::" (cons path paths)))
    else doError (join ["Library ", lib, " not found in MCORE_LIBS"])
  else
    -- Non-explicit
    let localPath = fileutilsNormalize (filepathConcat relativeTo path) in
    -- Check if explicitly local
    match path with "./" ++ _ | "../" ++ _ then localPath else
    -- Implicit, check if in stdlib
    let stdlibPath = fileutilsNormalize (filepathConcat stdlibLoc path) in
    -- Check if both resolve to the same path, return it if so
    if eqString localPath stdlibPath then stdlibPath else
    switch (sysFileExists stdlibPath, sysFileExists localPath)
    case (true, false) then stdlibPath
    case (true, true) then doError (join ["Path ", path, " is ambiguous, exists both locally and in stdlib"])
    case _ then localPath
    end
