include "map.mc"
include "seq.mc"
include "string.mc"
include "sys.mc"
include "common.mc"

let parseMCoreLibs : String -> Map String String = lam str.
  match str with "" then mapEmpty cmpString else 
  let libs = strSplit ":" str in 
  let pairs = map (lam lib. strSplit "=" lib) libs in 

  let isValid = lam pair. 
    if neqi (length pair) 2 then 
      error (join [
        "Invalid $MCORE_LIBS environment: '",
        str,
        "'!"
      ])
    else  ()
  in 
  iter isValid pairs ;

  let pairs = map (lam p. (head p, get p 1)) pairs in 

  mapFromSeq cmpString pairs

utest parseMCoreLibs "" with mapEmpty cmpString using mapEq eqString
utest parseMCoreLibs "stdlib=a/b/c" 
  with mapFromSeq cmpString [("stdlib", "a/b/c")] 
  using mapEq eqString
utest parseMCoreLibs "stdlib=a/b/c:foo=bar" 
  with mapFromSeq cmpString [("stdlib", "a/b/c"), ("foo", "bar")] 
  using mapEq eqString

-- TODO(voorberg, 27-05-2024): Add a sensible default for $MCORE_LIBS to 
--                             fall back on. 
let parseMCoreLibsEnv : () -> Map String String = lam.
  match sysGetEnv "MCORE_LIBS" with Some s then
    parseMCoreLibs s
  else
    error "Environment variable $MCORE_LIBS is not set!"

let addCWDtoLibs : Map String String -> Map String String = lam libs. 
  mapInsert "cwd" (sysGetCwd ()) libs

let filepathConcat : String -> String -> String = lam dir. lam path. 
  if eqc '/' (last dir) then
    concat dir path
  else
    join [dir, "/", path]
utest filepathConcat "a/b/c" "foo.mc" with "a/b/c/foo.mc"
utest filepathConcat "a/b/c/" "foo.mc" with "a/b/c/foo.mc"

let eraseFile : String -> String = lam filepath. 
  match findiLast (eqc '/') filepath with Some i then
    subsequence filepath 0 i
  else 
    ""

utest eraseFile "foo.mc" with "" 
utest eraseFile "a/b/c/foo.mc" with "a/b/c"
utest eraseFile "a/b/c/../foo.mc" with "a/b/c/.."

-- type Filepath = [String]

-- let filepath2string : Filepath -> String = lam fp.
--   cons '/' (strJoin "/" fp)

-- utest filepath2string ["a", "b", "c"] with "/a/b/c"
-- utest filepath2string ["a", "b", "foo.mc"] with "/a/b/foo.mc"

-- mexpr
-- let m = parseMCoreLibsEnv () in 
-- let m = addCWDtoLibs m in 
-- let m = mapToSeq m in 
-- iter (lam p. match p with (_, y) in printLn y) m