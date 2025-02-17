include "map.mc"
include "seq.mc"
include "string.mc"
include "sys.mc"
include "common.mc"

let filepathConcat : String -> String -> String = lam dir. lam path.
  if eqc '/' (last dir) then
    concat dir path
  else
    join [dir, "/", path]
utest filepathConcat "a/b/c" "foo.mc" with "a/b/c/foo.mc"
utest filepathConcat "a/b/c/" "foo.mc" with "a/b/c/foo.mc"

let dirname : String -> String = lam filepath.
  match findiLast (eqc '/') filepath with Some i then
    subsequence filepath 0 i
  else
    ""

utest dirname "foo.mc" with ""
utest dirname "a/b/c/foo.mc" with "a/b/c"
utest dirname "a/b/c/../foo.mc" with "a/b/c/.."

let fileutilsNormalize : String -> String = lam path.
  recursive let recur = lam zipper : ([String], [String]).
    switch zipper
    case (segments, []) then strJoin "/" segments
    case ([], [""] ++ after) then recur ([""], after)
    case (before, ["." | ""] ++ after) then recur (before, after)
    case (before ++ [_], [".."] ++ after) then recur (before, after)
    case (before, [here] ++ after) then recur (snoc before here, after)
    end in
  let path = match path with "/" ++ _
    then path
    else concat (sysGetCwd ()) (cons '/' path) in
  recur ([], strSplit "/" path)

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
