include "string.mc"
include "python/python.mc"

let _blt = pyimport "builtins"
let _subprocess = pyimport "subprocess"
let _tempfile = pyimport "tempfile"
let _pathlib = pyimport "pathlib"

type ExecResult = {stdout: String, stderr: String, returncode: Int}

let phWriteToFile = lam str. lam filename.
  let f = pycall _blt "open" (filename, "w+") in
  pycall f "write" (str,);
  pycall f "close" ();
  ()

let phReadFile = lam filename.
  let f = pycall _blt "open" (filename, "r+") in
  let content = pycall f "read" () in
  pycall f "close" ();
  pyconvert content

let phJoinPath = lam p1. lam p2.
  let p = pycall _pathlib "Path" (p1,) in
  pycall _blt "str" (pycall p "joinpath" (p2,),)

let phRunCommand : String -> String -> String -> ExecResult =
  lam cmd. lam stdin. lam cwd.
    let r = pycallkw _subprocess "run" (cmd,)
            { cwd=cwd,
              input=pycall (pycall _blt "str" (stdin,)) "encode" (),
              stdout = pythonGetAttr _subprocess "PIPE",
              stderr = pythonGetAttr _subprocess "PIPE" } in
    let returncode = pyconvert (pythonGetAttr r "returncode") in
    let stdout =
      pyconvert (pycall (pythonGetAttr r "stdout") "decode" ())
    in
    let stderr =
      pyconvert (pycall (pythonGetAttr r "stderr") "decode" ())
    in
    {stdout=stdout, stderr=stderr, returncode=returncode}

let phTempDirMake = lam. pycall _tempfile "TemporaryDirectory" ()
let phTempDirName = lam td. pythonGetAttr td "name"
let phTempDirDelete = lam td. lam. pycall td "cleanup" (); ()
