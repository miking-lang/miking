include "string.mc"

let _blt = pyimport "builtins"
let _subprocess = pyimport "subprocess"
let _tempfile = pyimport "tempfile"

type Program = String -> [String] -> {stdout: String, stderr: String, returncode: Int}

let writeToFile = lam str. lam filename.
  let f = pycall _blt "open" (filename, "w+") in
  let _ = pycallkw _subprocess "run" (["echo", str],) {stdout=f} in
  let _ = pycall f "close" () in
  ()

let runCommand = lam cmd. lam cwd. lam exitOnFailure.
  let r = pycallkw _subprocess "run" (cmd,) {cwd=cwd, capture_output=true} in
  let returncode = pyconvert (pycall _blt "getattr" (r,"returncode")) in
  let stdout =
    pyconvert (pycall (pycall _blt "getattr" (r,"stdout")) "decode" ())
  in
  let stderr =
    pyconvert (pycall (pycall _blt "getattr" (r,"stderr")) "decode" ())
  in
  if and (neqi returncode 0) exitOnFailure then
    exit returncode
  else
    {stdout=stdout, stderr=stderr, returncode=returncode}

let compile : String -> Program = lam p.
  let symlink = lam from. lam to.
    pycall _subprocess "run" (["ln", "-sf", from, to],)
  in

  let dunefile = "(executable (name program) (libraries batteries boot))" in
  let td = pycall _tempfile "TemporaryDirectory" () in
  let dir = pyconvert (pycall _blt "getattr" (td, "name")) in
  let tempfile = lam f. strJoin "/" [dir, f] in

  let _ = writeToFile p (tempfile "program.ml") in
  let _ = writeToFile dunefile (tempfile "dune") in

  let command = ["dune", "build"] in
  let _ = runCommand command (tempfile "") true in

  lam stdin. lam args.
    let command = ["dune", "exec", "./program.exe", "--", strJoin " " args] in
    runCommand command (tempfile "") false

mexpr

let run =
  compile "print_endline (\"This is the sym: \" ^ (Boot.Intrinsics.Symb.Helpers.string_of_sym (Boot.Intrinsics.Symb.gensym ())))"
in

let run2 =
  compile "print_endline \"Hello World!\""
in

let _ = dprint (run "" [""]) in
let _ = dprint (run2 "" [""]) in
let _ = dprint (run "" [""]) in
()
