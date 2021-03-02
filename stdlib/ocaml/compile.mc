include "string.mc"
include "python/python.mc"

let _blt = pyimport "builtins"
let _subprocess = pyimport "subprocess"
let _tempfile = pyimport "tempfile"
let _pathlib = pyimport "pathlib"

type ExecResult = {stdout: String, stderr: String, returncode: Int}
type Program = String -> [String] -> ExecResult

let _writeToFile = lam str. lam filename.
  let f = pycall _blt "open" (filename, "w+") in
  pycall f "write" (str,);
  pycall f "close" ();
  ()

let _readFile = lam filename.
  let f = pycall _blt "open" (filename, "r+") in
  let content = pycall f "read" () in
  pycall f "close" ();
  pyconvert content


let _runCommand : String->String->String->ExecResult =
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

let ocamlCompileWithConfig : {warnings: Bool} -> String -> {run: Program, cleanup: Unit -> Unit} = lam config. lam p.
  let config = if config.warnings
    then ""
    else "(env (dev (flags (:standard -w -a)))) " in
  let dunefile = concat config "(executable (name program) (libraries batteries boot))" in
  let td = pycall _tempfile "TemporaryDirectory" () in
  let dir = pythonGetAttr td "name" in
  let tempfile = lam f.
    let p = pycall _pathlib "Path" (dir,) in
    pycall _blt "str" (pycall p "joinpath" (f,),)
  in

  _writeToFile p (tempfile "program.ml");
  _writeToFile dunefile (tempfile "dune");

  let command = ["dune", "build"] in
  let r = _runCommand command "" (tempfile "") in
  if neqi r.returncode 0 then
      print (join ["'dune build' failed on program:\n\n",
                   _readFile (tempfile "program.ml"),
                   "\n\nexit code: ",
                   int2string r.returncode,
                   "\n\nstandard error:\n", r.stderr]);
      exit 1
  else ();
  

  {
    run =
      lam stdin. lam args.
        let command =
          concat ["dune", "exec", "./program.exe", "--"] args
        in
        _runCommand command stdin (tempfile ""),
    cleanup =
      lam.
        pycall td "cleanup" ();
        ()
  }

let ocamlCompile : String -> {run: Program, cleanup: Unit -> Unit} =
  ocamlCompileWithConfig {warnings=true}

mexpr

let sym =
  ocamlCompile
  "print_int (Boot.Intrinsics.Mseq.length Boot.Intrinsics.Mseq.empty)"
in

let hello =
  ocamlCompile "print_string \"Hello World!\""
in

let echo =
  ocamlCompile "print_string (read_line ())"
in

let args =
  ocamlCompile "print_string (Sys.argv.(1))"
in

let err =
  ocamlCompile "Printf.eprintf \"Hello World!\""
in

let manyargs =
  ocamlCompile "Printf.eprintf \"%s %s\" (Sys.argv.(1)) (Sys.argv.(2))"
in

utest (sym.run "" []).stdout with "0" in
utest (hello.run "" []).stdout with "Hello World!" in
utest (echo.run "hello" []).stdout with "hello" in
utest (args.run "" ["world"]).stdout with "world" in
utest (err.run "" []).stderr with "Hello World!" in
utest (manyargs.run "" ["hello", "world"]).stderr with "hello world" in

sym.cleanup ();
hello.cleanup ();
echo.cleanup ();
args.cleanup ();
err.cleanup ();
manyargs.cleanup ();

()
