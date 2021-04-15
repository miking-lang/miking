include "string.mc"
include "sys.mc"

type Program = String -> [String] -> ExecResult

let ocamlCompileWithConfig : {warnings: Bool} -> String -> {run: Program, cleanup: Unit -> Unit} = lam config. lam p.
  let config = if config.warnings
    then ""
    else "(env (dev (flags (:standard -w -a)))) " in
  let dunefile =
    concat config "(executable (name program) (libraries batteries boot))"
  in
  let td = sysTempDirMake () in
  let dir = sysTempDirName td in
  let tempfile = lam f. sysJoinPath dir f in

  writeFile (tempfile "program.ml") p;
  writeFile (tempfile "dune") dunefile;

  let command = ["dune", "build"] in
  let r = sysRunCommand command "" dir in
  if neqi r.returncode 0 then
      print (join ["'dune build' failed on program:\n\n",
                   readFile (tempfile "program.ml"),
                   "\n\nexit code: ",
                   int2string r.returncode,
                   "\n\nstandard error:\n", r.stderr]);
      sysTempDirDelete td;
      exit 1
  else ();

  {
    run =
      lam stdin. lam args.
        let command =
          concat ["dune", "exec", "./program.exe", "--"] args
        in
        sysRunCommand command stdin (tempfile ""),
    cleanup = sysTempDirDelete td,
    binaryPath = tempfile "_build/default/program.exe"
  }

let ocamlCompile : String -> {run: Program, cleanup: Unit -> Unit} =
  ocamlCompileWithConfig {warnings=false}

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
