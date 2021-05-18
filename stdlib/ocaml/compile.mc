include "string.mc"
include "sys.mc"

type CompileOptions = {
  optimize : Bool,
  libraries : [String]
}

type Program = String -> [String] -> ExecResult
type CompileResult = {
  run : Program,
  cleanup : Unit -> Unit,
  binaryPath : String
}

let defaultCompileOptions : CompileOptions = {
  optimize = true,
  libraries = []
}

let ocamlCompileWithConfig : CompileOptions -> String -> CompileResult =
  lam options : CompileOptions. lam p.
  let libstr =
    strJoin " " (distinct eqString (cons "boot" options.libraries))
  in
  let dunefile =
   join [
   "(env
      (dev
        (flags (:standard -w -a))
        (ocamlc_flags (-without-runtime))
        (ocamlopt_flags (-linscan -inline 1)))
      (opt
        (flags (:standard -w -a))
        (ocamlc_flags (-without-runtime))
        (ocamlopt_flags (-O3))))
    (executable (name program) (libraries ", libstr , "))"] in
  let td = sysTempDirMake () in
  let dir = sysTempDirName td in
  let tempfile = lam f. sysJoinPath dir f in

  writeFile (tempfile "program.ml") p;
  writeFile (tempfile "program.mli") "";
  writeFile (tempfile "dune") dunefile;

  let command =
    if options.optimize then
      ["dune", "build", "--profile=opt"]
    else
      ["dune", "build"]
  in
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

let ocamlCompile : String -> CompileResult =
  ocamlCompileWithConfig defaultCompileOptions

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
