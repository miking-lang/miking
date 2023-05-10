include "string.mc"
include "sys.mc"

type CompileOptions = {
  optimize : Bool,
  libraries : [String],
  cLibraries : [String]
}

type Program = String -> [String] -> ExecResult
type CompileResult = {
  run : Program,
  cleanup : () -> (),
  binaryPath : String,
  keepFiles : [String] -- If any other files should be kept, specify so here
}

let defaultCompileOptions : CompileOptions = {
  optimize = true,
  libraries = [],
  cLibraries = []
}

let ocamlCompilePEval : CompileOptions -> String -> String -> CompileResult =
  lam options. lam p. lam entryPointId.
  let mainFile = join ["open Program let () = Program.", entryPointId, " ()"] in

  let td = sysTempDirMake () in
  let dir = sysTempDirName td in
  let tempfile = lam f. sysJoinPath dir f in

  writeFile (tempfile "program.ml") p;
  writeFile (tempfile "main.ml") mainFile;

  let programCmxPath = tempfile "program.cmx" in

  let command = ["ocamlfind", "ocamlopt", "-c -package \"boot\"",
                 "program.ml"] in
  let r = sysRunCommand command "" dir in
  if neqi r.returncode 0 then
    print (join ["Something went wrong when compiling the program\n",
                 r.stdout, "\n", r.stderr, "\n"]);
    exit 1
  else ();
  let command = ["ocamlfind", "ocamlopt", "-thread -package \"boot\""
                ,"-linkpkg -linkall", programCmxPath, "main.ml"] in
  let r = sysRunCommand command "" dir in
  if neqi r.returncode 0 then
    print (join ["Something went wrong when compiling main\n",
                 r.stdout, "\n", r.stderr, "\n"]);
    exit 1
  else ();
  {
    run =
      lam stdin. lam args.
        let command =
          concat ["dune", "exec", "--no-build", "./program.exe", "--"] args
        in
        sysRunCommand command stdin (tempfile ""),
    cleanup = lam. sysTempDirDelete td (); (),
    binaryPath = tempfile "a.out",
    keepFiles = [tempfile "program.cmi"]
 }

let ocamlCompileWithConfig : CompileOptions -> String -> CompileResult =
  lam options : CompileOptions. lam p.
  let libstr =
    strJoin " " (distinct eqString (cons "boot" options.libraries))
  in
  let flagstr =
    let clibstr =
      strJoin " "(map (concat "-cclib -l") (distinct eqString options.cLibraries))
    in
    concat ":standard -w -a " clibstr
  in
  let dunefile =
   join [
   "(env
      (dev
        (flags (", flagstr ,"))
        (ocamlc_flags (-without-runtime))
        (ocamlopt_flags (-linscan -inline 1)))
      (opt
        (flags (", flagstr ,"))
        (ocamlc_flags (-without-runtime))
        (ocamlopt_flags (-O3))))
    (executable (name program) (libraries ", libstr , "))"] in
  let td = sysTempDirMake () in
  let dir = sysTempDirName td in
  let tempfile = lam f. sysJoinPath dir f in

  writeFile (tempfile "program.ml") p;
  writeFile (tempfile "program.mli") "";
  writeFile (tempfile "dune-project") "(lang dune 2.0)";
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
          concat ["dune", "exec", "--no-build", "./program.exe", "--"] args
        in
        sysRunCommand command stdin (tempfile ""),
    cleanup = lam. sysTempDirDelete td (); (),
    binaryPath = tempfile "_build/default/program.exe",
    keepFiles = []
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
