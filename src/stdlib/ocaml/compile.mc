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
  binaryPath : String
}

let defaultCompileOptions : CompileOptions = {
  optimize = true,
  libraries = [],
  cLibraries = []
}

let ocamlCompileWithConfig : CompileOptions -> String -> CompileResult
  = lam options : CompileOptions. lam p.
    let td = sysTempDirMake () in
    let dir = sysTempDirName td in
    let tempfile = lam f. sysJoinPath dir f in

    let libflags =
      joinMap (lam x. ["-package", x]) (distinct eqString (cons "boot" options.libraries))
    in
    let clibflags =
      joinMap (lam x. ["-cclib", concat "-l" x]) (distinct eqString options.cLibraries) in
    let otherflags =
      ["-linkpkg", "-thread", "-w", "-a"] in
    let flags = join
      [ clibflags, libflags, otherflags
      , if options.optimize
        then ["-O3"]
        else ["-linscan", "-inline", "1"]
      ] in
    let command = join
      [ ["ocamlfind", "ocamlopt"]
      , flags
      , ["program.mli", "program.ml", "-o", tempfile "program.exe"]
      ] in

    writeFile (tempfile "program.ml") p;
    writeFile (tempfile "program.mli") "";

    let r = sysRunCommand command "" dir in
    if neqi r.returncode 0 then
        print (join ["'ocamlfind ocamlopt' failed on program:\n\n",
                     readFile (tempfile "program.ml"),
                     "\n\nexit code: ",
                     int2string r.returncode,
                     "\n\nstandard out:\n", r.stdout,
                     "\n\nstandard error:\n", r.stderr]);
        sysTempDirDelete td;
        exit 1
    else ();

    {
      run =
        lam stdin. lam args.
          let command =
            cons (tempfile "program.exe") args
          in
          sysRunCommand command stdin (tempfile ""),
      cleanup = lam. sysTempDirDelete td (); (),
      binaryPath = tempfile "program.exe"
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
