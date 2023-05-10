include "mexpr/ast.mc"
include "ocaml/mcore.mc"

type LibCompileResult = {
  cleanup : () -> (),
  libPath : String
}

let compileOcamlLibrary : [String] -> [String] -> String -> LibCompileResult =
  lam libs. lam clibs. lam ocamlProg.

  let td = sysTempDirMake () in
  let dir = sysTempDirName td in
  let tempfile = lam f. sysJoinPath dir f in
  let t = tempfile ("plugin.ml") in
  writeFile t ocamlProg;
  -- Assume that needed dependencies are present in the cwd
  let includePath = sysGetCwd () in

  let command = ["ocamlfind", "ocamlopt -package boot -shared -I ", includePath,
                 " -o plugin.cmxs ", t] in
  let r = sysRunCommand command "" dir in
  (if neqi r.returncode 0 then
    print (join ["Something went wrong when compiling the plugin\n",
                 r.stdout, "\n", r.stderr, "\n"]);
    exit 1
  else ()); 
  {
  libPath = tempfile ("plugin.cmxs"),
  cleanup = lam. sysTempDirDelete td (); ()
  }

let _jitCompiled = ref (mapEmpty nameCmp)

let jitCompile : all a. Name -> Map Name String -> Expr -> a =
  lam id. lam pprintEnv.  lam e.
  match mapLookup id (deref _jitCompiled) with Some f then f
  else
    let nameToStr = lam id.
      let s = nameGetStr id in
      match nameGetSym id with Some sym then
        join [s, "_", int2string (sym2hash sym)]
      else s
    in
  let extId = concat "mexpr_jit_" (nameToStr id) in
  let p =
    use MCoreCompileLang in
    compileMCorePlugin extId pprintEnv e (mkEmptyHooks (compileOcamlLibrary))
  in
  loadLibraries p.libPath;
  p.cleanup ();
  let residual = unsafeCoerce (getExternal extId) in
  modref _jitCompiled (mapInsert id residual (deref _jitCompiled));
  residual
