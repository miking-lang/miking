include "mexpr/ast.mc"
include "ocaml/mcore.mc"

type LibCompileResult = {
  cleanup : () -> (),
  libPath : String
}


let compileOcamlLibrary : String -> [String] -> [String] -> String -> LibCompileResult =
  lam id. lam libs. lam clibs. lam ocamlProg.

  let td = sysTempDirMake () in
  let dir = sysTempDirName td in
  let tempfile = lam f. sysJoinPath dir f in
--  let t = tempfile (join ["plugin.ml"]) in
  let t = tempfile (concat id ".ml") in
  writeFile t ocamlProg;
  -- Assume that needed dependencies are present in the cwd
  let includePath = sysGetCwd () in

  let command = ["ocamlfind", "ocamlopt -O3 -package boot -shared -I ", includePath,
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

-- To keep track of names that have previously been JIT compiled
let _jitCompiled = ref (mapEmpty nameCmp)

let jitCompile : all a. Name -> Map Name String -> Expr -> a =
  lam id. lam pprintEnv.  lam e.
  -- With current implementation, each residual must be uniquely identified when
  -- dynamically loaded.
  let counter = match mapLookup id (deref _jitCompiled) with Some lastCount
    then addi lastCount 1 else 1 in

  modref _jitCompiled (mapInsert id counter (deref _jitCompiled));

  let nameToStr = lam id.
    let s = nameGetStr id in
    match nameGetSym id with Some sym then
        join [s, "_", int2string (sym2hash sym), "_", int2string counter]
    else s
  in

  let residualId = concat "mexpr_jit_" (nameToStr id) in
  let p =
    use MCoreCompileLang in
    compileMCorePlugin residualId pprintEnv e
      (mkEmptyHooks (compileOcamlLibrary residualId))
  in
  loadLibraries p.libPath;
  p.cleanup ();
  let residual = getExternal residualId in
  unsafeCoerce residual
