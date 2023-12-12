include "sys.mc"
include "ocaml/ast.mc"
include "set.mc"
include "ext/ext-test.ext-ocaml.mc"           -- For testing
include "ext/math-ext.ext-ocaml.mc"
include "ext/dist-ext.ext-ocaml.mc"
include "ext/matrix-ext.ext-ocaml.mc"
include "ext/file-ext.ext-ocaml.mc"
include "ext/toml-ext.ext-ocaml.mc"
include "ext/async-ext.ext-ocaml.mc"
include "ext/rtppl-ext.ext-ocaml.mc"
include "ext/array-ext.ext-ocaml.mc"
include "sundials/sundials.ext-ocaml.mc"
include "sundials/ida.ext-ocaml.mc"
include "sundials/cvode.ext-ocaml.mc"
include "sundials/kinsol.ext-ocaml.mc"
include "multicore/atomic.ext-ocaml.mc"
include "multicore/thread.ext-ocaml.mc"
include "multicore/mutex.ext-ocaml.mc"
include "multicore/cond.ext-ocaml.mc"
include "ipopt/ipopt.ext-ocaml.mc"


type ExternalImpl = {
  expr : String,
  ty : use Ast in Type,
  libraries : [String],
  cLibraries : [String]
}

-- NOTE(oerikss, 2021-04-30) Add your external maps here. This is a temporary
-- solution. In the end we want to provide these definitions outside the
-- compiler (which will require some parsing).
let globalExternalImplsMap : Map String [ExternalImpl] =
  foldl1 mapUnion
    [
      extTestMap,               -- For testing purposes
      mathExtMap,
      arrayExtMap,
      sundialsExtMap,
      idaExtMap,
      cvodeExtMap,
      kinsolExtMap,
      atomicExtMap,
      threadExtMap,
      mutexExtMap,
      condExtMap,
      distExtMap,
      matrixExtMap,
      fileExtMap,
      ipoptExtMap,
      tomlExtMap,
      asyncExtMap,
      rtpplExtMap
    ]

-- List OCaml packages available on the system. These are returned on the format
-- (name, version). If `dune` is not available on the system, an empty
-- sequence is returned.
let externalListOcamlPackages : () -> [(String, String)] = lam.
  let res = mapEmpty cmpString in
  if sysCommandExists "dune" then
    let tempDir = sysTempDirMake () in
    match sysRunCommand [
      "dune", "installed-libraries", "--root", tempDir
    ] "" "." with
      {stdout = stdout, returncode = returncode}
    then
      sysTempDirDelete tempDir ();
      if eqi 0 returncode then
        -- Format is: `name (version: info)` delimited by newline
        let pkgs = map (strSplit "(version: ") (strSplit "\n" stdout) in
        let pkgs =
          map (lam x. (strTrim (head x), (init (join ((tail x)))))) pkgs
        in
        pkgs
      else
        printError
          (join
            ["externalListOcamlPackages: failed to run `dune installed-libraries`",
             " cannot automatically find ocaml packages available the system\n"]);
        flushStderr;
        []
    else never
  else
    printError
      (join
        ["externalListOcamlPackages: dune not in PATH, cannot",
         " automatically find ocaml packages available the system\n"]);
    flushStderr;
    []

-- Filters all external implementations defined in `globalExternalImplsMap` to
-- implementations supported on the current system.
let externalGetSupportedExternalImpls : () -> Map String [ExternalImpl] = lam.
  let syslibs =
    setOfSeq cmpString
      (map (lam x : (String, String). x.0) (externalListOcamlPackages ()))
  in
  -- We are unable to list available OCaml packages for this system so we
  -- assume that all dependencies are met.
  if setIsEmpty syslibs then globalExternalImplsMap
  -- Filter implementations to include only those with met dependencies on this
  -- system.
  else
    let newMap = mapEmpty cmpString in
    mapFoldWithKey
      (lam acc : Map String [ExternalImpl].
       lam x : String.
       lam impls : [ExternalImpl].
        let impls =
          filter
            (lam impl : ExternalImpl.
              forAll (lam lib. setMem lib syslibs) impl.libraries)
          impls
        in
        match impls with [] then acc else mapInsert x impls acc)
        (mapEmpty cmpString)
        globalExternalImplsMap
