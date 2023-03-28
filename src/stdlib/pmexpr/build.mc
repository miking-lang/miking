include "c/compile.mc"
include "c/pprint.mc"
include "cuda/cuda-utils.mc"
include "cuda/pprint.mc"
include "futhark/pprint.mc"
include "pmexpr/classify.mc"
include "ocaml/pprint.mc"
include "sys.mc"

let cudaCodeName = "mexpr-cuda"
let futharkCodeName = "mexpr-futhark"
let futharkWrapperCodeName = "mexpr-futhark-wrap"

let filename = lam path.
  match strLastIndex '/' path with Some idx then
    subsequence path (addi idx 1) (length path)
  else path

let filenameWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename

lang PMExprBuildBase =
  PMExprClassify + FutharkAst + CudaAst + OCamlTopAst + CProgAst

  -- TODO(larshum, 2022-06-06): Move this to separate file defining the
  -- compilation process (in standard library).
  syn GpuCompileResult =
  | FutharkCompileResult (FutProg, CProg)
  | CudaCompileResult CudaProg

  type AcceleratedCode = Map Class GpuCompileResult

  sem hasAcceleratedCuda : AcceleratedCode -> Bool
  sem hasAcceleratedCuda =
  | ac -> optionIsSome (mapLookup (Cuda ()) ac)

  sem hasAcceleratedFuthark : AcceleratedCode -> Bool
  sem hasAcceleratedFuthark =
  | ac -> optionIsSome (mapLookup (Futhark ()) ac)

  type PMExprBuildOptions = {
    debugGenerate : Bool,
    output : Option String,
    file : String,
    libs : [String],
    clibs : [String],
    ocamlTops : [Top],
    acceleratedCode : AcceleratedCode
  }
end

lang PMExprBuildConfig = PMExprBuildBase
  type BuildConfig = (String, String)

  sem _duneBaseConfig : String -> String -> String
  sem _duneBaseConfig libstr =
  | flagstr ->
    strJoin "\n" [
      "(env",
      "  (dev",
      (join ["    (flags (", flagstr, "))"]),
      "    (ocamlc_flags (-without-runtime))))",
      "(executable",
      "  (name program)",
      join ["  (libraries ", libstr, ")"]]

  sem _duneConfig : PMExprBuildOptions -> String -> String
  sem _duneConfig options =
  | dir ->
    let libstr = strJoin " " (distinct eqString (cons "boot" options.libs)) in
    let flagstr =
      let clibstr =
        strJoin " " (map (concat "-cclib -l") (distinct eqString options.clibs))
      in
      concat ":standard -w a " clibstr
    in
    let buildCuda = hasAcceleratedCuda options.acceleratedCode in
    let buildFuthark = hasAcceleratedFuthark options.acceleratedCode in
    let baseConfig = _duneBaseConfig libstr flagstr in
    -- NOTE(larshum, 2022-05-16): Choose dune configurations based on which
    -- kinds of acceleration are used in the program.
    if and buildCuda buildFuthark then
      let linkFlags = join [
        "  (link_flags -I ", dir, " -cclib -l", cudaCodeName,
        "\n    -cclib -lcuda -cclib -lcudart -cclib -lnvrtc -cclib -lstdc++)"] in
      let foreignStubs = join [
        "  (foreign_stubs (language c) (names ", futharkCodeName, " ",
        futharkWrapperCodeName, ")))"] in
      strJoin "\n" [baseConfig, linkFlags, foreignStubs]
    else if buildCuda then
      let linkFlags = join [
        "  (link_flags -I ", dir, " -cclib -l", cudaCodeName, " -cclib -lcudart -cclib -lstdc++))"
      ] in
      strJoin "\n" [baseConfig, linkFlags]
    else if buildFuthark then
      let foreignStubs = join [
        "  (foreign_stubs (language c) (names ", futharkCodeName, " ",
        futharkWrapperCodeName, ")))"
      ] in
      strJoin "\n" [
        baseConfig,
        "  (link_flags -cclib -lcuda -cclib -lcudart -cclib -lnvrtc)",
        foreignStubs]
    else
      concat baseConfig ")"

  sem _makefileConfig : AcceleratedCode -> String
  sem _makefileConfig =
  | acceleratedCode ->
    let buildCuda = hasAcceleratedCuda acceleratedCode in
    let buildFuthark = hasAcceleratedFuthark acceleratedCode in
    let cudaLibFile = join ["lib", cudaCodeName, ".a"] in
    let futharkCCodeFile = concat futharkCodeName ".c" in
    let futharkWrapperFile = concat futharkWrapperCodeName ".c" in
    let extraDependencies =
      if and buildCuda buildFuthark then
        strJoin " " [cudaLibFile, futharkCCodeFile, futharkWrapperFile]
      else if buildCuda then
        cudaLibFile
      else if buildFuthark then
        strJoin " " [futharkCCodeFile, futharkWrapperFile]
      else ""
    in
    let outdir = "_build/" in
    let outexec = concat outdir "default/program.exe" in
    let rebuildRules = strJoin "\n" [
      "clean:",
      join ["\trm -rf ", outdir, " ", extraDependencies],
      concat "rebuild: clean " outexec] in
    strJoin "\n" [
      join [outexec, ": program.ml ", extraDependencies],
      "\tdune build $@",
      join [cudaLibFile, ": ", cudaCodeName, ".cu"],
      "\tnvcc -I`ocamlc -where` $^ -lib -O3 -o $@",
      join [futharkCCodeFile, ": ", futharkCodeName, ".fut"],
      "\tfuthark cuda --library $^",
      rebuildRules]

  sem buildConfig : PMExprBuildOptions -> String -> BuildConfig
  sem buildConfig options =
  | dir ->
    ( _duneConfig options dir
    , _makefileConfig options.acceleratedCode )
end

lang PMExprBuildPrint = OCamlAst + CAst + CProgAst + FutharkAst + CudaAst

  sem _pprintOCamlTops : [Top] -> String
  sem _pprintOCamlTops =
  | tops ->
    use OCamlPrettyPrint in
    pprintOcamlTops tops

  sem _pprintCAst : CProg -> String
  sem _pprintCAst =
  | cProg ->
    use CPrettyPrint in
    use CProgPrettyPrint in
    printCProg [] cProg

  sem _pprintFutharkAst : FutProg -> String
  sem _pprintFutharkAst =
  | futProg ->
    use FutharkPrettyPrint in
    printFutProg futProg

  sem _pprintCudaAst : CudaProg -> String
  sem _pprintCudaAst =
  | cudaAst ->
    use CudaPrettyPrint in
    printCudaProg cCompilerNames cudaAst
end

lang PMExprBuild = PMExprBuildConfig + PMExprBuildPrint
  sem addAccelerateBackendFiles : [(String, String)] -> GpuCompileResult
                               -> [(String, String)]
  sem addAccelerateBackendFiles files =
  | FutharkCompileResult (futharkAst, wrapperAst) ->
    concat
      files
      [ (concat futharkWrapperCodeName ".c", _pprintCAst wrapperAst)
      , (concat futharkCodeName ".fut", _pprintFutharkAst futharkAst) ]
  | CudaCompileResult cudaAst ->
    concat
      files
      [ (concat cudaCodeName ".cu", _pprintCudaAst cudaAst)
      , ("cuda-utils.cuh", cudaUtilsCode) ]

  sem addFileData : PMExprBuildOptions -> BuildConfig -> [(String, String)]
  sem addFileData options =
  | (dune, make) ->
    let baseFiles = [
      ("program.ml", _pprintOCamlTops options.ocamlTops),
      ("program.mli", ""),
      ("dune", dune),
      ("dune-project", "(lang dune 2.0)"),
      ("Makefile", make)] in
    foldl addAccelerateBackendFiles baseFiles
      (mapValues options.acceleratedCode)

  sem _writeFiles : String -> [(String, String)] -> ()
  sem _writeFiles dir =
  | files ->
    let tempfile = lam f. sysJoinPath dir f in
    iter
      (lam fstr : (String, String).
        match fstr with (filename, text) in
        writeFile (tempfile filename) text)
      files

  sem buildBinaryUsingMake : PMExprBuildOptions -> String -> ()
  sem buildBinaryUsingMake options =
  | td ->
    let dir = sysTempDirName td in
    let r = sysRunCommand ["make"] "" dir in
    (if neqi r.returncode 0 then
      print (join ["Compilation failed:\n\n", r.stderr]);
      sysTempDirDelete td;
      exit 1
    else ());
    let binPath = sysJoinPath dir "_build/default/program.exe" in
    let destFile =
      match options.output with Some o then o
      else filenameWithoutExtension (filename options.file) in
    sysMoveFile binPath destFile;
    sysChmodWriteAccessFile destFile;
    sysTempDirDelete td ();
    ()

  -- TODO: Update uses of 'acceleratedCode' such that we can make the build
  -- process extensible.
  sem buildAccelerated : PMExprBuildOptions -> ()
  sem buildAccelerated =
  | options ->
    let td = sysTempDirMake () in
    let dir = sysTempDirName td in
    let config = buildConfig options dir in
    let files = addFileData options config in
    _writeFiles dir files;
    (if options.debugGenerate then
      printLn (join ["Output files saved at '", dir, "'"]);
      exit 0
    else ());
    buildBinaryUsingMake options td
end
