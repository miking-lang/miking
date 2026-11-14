-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- A lightweight compiler holding the minimal amount of code needed to
-- bootstrap `mi` through the `ecmascript` backend.

include "basic-types.mc"
include "map.mc"
include "name.mc"
include "option.mc"
include "seq.mc"
include "stdlib.mc"
include "string.mc"
include "sys.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/builtin.mc"
include "mexpr/deadcode.mc"
include "mexpr/generate-pprint.mc"
include "mexpr/generate-utest.mc"
include "mexpr/shallow-patterns.mc"
include "mexpr/type-check.mc"
include "mlang/loader.mc"
include "parser/loader.mc"
include "ocaml/compile.mc"
include "ocaml/mcore.mc"

lang MCoreESLiteCompile =
  ComposedMCoreLoader + NativeParserLoader +
  DPrintViaPprintLoader + StripUtestLoader +
  OldDPrintViaPprint + MExprGeneratePprint + GeneratePprintMissingCase +
  MExprLowerNestedPatterns + MExprDeadcodeElimination + MCoreCompileLang
end

type ESLiteOptions = {
  disableOptimizations: Bool,
  output: Option String
}

let esLiteOptionsDefault : ESLiteOptions = {
  disableOptimizations = false,
  output = None ()
}

-- NOTE(larshum, 2021-03-22): This does not work for Windows file paths.
let filename = lam path.
  match strLastIndex '/' path with Some idx then
    subsequence path (addi idx 1) (length path)
  else path

let filenameWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename

let ocamlCompile : ESLiteOptions -> String -> [String] -> [String] -> String -> String =
  lam options. lam sourcePath. lam libs. lam clibs. lam ocamlProg.
  let compileOptions : CompileOptions =
    let opts = { defaultCompileOptions with libraries = libs, cLibraries = clibs } in
    if options.disableOptimizations then { opts with optimize = false } else opts
  in
  let p : CompileResult = ocamlCompileWithConfig compileOptions ocamlProg in
  let destinationFile =
    switch options.output
    case None () then filenameWithoutExtension (filename sourcePath)
    case Some o then o
    end
  in
  sysMoveFile p.binaryPath destinationFile;
  sysChmodWriteAccessFile destinationFile;
  p.cleanup ();
  destinationFile

-- This is a minimal copy of compileViaLoader in compile.mc
let compile : ESLiteOptions -> String -> () = lam options. lam file.
  use MCoreESLiteCompile in
  let sourcePath = stdlibMkExplicitPreferLocal file in

  let loader = mkLoader typcheckEnvDefault [] in
  let loader = enableNativeParser loader in

  let loader = addHook loader (StripUtestHook ()) in

  let loader =
    let loader = enableDPrintViaPprint loader in
    match includeFileExn "." "stdlib::string.mc" loader with (stringEnv, loader) in
    let symName = nameSym "s" in
    let symPprint =
      nulam_ symName (concat_ (str_ "sym (")
        (concat_
          (app_ (nvar_ (_getVarExn "int2string" stringEnv)) (app_ (uconst_ (CSym2hash ())) (nvar_ symName)))
          (str_ ")"))) in
    registerCustomPprintFunction (mapFindExn "Symbol" builtinTypeNames) symPprint loader in

  let loader =
    (includeFileTypeExn (FMCore {includeMExpr = true}) "." sourcePath loader).1 in

  let ast = buildFullAst loader in
  let ast = removeMetaVarExpr ast in
  let ast = lowerAll ast in
  let ast = deadcodeElimination ast in
  let ast = forceLazyExpr ast in
  let ast = removeOpaqueExpr ast in

  compileMCore ast (mkEmptyHooks (ocamlCompile options sourcePath));
  ()

mexpr

let usage = join
[ "Usage: mi-es-lite compile [<options>] file\n\n"
, "Options:\n"
, "  --native-parser          Accepted and ignored, always used\n"
, "  --disable-optimizations  Compile the OCaml output without optimizations\n"
, "  --output <file>          Write the result here\n" ] in

recursive let parseArgs = lam args. lam options : ESLiteOptions. lam file.
  switch args
    case [] then (options, file)
    case ["compile"] ++ rest then parseArgs rest options file
    case ["--native-parser"] ++ rest then parseArgs rest options file
    case ["--disable-optimizations"] ++ rest then
      parseArgs rest { options with disableOptimizations = true } file
    case ["--output"] ++ rest then
      match rest with [out] ++ rest
      then parseArgs rest { options with output = Some out } file
      else error "mi-es-lite: --output requires an argument"
    case [arg] ++ rest then
      match arg with "--" ++ _ then
        error (join ["mi-es-lite: unknown option ", arg])
      else match file with Some _ then
        error "mi-es-lite: only one file can be compiled at a time"
      else parseArgs rest options (Some arg)
  end
in

match parseArgs (tail argv) esLiteOptionsDefault (None ()) with (options, file) in
match file with Some file then compile options file
else print usage
