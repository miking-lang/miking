-- Defines functions for compiling (and running) an MCore program.

include "mexpr/remove-ascription.mc"
include "mexpr/type-annot.mc"
include "mexpr/type-lift.mc"
include "mexpr/ast-builder.mc"
include "ocaml/generate.mc"
include "ocaml/pprint.mc"
include "sys.mc"
include "seq.mc"
include "string.mc"

type Hooks a =
  { debugTypeAnnot : Expr -> ()
  , debugGenerate : String -> ()
  , exitBefore : () -> ()
  , postprocessOcamlTops : [Top] -> [Top]
  , compileOcaml : [String] -> [String] -> String -> a
  , compileOcamlPEval : Option ([String] -> [String] -> String -> String -> a)
  , nameMap : Option (Map Name String)
  }

let mkEmptyHooks : all a. ([String] -> [String] -> String -> a) -> Hooks a =
  lam compileOcaml.
  { debugTypeAnnot = lam. ()
  , debugGenerate = lam. ()
  , exitBefore = lam. ()
  , postprocessOcamlTops = lam tops. tops
  , compileOcaml = compileOcaml
  , compileOcamlPEval = None ()
  , nameMap = None ()
  }

lang MCoreCompileLang =
  MExprTypeAnnot + MExprRemoveTypeAscription + MExprTypeLift +
  OCamlTypeDeclGenerate + OCamlGenerate + OCamlGenerateExternalNaive

  sem collectLibraries : Map Name [ExternalImpl] -> Set String -> ([String], [String])
  sem collectLibraries extNameMap =
  | syslibs ->
    let f = lam s. lam str. setInsert str s in
    let g = lam acc : (Set String, Set String). lam impl :  ExternalImpl.
      match acc with (libs, clibs) then
        (foldl f libs impl.libraries, foldl f clibs impl.cLibraries)
      else never
    in
    let h = lam acc. lam. lam impls. foldl g acc impls in
    match mapFoldWithKey h (setEmpty cmpString, setEmpty cmpString) extNameMap
    with (libs, clibs) then
      (setToSeq libs, setToSeq clibs)
    else never

  sem compileMCore : all a. Expr -> Hooks a -> a
  sem compileMCore ast =
  | hooks ->
    let ast = typeAnnot ast in
    let ast = removeTypeAscription ast in

    -- If option --debug-type-annot, then pretty-print the AST
    hooks.debugTypeAnnot ast;

    match typeLift ast with (env, ast) in
    match generateTypeDecls env with (env, typeTops) in
    let env : GenerateEnv =
      chooseExternalImpls (externalGetSupportedExternalImpls ()) env ast
    in
    match generateTops env ast with (entryPointId, exprTops) in
    -- If we are partially evaluating then we'll call into program.ml
    -- from elsewhere
    let exprTops = match hooks.compileOcamlPEval with Some _
      then init exprTops else exprTops in

    let exprTops = hooks.postprocessOcamlTops exprTops in

    -- List OCaml packages availible on the system.
    let syslibs =
      setOfSeq cmpString
        (map (lam x : (String, String). x.0) (externalListOcamlPackages ()))
    in

    -- Collect external library dependencies
    match collectLibraries env.exts syslibs with (libs, clibs) in

    let ppEnv = pprintEnvEmpty in
    let ppEnv = match hooks.nameMap with Some n
      then {ppEnv with nameMap = n, strings = setOfSeq cmpString (mapValues n)}
      else ppEnv in

    match use OCamlPrettyPrint in
        pprintOcamlTopsAndEnv ppEnv (concat typeTops exprTops)
    with (pprintEnv, ocamlProg) in

    -- If option --debug-generate, print the AST
    hooks.debugGenerate ocamlProg;

    -- If option --exit-before, exit the program
    hooks.exitBefore ();

    -- Compile OCaml AST
    match hooks.compileOcamlPEval with Some comp then
      use OCamlPrettyPrint in
      match pprintVarName pprintEnv entryPointId with (_, entryPointName) in
      comp libs clibs ocamlProg entryPointName
    -- Normal compilation
    else hooks.compileOcaml libs clibs ocamlProg

  -- Compiles and runs the given MCore AST, using the given standard in and
  -- program arguments. The return value is a record containing the return code,
  -- the standard out and the standard error, based on the result of running the
  -- program.
  --
  -- If the compilation fails, the compile error will be printed and the program
  -- will exit.
  sem compileRunMCore : String -> [String] -> Expr -> ExecResult
  sem compileRunMCore stdin args =
  | ast ->
    let compileOcaml = lam libs. lam clibs. lam ocamlProg.
      let options = {optimize = true, libraries = libs, cLibraries = clibs} in
      let cunit : CompileResult = ocamlCompileWithConfig options ocamlProg in
      let res = cunit.run stdin args in
      cunit.cleanup ();
      res
    in
    compileMCore ast (mkEmptyHooks compileOcaml)

  sem compileMCorePlugin : all a. String -> Map Name String -> Expr -> Hooks a -> a
  sem compileMCorePlugin pluginId nameMap ast =
  | hooks ->
    let ast = typeAnnot ast in
    let ast = removeTypeAscription ast in

    -- If option --debug-type-annot, then pretty-print the AST
    hooks.debugTypeAnnot ast;

    match typeLift ast with (env, ast) in
    match generateTypeDecls env with (env, typeTops) in
    let env : GenerateEnv =
      chooseExternalImpls (externalGetSupportedExternalImpls ()) env ast
    in
    match generateTops env ast with (entryPointId, exprTops) in
    -- The main function will be called later separately
    let exprTops = init exprTops in
    let exprTops = hooks.postprocessOcamlTops exprTops in

    -- List OCaml packages availible on the system.
    let syslibs =
      setOfSeq cmpString
        (map (lam x : (String, String). x.0) (externalListOcamlPackages ()))
    in

    -- Collect external library dependencies
    match collectLibraries env.exts syslibs with (libs, clibs) in
    let ppEnv = pprintEnvEmpty in
    let ppEnv = {ppEnv with nameMap = nameMap,
                            strings = setOfSeq cmpString (mapValues nameMap)} in
    match use OCamlPrettyPrint in
        pprintOcamlTopsAndEnv (ppEnv) (concat typeTops exprTops)
    with (pprintEnv, ocamlProg) in

    match use OCamlPrettyPrint in
      pprintVarName pprintEnv entryPointId with (_, entryPointName) in

    let ocamlProg = join ["
    open Boot.Inter
    open Program

    module M:Boot.Inter.PLUG =
    struct ",
    ocamlProg,
    "
    let residual () = Obj.magic (", entryPointName, " ())
    end
    let () = Boot.Inter.register \"", pluginId, "\" (module M:Boot.Inter.PLUG)"] in

    -- If option --debug-generate, print the AST
    hooks.debugGenerate ocamlProg;

    -- If option --exit-before, exit the program
    hooks.exitBefore ();

    -- Compile OCaml AST
    hooks.compileOcaml libs clibs ocamlProg
end
