-- Defines functions for compiling (and running) an MCore program.

include "mexpr/remove-ascription.mc"
include "mexpr/type-annot.mc"
include "mexpr/type-lift.mc"
include "ocaml/generate.mc"
include "ocaml/pprint.mc"
include "sys.mc"

type Hooks a =
  { debugTypeAnnot : Expr -> ()
  , debugGenerate : String -> ()
  , exitBefore : () -> ()
  , postprocessOcamlTops : [Top] -> [Top]
  , compileOcaml : [String] -> [String] -> String -> a
  }

let mkEmptyHooks : all a. ([String] -> [String] -> String -> a) -> Hooks a =
  lam compileOcaml.
  { debugTypeAnnot = lam. ()
  , debugGenerate = lam. ()
  , exitBefore = lam. ()
  , postprocessOcamlTops = lam tops. tops
  , compileOcaml = compileOcaml
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

  sem isRegular : Pat -> Bool
  sem isRegular =
  | PatAnd _ | PatOr _ | PatNot _ -> true
  | _ -> false

  sem isPatNamed : Bool -> Pat -> Bool
  sem isPatNamed acc =
  | PatNamed _ -> acc
  | _ -> false

  sem isNested : Bool -> Pat -> Bool
  sem isNested acc =
  | PatNamed _ | PatInt _ | PatChar _ | PatBool _ -> false
  | PatSeqTot t -> not (foldl isPatNamed true t.pats)
  | PatSeqEdge t -> not (foldl isPatNamed true (concat t.prefix t.postfix))
  | PatRecord t -> not (foldl isPatNamed true (mapValues t.bindings))
  | PatCon t -> not (isPatNamed true t.subpat)

  sem printNestedPatterns : () -> Expr -> ()
  sem printNestedPatterns acc =
  | TmMatch t ->
    printNestedPatterns acc t.target;
    (if isRegular t.pat then
      printLn "Found regular pattern";
      dprintLn t.pat
    else if isNested false t.pat then
      dprintLn t.pat
    else ());
    printNestedPatterns acc t.thn;
    printNestedPatterns acc t.els
  | t -> sfold_Expr_Expr printNestedPatterns acc t

  sem compileMCore : all a. Expr -> Hooks a -> a
  sem compileMCore ast =
  | hooks ->
    printNestedPatterns () ast;
    let ast = typeAnnot ast in
    let ast = removeTypeAscription ast in

    -- If option --debug-type-annot, then pretty-print the AST
    hooks.debugTypeAnnot ast;

    match typeLift ast with (env, ast) in
    match generateTypeDecls env with (env, typeTops) in
    let env : GenerateEnv =
      chooseExternalImpls (externalGetSupportedExternalImpls ()) env ast
    in
    let exprTops = generateTops env ast in
    let exprTops = hooks.postprocessOcamlTops exprTops in

    -- List OCaml packages availible on the system.
    let syslibs =
      setOfSeq cmpString
        (map (lam x : (String, String). x.0) (externalListOcamlPackages ()))
    in

    -- Collect external library dependencies
    match collectLibraries env.exts syslibs with (libs, clibs) in
    let ocamlProg =
      use OCamlPrettyPrint in
      pprintOcamlTops (concat typeTops exprTops)
    in

    -- If option --debug-generate, print the AST
    hooks.debugGenerate ocamlProg;

    -- If option --exit-before, exit the program
    hooks.exitBefore ();

    -- Compile OCaml AST
    hooks.compileOcaml libs clibs ocamlProg

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
end
