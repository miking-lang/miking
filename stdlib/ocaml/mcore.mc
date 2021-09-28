include "mexpr/type-annot.mc"
include "mexpr/type-lift.mc"
include "ocaml/generate.mc"
include "ocaml/pprint.mc"

lang MCoreCompileLang =
  MExprTypeAnnot + MExprTypeLift +
  OCamlPrettyPrint + OCamlTypeDeclGenerate + OCamlGenerate +
  OCamlGenerateExternalNaive
end

type Hooks =
  { debugTypeAnnot : Expr -> ()
  , debugGenerate : String -> ()
  , exitBefore : () -> ()
  , compileOcaml : [String] -> [String] -> String -> String
  }

let emptyHooks : Hooks =
  { debugTypeAnnot = lam. ()
  , debugGenerate = lam. ()
  , exitBefore = lam. ()
  , compileOcaml = lam. lam. lam. ""
  }

let collectLibraries : ExternalNameMap -> ([String], [String])
= lam extNameMap.
  let f = lam s. lam str. setInsert str s in
  let g = lam acc : (Set String, Set String). lam impl :  ExternalImpl.
    match acc with (libs, clibs) then
      (foldl f libs impl.libraries, foldl f clibs impl.cLibraries)
    else never
  in
  let h = lam acc. lam. lam impls. foldl g acc impls in
  match mapFoldWithKey h (setEmpty cmpString, setEmpty cmpString) extNameMap
  with (libs, clibs) then (setToSeq libs, setToSeq clibs)
  else never

let compileMCore : Expr -> Hooks -> String =
  lam ast. lam hooks.
  use MCoreCompileLang in
  let ast = typeAnnot ast in
  let ast = removeTypeAscription ast in

  -- If option --debug-type-annot, then pretty-print the AST
  hooks.debugTypeAnnot ast;

  match typeLift ast with (env, ast) then
    match generateTypeDecls env with (env, typeTops) then
      let env : GenerateEnv = chooseExternalImpls globalExternalImplsMap env ast in
      let exprTops = generateTops env ast in

      -- Collect external library dependencies
      match collectLibraries env.exts with (libs, clibs) then
        let ocamlProg = pprintOcamlTops (concat typeTops exprTops) in

        -- If option --debug-generate, print the AST
        hooks.debugGenerate ocamlProg;

        -- If option --exit-before, exit the program
        hooks.exitBefore ();

        -- Compile OCaml AST
        hooks.compileOcaml libs clibs ocamlProg
      else never
    else never
  else never
