
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "options.mc"
include "seq.mc"
include "name.mc"


include "mexpr/boot-parser.mc"
include "mexpr/ast-builder.mc"
include "mexpr/symbolize.mc"
include "mexpr/mexpr.mc"
include "mexpr/builtin.mc"
include "mexpr/eval.mc"
include "mexpr/type-annot.mc"
include "mexpr/type-lift.mc"
include "mexpr/utesttrans.mc"



lang ExtMCore =
  BootParser + MExpr + MExprTypeAnnot + MExprTypeLift + MExprUtestTrans + MExprEval
end

let generateTests = lam ast. lam testsEnabled.
  use ExtMCore in
  if testsEnabled then
    let ast = symbolize ast in
    let ast = typeAnnot ast in
    utestGen ast
  else
    let symEnv = {symEnvEmpty with varEnv = builtinNameMap} in
    (symEnv, utestStrip ast)


-- Function for updating the builtin environment to also include
-- program specific arguments
let updateBuiltinWithArgs = lam args. lam builtinEnv.
  let n = nameNoSym "argv" in
  let argsTerm = seq_ (map str_ args) in
  let f = lam acc. lam k. lam v.
             if nameEqStr k n then mapInsert k argsTerm acc
             else mapInsert k v acc in
  mapFoldWithKey f (mapEmpty nameCmp) builtinEnv



-- Main function for evaluating a program using the interpreter
-- files: a list of files
-- options: the options structure to the main program
-- args: the program arguments to the executed program, if any
let eval = lam files. lam options : Options. lam args.
  use ExtMCore in
  let evalFile = lam file.
    let ast = parseMCoreFile [] file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    match generateTests ast options.runTests with (symEnv, ast) then
      let ast = symbolizeExpr symEnv ast in
      if options.exitBefore then exit 0
      else
        eval {env = updateBuiltinWithArgs args builtinEnv} ast
    else never
  in
  iter evalFile files
