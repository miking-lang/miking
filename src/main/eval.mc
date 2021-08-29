
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
include "mexpr/remove-ascription.mc"
include "mexpr/type-lift.mc"
include "mexpr/utesttrans.mc"



lang ExtMCore =
  BootParser + MExpr + MExprTypeAnnot + MExprTypeLift + MExprUtestTrans +
  MExprProfileInstrument + MExprEval

  sem updateArgv (args : [String]) =
  | TmConst r -> match r.val with CArgv () then seq_ (map str_ args) else TmConst r
  | t -> smap_Expr_Expr (updateArgv args) t

end

let generateTests = lam ast. lam testsEnabled.
  use ExtMCore in
  if testsEnabled then
    let ast = symbolize ast in
    let ast = typeAnnot ast in
    let ast = removeTypeAscription ast in
    utestGen ast
  else
    let symEnv = symEnvEmpty in
    (symEnv, utestStrip ast)

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

    let ast =
      if options.debugProfiling then
        instrumentProfiling (symbolize ast)
      else ast
    in

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    match generateTests ast options.runTests with (symEnv, ast) then
      let ast = symbolizeExpr symEnv ast in
      if options.exitBefore then exit 0
      else
        eval {env = mapEmpty nameCmp} (updateArgv args ast)
    else never
  in
  iter evalFile files
