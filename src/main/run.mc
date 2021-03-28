
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "seq.mc"
include "mexpr/boot-parser.mc"
include "mexpr/ast-builder.mc"
include "mexpr/symbolize.mc"
include "mexpr/mexpr.mc"
include "mexpr/builtin.mc"
include "mexpr/type-annot.mc"
include "mexpr/type-lift.mc"
include "mexpr/utesttrans.mc"

lang ExtMCore =
  BootParser + MExpr + MExprTypeAnnot + MExprTypeLift + MExprUtestTrans
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

let run = lam files. lam options.
  use ExtMCore in
  let runFile = lam file.
    let ast = parseMCoreFile file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    match generateTests ast options.runTests with (symEnv, ast) then
      let ast = symbolizeExpr symEnv ast in
      eval {env = builtinEnv} ast
    else never
  in
  iter runFile files
