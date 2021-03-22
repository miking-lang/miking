
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "seq.mc"
include "mexpr/boot-parser.mc"
include "mexpr/ast-builder.mc"
include "mexpr/symbolize.mc"
include "mexpr/mexpr.mc"
include "mexpr/builtin.mc"
include "mexpr/type-annot.mc"
include "mexpr/utesttrans.mc"

lang ExtMCore = BootParser + MExpr + MExprTypeAnnot + MExprUtestTrans

let run = lam files. lam options.
  use ExtMCore in
  let builtinNames = map (lam x. x.0) builtinEnv in
  let runFile = lam file.
    let ast = parseMCoreFile file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    let ast =
      if options.runTests then
        -- Add type annotations as they are required by utestGen
        let ast = typeAnnot ast in
        utestGen ast
      else
        utestStrip ast
    in

    -- Evaluate the symbolized program
    eval {env = builtinEnv} (symbolizeExpr (symVarNameEnv builtinNames) ast)
  in
  iter runFile files
