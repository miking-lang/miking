
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
  let env = map (lam x. match x with (s,c) then (nameSym s, const_ c) else never) builtin in
  let names = match unzip env with (n,_) then n else never in
  let runFile = lam file.
    let ast = parseMCoreFile file in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    let ast = typeAnnot ast in

    -- If option --test, then generate utest runner calls. Otherwise strip away
    -- all utest nodes from the AST.
    let ast =
      if options.runTests then
        utestGen ast
      else
        utestStrip ast
    in

    -- Evaluate the symbolized program
    eval {env = env} (symbolizeExpr (symVarNameEnv names) ast)
  in
  iter runFile files
