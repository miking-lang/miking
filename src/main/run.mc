
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "seq.mc"
include "mexpr/boot-parser.mc"
include "mexpr/mexpr.mc"

lang ExtMCore = BootParser + MExpr

let run = lam files. lam options.
  use ExtMCore in

  -- Parse MCore files and return a list of ASTs
  let asts = map parseMCoreFile files in

  -- If option --print-ast, then pretty print all the ASTs
  (if options.printAst then print (strJoin "\n" (map expr2str asts)) else ());

  -- Evaluate list of programs
  let eval = lam t. eval {env = assocEmpty} (symbolize t) in
  map eval asts


  
