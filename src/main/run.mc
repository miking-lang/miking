
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "seq.mc"
include "mexpr/boot-parser.mc"
include "mexpr/ast-builder.mc"
include "mexpr/symbolize.mc"
include "mexpr/mexpr.mc"
include "mexpr/builtin.mc"

lang ExtMCore = BootParser + MExpr

let run = lam files. lam options.
  use ExtMCore in

  -- Parse MCore files and return a list of ASTs
  let asts = map parseMCoreFile files in
  
  -- If option --debug-parse, then pretty print all the ASTs
  (if options.debugParse then print (strJoin "\n" (map expr2str asts)) else ());

  -- Evaluate list of programs
  let env = map (lam x. match x with (s,c) then (nameSym s, const_ c) else never) builtin in
  let names = match unzip env with (n,_) then n else never in
  let eval = lam t. eval {env = env} (symbolizeExpr (symVarNameEnv names) t) in
  map eval asts


  
