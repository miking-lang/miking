include "mexpr.mc"
include "mcore_parser.mc"

mexpr

use MExpr in

-- TODO: Define remaining built-ins
let builtins =
    [("not", TmConst CNot)
    ,("and", TmConst CAnd)
    ,("or", TmConst COr)
    ,("addi", TmConst CAddi)
    ,("eqi", TmConst CEqi)
] in

if or (eqstr (nth argv 1) "test") (lti (length argv) 3) then
  ()
else
  let file = nth argv 2 in
  if fileExists file then
    let contents = readFile file in
    let res = run_parser file program contents in
    match res with Success t then
      let _ = print_ln "Parsing successful!" in
      let p = t.0 in
      eval builtins p
    else
      print_ln (show_error res)
  else
    print_ln (concat "Unknown file: " file)
