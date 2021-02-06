

-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "ast.mc"

-- Terms --
let idTmVar     = 100
let idTmLam     = 101
let idTmLet     = 102
let idTmType    = 103
let idTmRecLets = 104
let idTmApp     = 105
let idTmConst   = 106
let idTmSeq     = 107
let idTmRecord  = 108
let idTmRecordUpdate = 109
let idTmCondef  = 110
let idTmConapp  = 111
let idTmMatch   = 112
let idTmUse     = 113
let idTmUtest   = 114
let idTmNever   = 115
let idTmClos    = 116
let idTmFix     = 117

-- Types --
let idTyUnknown = 200
let idTyBool    = 201
let idTyInt     = 202
let idTyFloat   = 203
let idTyChar    = 204
let idTyArrow   = 205
let idTySeq     = 206
let idTyRecord  = 207
let idTyVariant = 208
let idTyVar     = 209
let idTyApp     = 210



let bootParse = lam str. ()     -- bootParse
let bootParserGetId = lam t. idTmVar --bootParserGetId

let gint = lam t. lam n. addi n 1 -- bootParserGetInt
let gbool = lam t. lam n. true    --boolParserGetBool



lang BootParser = VarAst + AppAst + FunAst + ConstAst

  sem parse =
  | str ->
    let t = bootParse str in
    parseInternal t (bootParserGetId t)

  sem parseInternal (t:Unknown) =
  | idTmVar -> TmVar {ident = nameNoSym (gint t 0)}
      
    

end


