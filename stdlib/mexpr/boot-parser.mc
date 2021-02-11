-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "mexpr/ast.mc"
include "mexpr/info.mc"
include "mexpr/pprint.mc"
include "string.mc"
include "seq.mc"

let gstr = lam t. lam n. bootParserGetString t n
let gname = lam t. lam n. nameNoSym (bootParserGetString t n)
let gint = lam t. lam n. bootParserGetInt t n
let gfloat = lam t. lam n. bootParserGetFloat t n
let glistlen = lam t. lam n. bootParserGetListLength t n

let makeSeq = lam f. lam len.
  recursive
    let work = lam acc. lam n.
      if eqi n len then acc else work (snoc acc (f n)) (addi n 1)
  in
    work [] 0


lang BootParser = MExprAst
  sem parseMExprString =
  | str ->
    let t = bootParserParseMExprString str in
    matchTerm t (bootParserGetId t)

  sem gconst(t:Unkown) =
  | n -> let t2 = bootParserGetConst t n in
         matchConst t2 (bootParserGetId t2)

  sem matchConst (t:Unknown) =
  | 300 /-CBool-/  -> CBool {val = eqi (gint t 0) 1 }
  | 301 /-CInt-/   -> CInt {val = gint t 0 } 
  | 302 /-CFloat-/ -> CFloat {val = gfloat t 0}
  | 303 /-CChar-/  -> CChar {val = int2char (gint t 0)}

  sem gterm (t:Unkown) =
  | n -> let t2 = bootParserGetTerm t n in
         matchTerm t2 (bootParserGetId t2)

  sem matchTerm (t:Unknown) =
  | 100 /-TmVar-/ ->
      TmVar {ident = gname t 0,
             ty = TyUnknown(),
             info = ginfo t}
  | 101 /-TmLam-/ ->
      TmLam {ident = gname t 0,
             ty = gtype t 0,
             info = ginfo t,
             body = gterm t 0}
  | 102 /-TmLet-/ ->
      TmLet {ident = gname t 0,
             tyBody = gtype t 0,
             body = gterm t 0,
             inexpr = gterm t 1,
             ty = TyUnknown(),
             fi = ginfo t}
  | 103 /-TmType-/ ->
      TmType {ident = gname t 0,
              ty = gtype t 0,
              inexpr = gterm t 0,
              fi = ginfo t}
  | 104 /-TmRecLets-/ ->
      TmRecLets {bindings =
                   makeSeq (lam n. {ident = gname t n,
                                 ty = gtype t n,
                                 body = gterm t n}) (glistlen t 0),
                 inexpr = gterm t (glistlen t 0),
                 ty = TyUnknown()}                            
  | 105 /-TmApp-/ ->
      TmApp {lhs = gterm t 0,
             rhs = gterm t 1,
             ty = TyUnknown(),
             fi = ginfo t}     
  | 106 /-TmConst-/ ->
      let c = gconst t 0 in
      TmConst {val = gconst t 0,
               ty = match c with CBool _ then TyBool {} else
                    match c with CInt _ then TyInt {} else
                    match c with CFloat _ then TyFloat {} else
                    TyChar {},
               fi = ginfo t}
  | 107 /-TmSeq-/ ->
      TmSeq {tms = makeSeq (lam n. gterm t n) (glistlen t 0),
             ty =  TyUnknown(),
             fi = ginfo t}
  | 108 /-TmRecord-/ ->
     let lst = makeSeq (lam n. (gstr t n, gterm t n)) (glistlen t 0) in
      TmRecord {bindings = seq2assoc {eq = eqString} lst,
               ty = TyUnknown(),
               fi = ginfo t}
  | 109 /-TmRecordUpdate-/ ->
     TmRecordUpdate {rec = gterm t 0,
                    key = gstr t 0,
                    value = gterm t 1,
                    ty = TyUnknown(),
                    fi = ginfo t}
  | 110 /-TmConDef-/ ->
     TmConDef {ident = gname t 0,
               ty = gtype t 0,
               inexpr = gterm t 0}
  | 111 /-TmConApp-/ ->
     TmConApp {ident = gname t 0,
               body = gterm t 0,
               ty = TyUnknown()}
  | 112 /-TmMatch-/ ->
     TmMatch {target = gterm t 0,
              pat = gpat t 0,
              thn = gterm t 1,
              els = gterm t 2,
              ty = TyUnknown(),
              fi = ginfo t}
  
  sem gpat (t:Unkown) =
  | n -> let t2 = bootParserGetPat t n in
         matchPat t2 (bootParserGetId t2)

  sem matchPat (t:Unknown) =
  | 400 /-PatNamed-/ -> PNamed {ident = strToPatName (gstr t 0)}
  | 401 /-PatSeqTot-/ ->
    PSeqTot {pats = makeSeq (lam n. gpat t n) (glistlen t 0) }
  | 402 /-PatSeqEdge-/ ->
    let len = glistlen t 0 in
    PSeqEdge {prefix = makeSeq (lam n. gpat t n) len,
              middle = strToPatName (gstr t 0),
              postfix = makeSeq (lam n. gpat t (addi n len)) (glistlen t 1)}
  | 403 /-PatRecord-/ ->
     let lst = makeSeq (lam n. (gstr t n, gpat t n)) (glistlen t 0) in
     PRecord {bindings = seq2assoc {eq = eqString} lst}



/-
let idPatNamed = 400
let idPatSeqTot = 401
let idPatSeqEdge = 402
let idPatRecord = 403
let idPatCon = 404
let idPatInt = 405
let idPatChar = 406
let idPatBool = 407
let idPatAnd = 408
let idPatOr = 409
let idPatNot = 410
-/

  -- Functions for transferring types and info are not yet implemented.  
  -- These functions are place holders.
  sem gtype (t:Unknown) = | n -> TyUnknown()
  sem ginfo = | t -> NoInfo()

  sem strToPatName =
  | "" ->  PWildcard ()
  | x -> PName (nameNoSym x)

end

lang BootParserTest = BootParser + MExprPrettyPrint 

mexpr
use BootParserTest in


-- Tests where strings of MExpr text is parsed and then pretty printed again.
-- All terms are tested in this way.
let norm = lam str. 
  filter (lam x. not (or (or (eqChar x ' ') (eqChar x '\n')) (eqChar x '\t'))) str in

let parse = lam s. expr2str (parseMExprString s) in
let lside = lam s. norm (parse s) in
let rside = norm in

-- TmVar and TmLam
let s = "_asdXA123" in
utest lside s with rside s in
let s = "lam x. lam y. x" in
utest lside s with rside s in

-- TmLet, TmLam
let s = "let y = lam x.x in y" in
utest lside s with rside s in

-- TmType
let s = "type Foo in x" in
utest lside s with rside s in

-- TmRecLets, TmLam
let s = "recursive let x = lam x.x in x" in
utest lside s with rside s in
let s = "recursive let x = lam x.x let y = lam x. x in y" in
utest lside s with rside s in

-- TmApp, TmLam
let s = "(lam x. lam y. x) z1 z2" in
utest lside s with rside s in

-- TmConst
let s = "true" in
utest lside s with rside s in
let s = "false" in
utest lside s with rside s in
let s = "123" in
utest lside s with rside s in
let s = "1.70e+1" in
utest lside s with rside s in
let s = "'a'" in
utest lside s with rside s in

-- TmSeq
let s = "\"\"" in
utest lside s with rside s in
let s = "[3,4,1123,21,91]" in
utest lside s with rside s in
let s = "[[1],[12,42311],[23,21,91]]" in
utest lside s with rside s in
let s = "\"Hello world\"" in
utest lside s with rside s in

-- TmRecord
let s = "{}" in
utest lside s with rside s in
let s = "{a = 5}" in
utest lside s with rside s in
let s = "{foo = 123, bar = \"Hello\"}" in
utest lside s with rside s in

-- TmRecordUpdate
let s = "{a with foo = 5}" in
utest lside s with rside s in
let s = "{{foo=7, bar='a'} with bar = 'b'}" in
utest lside s with rside s in

-- TmConDef
let s = "con Foo in x" in
utest lside s with rside s in
let s = "con Foo : Int -> Tree in x" in
utest lside s with rside "con Foo in x" in

-- TmConApp
let s = "Foo {a = 5}" in
utest lside s with rside s in

-- TmMatch, PatNamed
let s = "match 5 with x then x else 2" in
utest lside s with rside s in
let s = "match foo with _ then 7 else 2" in
utest lside s with rside s in

-- TmMatch, PatSeqTot, PatSeqEdge
let s = "match x with \"\" then x else 2" in
utest lside s with rside s in
let s = "match x with [x,y,z] then x else 2" in
utest lside s with rside s in
let s = "match x with [a] ++ v ++ [x,y,z] then x else 2" in
utest lside s with rside s in
let s = "match x with \"\" ++ x ++ [y] then x else x" in
utest lside s with rside s in
let s = "match x with [z] ++ x ++ \"\" then z else 2" in
utest lside s with rside s in

--TmMatch, PatRecord
let s = "match x with {} then x else 2" in
utest lside s with rside s in
let s = "match x with {foo=x, bar=_} then x else 2" in
utest lside s with rside s in

()
