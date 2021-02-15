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

  -- Get term help function
  sem gterm (t:Unkown) =
  | n -> let t2 = bootParserGetTerm t n in
         matchTerm t2 (bootParserGetId t2)

  -- Match term from ID
  sem matchTerm (t:Unknown) =
  | 100 /-TmVar-/ ->
      TmVar {ident = gname t 0,
             ty = TyUnknown(),
             info = ginfo t 0}
  | 101 /-TmApp-/ ->
      TmApp {lhs = gterm t 0,
             rhs = gterm t 1,
             ty = TyUnknown(),
             info = ginfo t 0}     
  | 102 /-TmLam-/ ->
      TmLam {ident = gname t 0,
             ty = gtype t 0,
             info = ginfo t 0,
             body = gterm t 0}
  | 103 /-TmLet-/ ->
      TmLet {ident = gname t 0,
             tyBody = gtype t 0,
             body = gterm t 0,
             inexpr = gterm t 1,
             ty = TyUnknown(),
             info = ginfo t 0}
  | 104 /-TmRecLets-/ ->
      TmRecLets {bindings =
                   makeSeq (lam n. {ident = gname t n,
                                 ty = gtype t n,
                                 body = gterm t n}) (glistlen t 0),
                                 info = ginfo t (addi n 1),
                 inexpr = gterm t (glistlen t 0),
                 ty = TyUnknown(),
                 info = ginfo t 0}                            
  | 105 /-TmConst-/ ->
      let c = gconst t 0 in
      TmConst {val = gconst t 0,
               ty = match c with CBool _ then TyBool {} else
                    match c with CInt _ then TyInt {} else
                    match c with CFloat _ then TyFloat {} else
                    TyChar {},
               info = ginfo t 0}
  | 106 /-TmSeq-/ ->
      TmSeq {tms = makeSeq (lam n. gterm t n) (glistlen t 0),
             ty =  TyUnknown(),
             info = ginfo t 0}
  | 107 /-TmRecord-/ ->
     let lst = makeSeq (lam n. (gstr t n, gterm t n)) (glistlen t 0) in
      TmRecord {bindings = seq2assoc {eq = eqString} lst,
               ty = TyUnknown(),
               info = ginfo t 0}
  | 108 /-TmRecordUpdate-/ ->
     TmRecordUpdate {rec = gterm t 0,
                    key = gstr t 0,
                    value = gterm t 1,
                    ty = TyUnknown(),
                    info = ginfo t 0}
  | 109 /-TmType-/ ->
      TmType {ident = gname t 0,
              ty = gtype t 0,
              inexpr = gterm t 0,
              info = ginfo t 0}
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
              info = ginfo t 0}
  | 113 /-TmUtest-/ ->
     TmUtest {test = gterm t 0,
              expected = gterm t 1,
              next = gterm t 2,  
              ty = TyUnknown()}
  | 114 /-TmNever-/ ->
     TmNever {ty = TyUnknown(),
              info = ginfo t 0}

  -- Get constant help function
  sem gconst(t:Unkown) =
  | n -> let t2 = bootParserGetConst t n in
         matchConst t2 (bootParserGetId t2)

  -- Match constant from ID
  sem matchConst (t:Unknown) =
  | 300 /-CBool-/  -> CBool {val = eqi (gint t 0) 1 }
  | 301 /-CInt-/   -> CInt {val = gint t 0 } 
  | 302 /-CFloat-/ -> CFloat {val = gfloat t 0}
  | 303 /-CChar-/  -> CChar {val = int2char (gint t 0)}

  -- Get pattern help function
  sem gpat (t:Unkown) =
  | n -> let t2 = bootParserGetPat t n in
         matchPat t2 (bootParserGetId t2)

  -- Match pattern from ID
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
  | 404 /-PatCon-/ ->
     PCon {ident = gname t 0, 
           subpat = gpat t 0}
  | 405 /-PatInt-/ ->     
     PInt {val = gint t 0}
  | 406 /-PatChar-/ ->     
     PChar {val = int2char (gint t 0)}
  | 407 /-PatBool-/ ->     
     PBool {val = eqi (gint t 0) 1,
            info = ginfo t 0}
  | 408 /-PatAnd-/ ->     
     PAnd {lpat = gpat t 0,
           rpat = gpat t 1}
  | 409 /-PatOr-/ ->     
     POr {lpat = gpat t 0,
           rpat = gpat t 1}
  | 410 /-PatNot-/ ->     
     PNot {subpat = gpat t 0}


  -- Get info help function
  sem ginfo (t:Unknown) =
  | n -> let t2 = bootParserGetInfo t n in
         matchInfo t2 (bootParserGetId t2)

  -- Match info from ID
  sem matchInfo (t:Unknown) =
  | 500 /-Info-/ -> 
      Info {filename = gstr t 0,
            row1 = gint t 0,
            col1 = gint t 1,
            row2 = gint t 2,
            col2 = gint t 3}
  | 501 /-NoInfo-/ ->
      NoInfo {} 


  -- Functions for transferring types and info are not yet implemented.  
  -- These functions are place holders.
  sem gtype (t:Unknown) = | n -> TyUnknown()

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

-- Test the combination of parsing and pretty printing
let parse = lam s. expr2str (parseMExprString s) in
let lside = lam s. norm (parse s) in
let rside = norm in

-- Test that info gives the right columns and rows
let l_info = lam s.  info (parseMExprString s) in
let r_info = lam r1. lam c1. lam r2. lam c2.
      Info {filename = "internal", row1 = r1, col1 = c1, row2 = r2, col2 = c2} in

-- TmVar 
let s = "_asdXA123" in
utest lside s with rside s in

-- TmApp
let s = "f x" in
utest lside s with rside s in
utest l_info "   (foo f1) f2  " with r_info 1 4 1 14 in

-- TmLam
let s = "lam x. lam y. x" in
utest lside s with rside s in
let s = "(lam x. lam y. x) z1 z2" in
utest lside s with rside s in
utest l_info "  _aas_12 " with r_info 1 2 1 9 in

-- TmLet, TmLam
let s = "let y = lam x.x in y" in
utest lside s with rside s in
utest l_info "  \n lam x.x" with r_info 2 1 2 8 in
utest info (match parseMExprString s with TmLet r then r.body else ())
with r_info 1 8 1 15 in
utest l_info "  let x = 4 in y  " with r_info 1 2 1 14 in

-- TmRecLets, TmLam
let s = "recursive let x = lam x.x in x" in
utest lside s with rside s in
let s = "recursive let x = lam x.x let y = lam x. x in y" in
utest lside s with rside s in
utest l_info "   recursive let x = 5 \n let foo = 7 in x "  with r_info 1 3 2 15 in

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

-- TmType
let s = "type Foo in x" in
utest lside s with rside s in

-- TmConDef

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

--TmMatch, PatCon
let s = "match x with Foo {foo = x} then x else 100" in
utest lside s with rside s in

--TmMatch, PatInt, PatBool, PatChar
let s = "match x with [1,2,12] then x else x" in
utest lside s with rside s in
let s = "match x with 'A' then x else x" in
utest lside s with rside s in
let s = "match x with [true,false] then x else x" in
utest lside s with rside s in

-- TmMatch, PatAnd, PatOr, PatNot
let s = "match x with 1 & x then x else x" in
utest lside s with rside s in
let s = "match x with 1 | x then x else x" in
utest lside s with rside s in
let s = "match x with !y then x else x" in
utest lside s with rside s in
let s = "match 1 with (a & b) | (!c) then x else x" in
utest lside s with rside s in

-- TmUtest
let s = "utest lam x.x with 4 in 0" in
utest lside s with rside s in

-- TmNever
let s = "never" in
utest lside s with rside s in

()
