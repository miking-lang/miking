-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "ast.mc"
include "eq.mc"
include "info.mc"
include "pprint.mc"
include "const-transformer.mc"
include "string.mc"
include "stringid.mc"
include "seq.mc"
include "name.mc"

let gstr = lam t. lam n. bootParserGetString t n
let gname = lam t. lam n. nameNoSym (bootParserGetString t n)
let gint = lam t. lam n. bootParserGetInt t n
let gfloat = lam t. lam n. bootParserGetFloat t n
let glistlen = lam t. lam n. bootParserGetListLength t n


lang BootParser = MExprAst + ConstTransformer

  -- Parse a complete MCore file, including MLang code
  -- This function returns the final MExpr AST. The MCore
  -- file can refer to other files using include statements
  sem parseMCoreFile (keywords : [String]) =
  | filename ->
    let t = bootParserParseMCoreFile keywords filename in
    constTransform (matchTerm t (bootParserGetId t))

  -- Parses an MExpr string and returns the final MExpr AST
  sem parseMExprString (keywords : [String]) =
  | str ->
    let t = bootParserParseMExprString keywords str in
    constTransform (matchTerm t (bootParserGetId t))

  -- Get term help function
  sem gterm (t:Unknown) =
  | n -> let t2 = bootParserGetTerm t n in
         matchTerm t2 (bootParserGetId t2)

  -- Match term from ID
  sem matchTerm (t:Unknown) =
  | 100 /-TmVar-/ ->
    TmVar {ident = gname t 0,
           ty = tyunknown_,
           info = ginfo t 0}
  | 101 /-TmApp-/ ->
    TmApp {lhs = gterm t 0,
           rhs = gterm t 1,
           ty = tyunknown_,
           info = ginfo t 0}
  | 102 /-TmLam-/ ->
    TmLam {ident = gname t 0,
           tyIdent = gtype t 0,
           ty = tyunknown_,
           info = ginfo t 0,
           body = gterm t 0}
  | 103 /-TmLet-/ ->
    TmLet {ident = gname t 0,
           tyBody = gtype t 0,
           body = gterm t 0,
           inexpr = gterm t 1,
           ty = tyunknown_,
           info = ginfo t 0}
  | 104 /-TmRecLets-/ ->
    TmRecLets {bindings =
               create (glistlen t 0)
                      (lam n. {ident = gname t n,
                               tyBody = gtype t n,
                               body = gterm t n,
                               ty = tyunknown_,
                               info = ginfo t (addi n 1)}),
               inexpr = gterm t (glistlen t 0),
               ty = tyunknown_,
               info = ginfo t 0}
  | 105 /-TmConst-/ ->
    let c = gconst t 0 in
    TmConst {val = gconst t 0,
             ty = tyunknown_,
             info = ginfo t 0}
  | 106 /-TmSeq-/ ->
    TmSeq {tms = create (glistlen t 0) (lam n. gterm t n),
           ty =  tyunknown_,
           info = ginfo t 0}
  | 107 /-TmRecord-/ ->
    let lst = create (glistlen t 0) (lam n. (gstr t n, gterm t n)) in
    TmRecord {bindings =
                mapFromList cmpSID
                  (map (lam b : (a,b). (stringToSid b.0, b.1)) lst),
              ty = tyunknown_,
              info = ginfo t 0}
  | 108 /-TmRecordUpdate-/ ->
    TmRecordUpdate {rec = gterm t 0,
                   key = stringToSid (gstr t 0),
                   value = gterm t 1,
                   ty = tyunknown_,
                   info = ginfo t 0}
  | 109 /-TmType-/ ->
    TmType {ident = gname t 0,
            tyIdent = gtype t 0,
            ty = tyunknown_,
            inexpr = gterm t 0,
            info = ginfo t 0}
  | 110 /-TmConDef-/ ->
    TmConDef {ident = gname t 0,
              tyIdent = gtype t 0,
              inexpr = gterm t 0,
              ty = tyunknown_,
              info = ginfo t 0}
  | 111 /-TmConApp-/ ->
    TmConApp {ident = gname t 0,
              body = gterm t 0,
              ty = tyunknown_,
              info = ginfo t 0}
  | 112 /-TmMatch-/ ->
    TmMatch {target = gterm t 0,
             pat = gpat t 0,
             thn = gterm t 1,
             els = gterm t 2,
             ty = tyunknown_,
             info = ginfo t 0}
  | 113 /-TmUtest-/ ->
    let tusing = match (glistlen t 0) with 4 then
                   Some (gterm t 3)
                 else None () in
    TmUtest {test = gterm t 0,
             expected = gterm t 1,
             next = gterm t 2,
             tusing = tusing,
             ty = tyunknown_,
             info = ginfo t 0}
  | 114 /-TmNever-/ ->
    TmNever {ty = tyunknown_,
             info = ginfo t 0}
  | 115 /-TmExt-/ ->
    TmExt {ident = gname t 0,
           effect = neqi (gint t 0) 0,
           ty = gtype t 0,
           inexpr = gterm t 0,
           info = ginfo t 0}

  -- Get type help function
  sem gtype(t:Unknown) =
  | n -> let t2 = bootParserGetType t n in
        matchType t2 (bootParserGetId t2)

  sem matchType (t:Unknown) =
  | 200 /-TyUnknown-/ ->
    TyUnknown {info = ginfo t 0}
  | 201 /-TyBool-/ ->
    TyBool {info = ginfo t 0}
  | 202 /-TyInt-/ ->
    TyInt {info = ginfo t 0}
  | 203 /-TyFloat-/ ->
    TyFloat {info = ginfo t 0}
  | 204 /-TyChar-/ ->
    TyChar {info = ginfo t 0}
  | 205 /-TyArrow-/ ->
    TyArrow {info = ginfo t 0,
             from = gtype t 0,
             to = gtype t 1}
  | 206 /-TySeq-/ ->
    TySeq {info = ginfo t 0,
           ty = gtype t 0}
  | 207 /-TyRecord-/ ->
    let lst = create (glistlen t 0) (lam n. (gstr t n, gtype t n)) in
    TyRecord {info = ginfo t 0,
              labels = map (lam b : (String, a). stringToSid b.0) lst,
              fields = mapFromList cmpSID (map (lam b : (a,b). (stringToSid b.0, b.1)) lst)}
  | 208 /-TyVariant-/ ->
    if eqi (glistlen t 0) 0 then
      TyVariant {info = ginfo t 0,
                 constrs = mapEmpty nameCmp}
    else error "Parsing of non-empty variant types not yet supported"
  | 209 /-TyVar-/ ->
    TyVar {info = ginfo t 0,
           ident = gname t 0}
  | 210 /-TyApp-/ ->
    TyApp {info = ginfo t 0,
           lhs = gtype t 0,
           rhs = gtype t 1}
  | 211 /-TyTensor-/ ->
    TyTensor {info = ginfo t 0,
              ty = gtype t 0}

  -- Get constant help function
  sem gconst(t:Unknown) =
  | n -> let t2 = bootParserGetConst t n in
         matchConst t2 (bootParserGetId t2)

  -- Match constant from ID
  sem matchConst (t:Unknown) =
  | 300 /-CBool-/   -> CBool {val = eqi (gint t 0) 1 }
  | 301 /-CInt-/    -> CInt {val = gint t 0 }
  | 302 /-CFloat-/  -> CFloat {val = gfloat t 0}
  | 303 /-CChar-/   -> CChar {val = int2char (gint t 0)}
  | 304 /-Cdprint-/ -> CDPrint {}
  | 305 /-Cerror-/  -> CError {}

  -- Get pattern help function
  sem gpat (t:Unknown) =
  | n -> let t2 = bootParserGetPat t n in
         matchPat t2 (bootParserGetId t2)

  -- Match pattern from ID
  sem matchPat (t:Unknown) =
  | 400 /-PatNamed-/ ->
    PatNamed {ident = strToPatName (gstr t 0),
            info = ginfo t 0}
  | 401 /-PatSeqTot-/ ->
    PatSeqTot {pats = create (glistlen t 0) (lam n. gpat t n),
             info = ginfo t 0}
  | 402 /-PatSeqEdge-/ ->
    let len = glistlen t 0 in
    PatSeqEdge {prefix = create len (lam n. gpat t n),
              middle = strToPatName (gstr t 0),
              postfix = create (glistlen t 1) (lam n. gpat t (addi n len)),
              info = ginfo t 0}
  | 403 /-PatRecord-/ ->
    let lst = create (glistlen t 0) (lam n. (gstr t n, gpat t n)) in

    PatRecord {bindings =
               mapFromList cmpSID
                 (map (lam b : (a,b). (stringToSid b.0, b.1)) lst),
               info = ginfo t 0}
  | 404 /-PatCon-/ ->
     PatCon {ident = gname t 0,
             subpat = gpat t 0,
             info = ginfo t 0}
  | 405 /-PatInt-/ ->
     PatInt {val = gint t 0,
             info = ginfo t 0}
  | 406 /-PatChar-/ ->
     PatChar {val = int2char (gint t 0),
              info = ginfo t 0}
  | 407 /-PatBool-/ ->
     PatBool {val = eqi (gint t 0) 1,
              info = ginfo t 0}
  | 408 /-PatAnd-/ ->
     PatAnd {lpat = gpat t 0,
             rpat = gpat t 1,
             info = ginfo t 0}
  | 409 /-PatOr-/ ->
     PatOr {lpat = gpat t 0,
            rpat = gpat t 1,
            info = ginfo t 0}
  | 410 /-PatNot-/ ->
     PatNot {subpat = gpat t 0,
             info = ginfo t 0}


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


  sem strToPatName =
  | "" ->  PWildcard ()
  | x -> PName (nameNoSym x)

end

lang BootParserTest = BootParser + MExprPrettyPrint + MExprEq

mexpr
use BootParserTest in


-- Tests where strings of MExpr text is parsed and then pretty printed again.
-- All terms are tested in this way.
let norm : String -> String = lam str.
  filter (lam x. not (or (or (eqChar x ' ') (eqChar x '\n')) (eqChar x '\t'))) str in

-- Test the combination of parsing and pretty printing
let parse = lam ks. lam s. expr2str (parseMExprString ks s) in
let lside : [String] -> String -> String = lam ks. lam s. norm (parse ks s) in
let lsideClosed = lside [] in
let rside : String -> String = norm in

-- Test that info gives the right columns and rows
let l_info : [String] -> String -> Info = lam ks. lam s.
  infoTm (parseMExprString ks s) in
let l_infoClosed = l_info [] in
let r_info : Int -> Int -> Int -> Int -> Info = lam r1. lam c1. lam r2. lam c2.
      Info {filename = "internal", row1 = r1, col1 = c1, row2 = r2, col2 = c2} in

-- TmVar
let s = "_asdXA123" in
utest lside ["_asdXA123"] s with rside s in
utest match parseMExprString [""] "#var\"\"" with TmVar r
      then nameGetStr r.ident else "ERROR" with "" in

-- TmApp
let s = "f x" in
utest lside ["f", "x"] s with rside s in
utest l_info ["f1", "f2", "foo"] "   (foo f1) f2  " with r_info 1 4 1 14 in

-- TmLam
let s = "lam x. lam y. x" in
utest lsideClosed s with rside s in
let s = "(lam x. lam y. x) z1 z2" in
utest lside ["z1", "z2"] s with rside s in
utest l_info ["_aas_12"] "  _aas_12 " with r_info 1 2 1 9 in

-- TmLet, TmLam
let s = "let y = lam x.x in y" in
utest lsideClosed s with rside s in
utest l_infoClosed "  \n lam x.x" with r_info 2 1 2 8 in
utest infoTm (match parseMExprString [] s with TmLet r then r.body else ())
with r_info 1 8 1 15 in
utest l_info ["y"] "  let x = 4 in y  " with r_info 1 2 1 14 in
let s = "(printLn x); 10" in
utest lside ["printLn", "x"] s with rside s in

-- TmRecLets, TmLam
let s = "recursive let x = lam x.x in x" in
utest lsideClosed s with rside s in
let s = "recursive let x = lam x.x let y = lam x. x in y" in
utest lsideClosed s with rside s in
let s = "   recursive let x = 5 \n let foo = 7 in x " in
utest l_infoClosed s with r_info 1 3 2 15 in
utest
  match parseMExprString [] s with TmRecLets r then
    let fst : RecLetBinding = head r.bindings in
    fst.info
  else never
with r_info 1 13 1 22 in

-- TmConst
let s = "true" in
utest lsideClosed s with rside s in
let s = "false" in
utest lsideClosed s with rside s in
let s = "123" in
utest lsideClosed s with rside s in
let s = "17." in
utest lsideClosed s with rside s in
let s = "'a'" in
utest lsideClosed s with rside s in
utest l_infoClosed " true " with r_info 1 1 1 5 in
utest l_infoClosed "  false " with r_info 1 2 1 7 in
utest l_infoClosed " 1234 " with r_info 1 1 1 5 in
utest l_infoClosed " 123.121 " with r_info 1 1 1 8 in
utest l_infoClosed "\n  'A' " with r_info 2 2 2 5 in

-- TmSeq
let s = "\"\"" in
utest lsideClosed s with rside s in
let s = "[3,4,1123,21,91]" in
utest lsideClosed s with rside s in
let s = "[[1],[12,42311],[23,21,91]]" in
utest lsideClosed s with rside s in
let s = "\"Hello world\"" in
utest lsideClosed s with rside s in
utest l_infoClosed "  [12,2,1] " with r_info 1 2 1 10 in

-- TmRecord
let s = "{}" in
utest lsideClosed s with rside s in
let s = "{a = 5}" in
utest lsideClosed s with rside s in
let s = "{bar = \"Hello\", foo = 123}" in
let t = urecord_ [("bar", str_ "Hello"), ("foo", int_ 123)] in
utest parseMExprString [] s with t using eqExpr in
utest l_infoClosed " {} " with r_info 1 1 1 3 in
utest l_infoClosed " {foo = 123} " with r_info 1 1 1 12 in

-- TmRecordUpdate
let s = "{a with foo = 5}" in
utest lside ["a"] s with rside s in
let s = "{{bar='a', foo=7} with bar = 'b'}" in
let t = recordupdate_ (urecord_ [("bar", char_ 'a'), ("foo", int_ 7)]) "bar" (char_ 'b') in
utest parseMExprString [] s with t using eqExpr in
utest l_info ["foo"] " {foo with a = 18 } " with r_info 1 1 1 19 in

-- NOTE(caylak, 2021-03-17): Commented out because test fails since parsing of TyVariant is not supported yet
-- TmType
let s = "type Foo=<> in x" in
--utest lsideClosed s with rside s in
utest l_infoClosed "  type Bar in () " with r_info 1 2 1 13 in

-- TmConDef
let s = "con Foo in x" in
utest lside ["x"] s with rside s in
let s = "con Foo : (Int) -> (Tree) in x" in
utest lside ["x"] s with rside s in
utest l_infoClosed "  con Bar in 10 " with r_info 1 2 1 12 in

-- TmConApp
let s = "Foo {a = 5}" in
utest lside ["Foo"] s with rside s in
utest l_info ["Foo"] "  Foo {foo = 7, b = 3} " with r_info 1 2 1 22 in

-- TmMatch, PatNamed
let s =  "match 5 with x then x else 2" in
utest lsideClosed s with rside s in
let s = "match foo with _ then 7 else 2" in
utest lside ["foo"] s with rside s in
utest l_infoClosed "match [4] with x then x else [] " with r_info 1 0 1 31 in
let s = " match bar with Foo {a = x} then x else 2" in
utest match parseMExprString ["Foo", "bar"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 16 1 27 in

-- TmMatch, PatSeqTot, PatSeqEdge
let s = "match x with \"\" then x else 2" in
utest lside ["x"] s with rside s in
let s = "match x with [x,y,z] then x else 2" in
utest lside ["x"] s with rside s in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 13 1 20 in
let s = " match x with [a] ++ v ++ [x,y,z] then x else 2" in
utest lside ["x"] s with rside s in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 14 1 33 in
let s = "match x with \"\" ++ x ++ [y] then x else x" in
utest lside ["x"] s with rside s in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 13 1 27 in
let s = "match x with [z] ++ x ++ \"\" then z else 2" in
utest lside ["x"] s with rside s in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 13 1 27 in

--TmMatch, PatRecord
let s = "match x with {} then x else 2" in
utest lside ["x"] s with rside s in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 13 1 15 in
let s = "match x with {bar=_, foo=x} then x else 2" in
let t = match_ (var_ "x")
               (prec_ [("bar", pvarw_), ("foo", pvar_ "x")])
               (var_ "x") (int_ 2) in
utest parseMExprString ["x"] s with t using eqExpr in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 13 1 27 in

--TmMatch, PatCon
let s = "match x with Foo {foo = x} then x else 100" in
utest lside ["x", "Foo"] s with rside s in
utest match parseMExprString ["x", "Foo"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 13 1 26 in

--TmMatch, PatInt, PatBool, PatChar
let s = "match x with [1,2,12] then x else x" in
utest lside ["x"] s with rside s in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 13 1 21 in
let s = "match x with 'A' then x else x" in
utest lside ["x"] s with rside s in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 13 1 16 in
let s = "match x with [true,false] then x else x" in
utest lside ["x"] s with rside s in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 13 1 25 in

-- TmMatch, PatAnd, PatOr, PatNot
let s = "match x with 1 & x then x else x" in
utest lside ["x"] s with rside s in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 13 1 18 in
let s = "match x with 1 | x then x else x" in
utest lside ["x"] s with rside s in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 13 1 18 in
let s = "match x with !y then x else x" in
utest lside ["x"] s with rside s in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 13 1 15 in
let s = "match 1 with (a & b) | (!c) then x else x" in
utest lside ["x"] s with rside s in
utest match parseMExprString ["x"] s with TmMatch r then infoPat r.pat else ()
with r_info 1 14 1 26 in

-- TmUtest
let s = "utest lam x.x with 4 in 0" in
utest lsideClosed s with rside s in
utest l_infoClosed "\n utest 3 with 4 in () " with r_info 2 1 2 18 in

-- TmNever
let s = "never" in
utest lsideClosed s with rside s in
utest l_infoClosed "  \n  never " with r_info 2 2 2 7 in

-- TmExt
let s = "external y : Int in 1" in
utest lsideClosed s with rside s in
utest l_infoClosed "   \n  external y : Int in 1" with r_info 2 2 2 23 in

let s = "external y! : Int in 1" in
utest lsideClosed s with rside s in
utest l_infoClosed "   \n  external y! : Int in 1" with r_info 2 2 2 24 in

-- TyUnknown
let s = "let y:Unknown = lam x.x in y" in
utest lsideClosed s with rside "let y = lam x.x in y" in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 6 1 13 in
let s = "lam x:Int. lam y:Char. x" in
utest lsideClosed s with rside s in
utest match parseMExprString [] " \n lam x:Int. lam y:Char. x" with TmLam l then infoTy l.tyIdent else ()
with r_info 2 7 2 10 in

-- TyInt
let s = "let y:Int = lam x.x in y" in
utest lsideClosed s with rside s in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 6 1 9 in

-- TyFloat
let s = "let y:Float = lam x.x in y" in
utest lsideClosed s with rside s in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 6 1 11 in

-- TyChar
let s = "let y:Char = lam x.x in y" in
utest lsideClosed s with rside s in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 6 1 10 in

-- TyArrow
let s = "let y:(Int)->(Int) = lam x.x in y" in
utest lsideClosed s with rside s in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 7 1 17 in

-- Nested TyArrow
let s = "let y:([Float])->(Int) = lam x.x in y" in
utest lsideClosed s with rside s in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 7 1 21 in

-- TySeq
let s = "let y:[Int] = lam x.x in y" in
utest lsideClosed s with rside s in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 6 1 11 in

-- Nested TySeq
let s = "let y:[{a:{a_1:Int,a_2:Float},b:{b_1:[Char],b_2:Float}}]= lam x.x in y" in
let recTy = tyseq_ (tyrecord_ [
  ("a", tyrecord_ [
    ("a_1", tyint_),
    ("a_2", tyfloat_)]),
  ("b", tyrecord_ [
    ("b_1", tystr_),
    ("b_2", tyfloat_)])]) in
let typedLet = lam letTy.
  bind_ (let_ "y" letTy (ulam_ "x" (var_ "x")))
        (var_ "y") in
utest parseMExprString [] s with typedLet recTy using eqExpr in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 6 1 56 in

-- TyTensor
let s = "let y:Tensor[Int] = lam x.x in y" in
utest lsideClosed s with rside s in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 6 1 17 in

-- Nested TyTensor
let s = "let y:{a:Tensor[Char],b:Float}= lam x.x in y" in
let recTy = tyseq_ (tyrecord_ [
    ("a", tytensor_ tychar_),
    ("b", tyfloat_)
  ])
in
let typedLet = lam letTy.
  bind_ (let_ "y" letTy (ulam_ "x" (var_ "x")))
        (var_ "y") in
utest parseMExprString [] s with typedLet recTy using eqExpr in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 6 1 30 in

-- TyRecord
let s = "let y:{a:Int,b:[Char]} = lam x.x in y" in
let recTy = tyrecord_ [("a", tyint_), ("b", tystr_)] in
utest parseMExprString [] s with typedLet recTy using eqExpr in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 6 1 22 in

-- Nested TyRecord
let s = "let y:{a:{a_1:Int,a_2:Float},b:{b_1:[Char],b_2:Float}} = lam x.x in y" in
let recTy = tyrecord_ [
  ("a", tyrecord_ [
    ("a_1", tyint_),
    ("a_2", tyfloat_)]),
  ("b", tyrecord_ [
    ("b_1", tystr_),
    ("b_2", tyfloat_)])] in
utest parseMExprString [] s with typedLet recTy using eqExpr in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 6 1 54 in

-- TyVariant
let s = "let y:<> = lam x.x in y" in
-- NOTE(caylak,2021-03-17): Parsing of TyVariant is not supported yet
--utest lsideClosed s with rside s in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 6 1 8 in

-- TyVar
let s = "let y:_asd = lam x.x in y" in
utest lsideClosed s with rside s in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 6 1 10 in

-- TyApp
let s = "let y:((Int)->(Int))(Int) = lam x.x in y" in
utest lsideClosed s with rside s in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 8 1 24 in

-- Nested TyApp
let s = "let y:((((Int)->(Int))(Int))->(Int))(Int) = lam x.x in y" in
utest lsideClosed s with rside s in
utest match parseMExprString [] s with TmLet l then infoTy l.tyBody else ()
with r_info 1 10 1 40 in
()
