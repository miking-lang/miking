-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "string.mc"
include "seq.mc"
include "ast.mc"
include "ast-builder.mc"
include "eq.mc"
include "info.mc"
include "parser/lexer.mc"

type ParseResult a = {val : a, pos : Pos, str: String}
type StrPos = {str : String, pos : Pos}

-- Commbined WSAC parser for MExpr
lang MExprWSACParser = WhitespaceParser + LineCommentParser + MultilineCommentParser
end

-- Top of the expression parser. Connects WSAC with parsing of other non terminals
lang ExprParser = WSACParser + Ast
  sem parseExpr (p: Pos) =
  | s ->
    let r1 : ParseResult Expr = parseExprMain p 0 s in
    let r2 : StrPos = eatWSAC r1.pos r1.str in
    if eqi (length r2.str) 0 then r1.val
    else posErrorExit r2.pos "Parse error. Unknown characters."

  sem parseExprMain (p: Pos) (prec: Int) =
  | s ->
    let r1 : StrPos = eatWSAC p s in
    let exp : ParseResult Expr = parseExprImp r1.pos r1.str in
    let r2 : StrPos = eatWSAC exp.pos exp.str in
    parseInfix r2.pos prec exp r2.str

  sem parseInfix (p: Pos) (prec: Int) (exp: ParseResult Expr) =

  sem parseExprImp (p: Pos) =
  | _ -> posErrorExit p "Parse error. Unknown character sequence."
end


-- Include this fragment if there are no infix operations
lang ExprParserNoInfix = ExprParser
  sem parseInfix (p: Pos) (prec: Int) (exp: ParseResult Expr) =
  | _ -> exp
end

-- Parses an identfier that starts with a lower-case letter or a '_' if parameter
-- 'upper' is false, and starts with an upper-case letter if 'upper' is true.
-- The rest of the string can contain both upper and lower-case letters.
-- If no identifier, the 'val' field contains an empty string.
let parseIdent = lam upper. lam p. lam str.
  recursive
  let work = lam acc. lam first. lam p. lam str.
    match str with [x] ++ xs then
      let c = char2int x in
      let m1 = or (not first) upper in
      let m2 = or (not first) (not upper) in
      if or (or (and m1 (isUpperAlpha x))
                (and m2 (or (eqChar x '_') (isLowerAlpha x))))
	    (and (not first) (isDigit x))
      then work (snoc acc x) false (advanceCol p 1) xs
      else {val = acc, pos = p, str = str}
    else {val = acc, pos = p, str = str}
  in work "" true p str

let emptyStr : String = ""
utest parseIdent false (initPos "") "+"
  with {val = emptyStr, str = "+", pos = posVal "" 1 0}
utest parseIdent false (initPos "") "a "
  with {val = "a", str = " ", pos = posVal "" 1 1}
utest parseIdent false (initPos "") "ba"
  with {val = "ba", str = emptyStr, pos = posVal "" 1 2}
utest parseIdent false (initPos "") "_asd "
  with {val = "_asd", str = " ", pos = posVal "" 1 4}
utest parseIdent true (initPos "") "_asd "
  with {val = emptyStr, str = "_asd ", pos = posVal "" 1 0}
utest parseIdent false (initPos "") "Asd12 "
  with {val = emptyStr, str = "Asd12 ", pos = posVal "" 1 0}
utest parseIdent true (initPos "") "Asd12 "
  with {val = "Asd12", str = " ", pos = posVal "" 1 5}



-- Parse identifier
lang IdentParser = ExprParser
  sem parseExprImp (p: Pos) =
  | (['_' | 'a' | 'b' | 'c' | 'd' | 'e' | 'f' | 'g' | 'h' | 'i' | 'j' | 'k' |
      'l' | 'm' | 'n' | 'o' | 'p' | 'q' | 'r' | 's' | 't' | 'u' | 'v' | 'w' |
      'x' | 'y' | 'z' ] ++ s) & xs ->
    let r : ParseResult String = parseIdent false p xs in
    nextIdent p r.str r.val

  sem nextIdent (p: Pos) (xs: String) =
end


-- Parsing of boolean literals
lang BoolParser = ExprParser + IdentParser + ConstAst + BoolAst + UnknownTypeAst
  sem nextIdent (p: Pos) (xs: String) =
  | "true" ->
      let p2 = advanceCol p 4 in
      {val = TmConst {val = CBool {val = true},
                      ty = tyunknown_,
                      info = makeInfo p p2},
       pos = p2, str = xs}
  | "false" ->
      let p2 = advanceCol p 5 in
      {val = TmConst {val = CBool {val = false},
                      ty = tyunknown_,
                      info = makeInfo p p2},
       pos = p2, str = xs}
end

let parseUInt : Pos -> String -> {val: String, pos: Pos, str: String} =
  lam p. lam str.
  recursive
  let work = lam p2. lam str. lam num.
    match str with [x] ++ xs then
      let c = char2int x in
      if and (geqi c 48) (leqi c 57)
      then work (advanceCol p2 1) xs (snoc num x)
      else {val = num, pos = p2, str = str}
    else {val = num, pos = p2, str = str}
  in work p str ""

utest parseUInt (initPos "") "123"
  with {val = "123", pos = posVal "" 1 3, str = ""}
utest parseUInt (initPos "") "1 "
  with {val = "1", pos = posVal "" 1 1, str = " "}
utest parseUInt (initPos "") "12.0"
  with {val = "12", pos = posVal "" 1 2, str = ".0"}
utest parseUInt (initPos "") "2x"
  with {val = "2", pos = posVal "" 1 1, str = "x"}
utest parseUInt (initPos "") "Not a number"
  with {val = emptyStr, pos = posVal "" 1 0, str = "Not a number"}

let parseFloatExponent : Pos -> String -> {val: String, pos: Pos, str: String} =
  lam p. lam str.
    match str with ['+' | '-'] ++ xs & s then
      let n : ParseResult String = parseUInt (advanceCol p 1) xs in
      match n.val with "" then n
      else {val = cons (head s) n.val, pos = n.pos, str = n.str}
    else
      parseUInt p str

utest parseFloatExponent (initPos "") "1"
  with {val = "1", pos = posVal "" 1 1, str = ""}
utest parseFloatExponent (initPos "") "-12  "
  with {val = "-12", pos = posVal "" 1 3, str = "  "}
utest parseFloatExponent (initPos "") "+3"
  with {val = "+3", pos = posVal "" 1 2, str = ""}
utest parseFloatExponent (initPos "") "-2.5"
  with {val = "-2", pos = posVal "" 1 2, str = ".5"}
utest parseFloatExponent (initPos "") "Not an exponent"
  with {val = emptyStr, pos = posVal "" 1 0, str = "Not an exponent"}

-- Parsing of an unsigned number
lang UNumParser = ExprParser
  sem parseExprImp (p : Pos) =
  | (['0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ s) & xs ->
    let n : ParseResult String = parseUInt p xs in
    let nextChar = if null n.str then None () else Some (head n.str) in
    nextNum p n.str n.val nextChar

  sem nextNum (p: Pos) (xs: String) (nval: String) =
end

-- Parsing of an unsigned integer
lang UIntParser = UNumParser + ConstAst + IntAst + UnknownTypeAst
  sem nextNum (p: Pos) (xs: String) (nval: String) =
  | _ ->
    let p2 = advanceCol p (length nval) in
    {val = TmConst {val = CInt {val = string2int nval},
                    ty = tyunknown_,
                    info = makeInfo p p2},
     pos = p2, str = xs}
end

-- Parsing of an unsigned float
lang UFloatParser = UNumParser + ConstAst + FloatAst + IntAst + UnknownTypeAst
  sem nextNum (p: Pos) (xs: String) (nval: String) =
  | Some (('.' | 'e' | 'E') & c) ->
    let exponentHelper = lam pos. lam pre. lam expChar. lam s. lam isFloat.
      let exp : ParseResult String = parseFloatExponent (advanceCol pos 1) s in
      match exp.val with "" then
        let constVal =
          if isFloat then
            CFloat {val = string2float pre}
          else
            CInt {val = string2int pre}
        in {val = TmConst {val = constVal,
                           ty = tyunknown_,
                           info = makeInfo p pos},
            pos = pos, str = cons expChar s}
      else
        let floatStr = join [pre, "e", exp.val] in
        {val = TmConst {val = CFloat {val = string2float floatStr},
                        ty = tyunknown_,
                        info = makeInfo p exp.pos},
         pos = exp.pos, str = exp.str}
    in
    let p2 = advanceCol p (length nval) in
    match c with '.' then
      let p3 = advanceCol p2 1 in
      let s = tail xs in
      match s with ['0' | '1' | '2' | '3' | '4' |
                    '5' | '6' | '7' | '8' | '9'] ++ s2 then
        let n2 : ParseResult String = parseUInt p3 s in
        let preExponentStr = join [nval, ".", n2.val] in
        match n2.str with ['e' | 'E'] ++ s3 then
          exponentHelper n2.pos preExponentStr (head n2.str) s3 true
        else
          {val = TmConst {val = CFloat {val = string2float preExponentStr},
                          ty = tyunknown_,
                          info = makeInfo p n2.pos},
           pos = n2.pos, str = n2.str}
      else match s with ['e' | 'E'] ++ s2 then
        exponentHelper p3 nval (head s) s2 true
      else
        {val = TmConst {val = CFloat {val = string2float nval},
                        ty = tyunknown_,
                        info = makeInfo p p3},
         pos = p3, str = s}
    else match c with 'e' | 'E' then
      exponentHelper (advanceCol p (length nval)) nval c (tail xs) false
    else
      never
end

-- Fragment for simple parsing of keyword
lang KeywordUtils = WSACParser
  sem matchKeyword (keyword: String) (p: Pos) =
  | s ->
     let r : StrPos = eatWSAC p s in
     if isPrefix eqc keyword r.str then
       let l = length keyword in
       {pos = advanceCol r.pos l, str = subsequence r.str l (subi (length r.str) l)}
     else
       posErrorExit r.pos (join ["Unknown character. Expected '", keyword, "'."])
end


-- Parsing if expressions
lang IfParser =
  ExprParser + IdentParser + KeywordUtils +  MatchAst + BoolPat + UnknownTypeAst

  sem nextIdent (p: Pos) (xs: String) =
  | "if" ->
     let e1 : ParseResult Expr = parseExprMain (advanceCol p 2) 0 xs in
     let r1 : StrPos = matchKeyword "then" e1.pos e1.str in
     let e2 : ParseResult Expr = parseExprMain r1.pos 0 r1.str in
     let r2 : StrPos = matchKeyword "else" e2.pos e2.str  in
     let e3 : ParseResult Expr = parseExprMain r2.pos 0 r2.str in
     {val = TmMatch {target = e1.val, pat = ptrue_,
                     thn = e2.val, els = e3.val, ty = tyunknown_,
                     info = makeInfo p e3.pos},
      pos = e3.pos,
      str = e3.str}
 end



-- Parse parentheses
lang ParenthesesParser = ExprParser + KeywordUtils
  sem parseExprImp (p: Pos) =
  | "(" ++ xs ->
    let e : ParseResult Expr = parseExprMain (advanceCol p 1) 0 xs in
    let r : StrPos = matchKeyword ")" e.pos e.str in
    {val = e.val, pos = r.pos, str = r.str}
end

-- Parses a sequence of
lang SeqParser = ExprParser + KeywordUtils + SeqAst + UnknownTypeAst
  sem parseExprImp (p: Pos) =
  | "[" ++ xs ->
    recursive let work = lam acc. lam first. lam p2. lam str.
      let r : StrPos = eatWSAC p2 str in
      match r.str with "]" ++ xs then
        {val = TmSeq{tms = acc, ty = tyunknown_, info = makeInfo p (advanceCol r.pos 1)},
         pos = advanceCol r.pos 1, str = xs}
      else
        let r2 : StrPos =
          if first then r else matchKeyword "," r.pos r.str in
        let e : ParseResult Expr = parseExprMain r2.pos 0 r2.str in
        work (snoc acc e.val) false e.pos e.str
    in work [] true (advanceCol p 1) xs
end


-- Matches a character (including escape character).
let matchChar : Pos -> String -> {val: Char, pos: Pos, str: String} =
  lam p. lam str : String.
  let ret = lam c. lam s. lam n. {val = c, pos = (advanceCol p n), str = s} in
    match str with "\\" ++ xs then
      match xs with "\\" ++ xs then ret '\\' xs 2 else
      match xs with "n" ++ xs then ret '\n' xs 2 else
      match xs with "t" ++ xs then ret '\t' xs 2 else
      match xs with "\"" ++ xs then ret '\"' xs 2 else
      match xs with "'" ++ xs then ret '\'' xs 2 else
      posErrorExit (advanceCol p 1) "Unknown escape character."
    else match str with [x] ++ xs then ret x xs 1
    else posErrorExit p "Unexpected end of file."
    -- TODO (David, 2020-09-27): Shoud we allow newlines etc. inside strings
    -- TODO (David, 2020-09-27): Add all other relevant escape characters

-- Parses strings, including escape characters
lang StringParser = ExprParser + SeqAst + CharAst + UnknownTypeAst
  sem parseExprImp (p: Pos) =
  | "\"" ++ xs ->
    recursive let work = lam acc. lam p2. lam str : String.
      match str with "\"" ++ xs then
        {val = TmSeq {tms = acc, ty = tyunknown_,
                      info = makeInfo p (advanceCol p2 1)},
	                    pos = advanceCol p2 1, str = xs}
      else
        let r : ParseResult Char = matchChar p2 str in
        let v = TmConst {val = CChar {val = r.val}, ty = tyunknown_,
                         info = makeInfo p2 r.pos} in
	      work (snoc acc v) r.pos r.str
    in
    work [] (advanceCol p 1) xs
end

-- Parses character literals
lang CharParser = ExprParser + KeywordUtils + CharAst + UnknownTypeAst
  sem parseExprImp (p: Pos) =
  | "\'" ++ xs ->
      let r : ParseResult Char = matchChar (advanceCol p 1) xs in
      let r2 : StrPos = matchKeyword "\'" r.pos r.str in
      {val = TmConst {val = CChar {val = r.val}, ty = tyunknown_,
                      info = makeInfo p r2.pos},
       pos = r2.pos, str = r2.str}
end



-- Parse variable
lang VarParser = ExprParser + IdentParser + VarAst + UnknownTypeAst
  sem nextIdent (p: Pos) (xs: String) =
  | x ->
      let p2 = advanceCol p (length x) in
      {val = TmVar {ident = nameNoSym x, ty = tyunknown_, info = makeInfo p p2, frozen = false},
       pos = p2, str = xs}
end


-- Parsing of a lambda
lang FunParser =
  ExprParser + IdentParser + KeywordUtils + LamAst + UnknownTypeAst

  sem nextIdent (p: Pos) (xs: String) =
  | "lam" ->
    let r : StrPos = eatWSAC (advanceCol p 3) xs in
    let r2 : ParseResult String = parseIdent false r.pos r.str in
    let r3 : StrPos = matchKeyword "." r2.pos r2.str in
    let e : ParseResult Expr = parseExprMain r3.pos 0 r3.str in
    {val = TmLam {ident = nameNoSym r2.val, ty = tyunknown_,
                  tyAnnot = tyunknown_, tyParam = tyunknown_, body = e.val,
                  info = makeInfo p e.pos},
     pos = e.pos, str = e.str}
end


-- Parsing let expressions
lang LetParser =
  ExprParser + IdentParser + KeywordUtils + LetAst + UnknownTypeAst
  sem nextIdent (p: Pos) (xs: String) =
  | "let" ->
    let r : StrPos = eatWSAC (advanceCol p 3) xs in
    let r2 : ParseResult String = parseIdent false r.pos r.str in
    let r3 : StrPos = matchKeyword "=" r2.pos r2.str in
    let e1 : ParseResult Expr = parseExprMain r3.pos 0 r3.str in
    let r4 : StrPos = matchKeyword "in" e1.pos e1.str in
    let e2 : ParseResult Expr = parseExprMain r4.pos 0 r4.str in
    {val = TmLet {ident = nameNoSym r2.val, tyAnnot = tyunknown_, tyBody = tyunknown_,
                  body = e1.val, inexpr = e2.val, ty = tyunknown_,
                  info = makeInfo p e2.pos},
     pos = e2.pos, str = e2.str}
end


-- General fragment for handling infix operations
lang ExprInfixParser = ExprParser
  syn Associativity =
  | LeftAssoc ()
  | RightAssoc ()

  sem parseInfix (p: Pos) (prec: Int) (exp: ParseResult Expr) =
  | str ->
    let r : StrPos = eatWSAC p str in
    match parseInfixImp r.pos r.str with Some op then
      let op : {val : Expr -> Expr -> Expr, pos : Pos, str : String,
                assoc : Associativity, prec : Int} = op in
      if geqi op.prec prec then
        let prec2 = match op.assoc with LeftAssoc ()
                    then addi op.prec 1
                    else op.prec in
        let exp2 : ParseResult Expr = parseExprMain op.pos prec2 op.str in
        let exp3 = {val = op.val exp.val exp2.val,
                    pos = exp2.pos, str = exp2.str} in
	      parseInfix exp3.pos prec exp3 exp3.str
      else exp
    else exp

  sem parseInfixImp (p: Pos) =
end


-- This parser should be used if juxtaposition is NOT used
lang ExprInfixParserClosed = ExprInfixParser
  sem parseInfixImp (p: Pos) =
  | _ -> None ()
end

-- This parser should be used for application using juxaposition
lang ExprInfixParserJuxtaposition = ExprInfixParser + AppAst + UnknownTypeAst
  sem parseInfixImp (p: Pos) =
  | str ->
    Some {
      val = lam x. lam y.
        TmApp {lhs = x, rhs = y, ty = tyunknown_, info = mergeInfo (infoTm x) (infoTm y)},
      pos = p, str = str, assoc = LeftAssoc (), prec = 50}
end


lang MExprParserBase = BoolParser + UIntParser + IfParser +
                       ParenthesesParser + MExprWSACParser +
                       UFloatParser +
		                   SeqParser +
		                   StringParser + CharParser +
		                   VarParser + FunParser + LetParser
end

lang MExprParser = MExprParserBase + ExprParserNoInfix
end

mexpr

use WhitespaceParser in
  utest eatWSAC (initPos "") "  foo"
    with {str = "foo", pos = (posVal "" 1 2)} in
  utest eatWSAC (initPos "") " \tfoo"
    with {str = "foo", pos = (posVal "" 1 3)} in
  utest eatWSAC (initPos "") " \n    bar "
    with {str = "bar ", pos = (posVal "" 2 4)} in
  ();

use MExprWSACParser in
  utest eatWSAC (initPos "") " --foo \n  bar "
    with {str = "bar ", pos = posVal "" 2 2} in
  utest eatWSAC (initPos "") " /- foo -/ bar"
    with {str = "bar", pos = posVal "" 1 11} in
  utest eatWSAC (initPos "") " /- foo\n x \n -/ \nbar "
    with {str = "bar ", pos = posVal "" 4 0} in
  utest eatWSAC (initPos "") " /- x -- y /- foo \n -/ -/ !"
    with {str = "!", pos = posVal "" 2 7} in
  ();




use MExprEq in
use MExprParser in

-- Definition of equality functions, with explicit type annotations.
let eqPos = lam l : Pos. lam r : Pos.
  and (eqString l.filename r.filename)
      (and (eqi l.row r.row) (eqi l.col r.col))
in
let eqExpr = lam l : Expr. lam r : Expr.
  eqExpr l r
in
let eqParseResult = lam l : ParseResult Expr. lam r : ParseResult Expr.
  and (eqExpr l.val r.val)
      (and (eqPos l.pos r.pos) (eqString l.str r.str))
in

-- Unsigned integer
utest parseExprMain (initPos "file") 0 "  123foo" with
      {val = TmConst {val = CInt {val = 123}, ty = tyunknown_,
                      info = infoVal "file" 1 2 1 5},
       pos = posVal "file" 1 5, str = "foo"} using eqParseResult in
-- Unsigned floats
utest parseExprMain (initPos "file") 0 "  1.0 " with
      {val = TmConst {val = CFloat {val = string2float "1.0"}, ty = tyunknown_,
                      info = infoVal "file" 1 2 1 5},
       pos = posVal "file" 1 5, str = " "} using eqParseResult in
utest parseExprMain (initPos "file") 0 " 1234.  " with
      {val = TmConst {val = CFloat {val = string2float "1234."}, ty = tyunknown_,
                      info = infoVal "file" 1 1 1 6},
       pos = posVal "file" 1 6, str = "  "} using eqParseResult in
utest parseExprMain (initPos "file") 0 " 13.37 " with
      {val = TmConst {val = CFloat {val = string2float "13.37"}, ty = tyunknown_,
                      info = infoVal "file" 1 1 1 6},
       pos = posVal "file" 1 6, str = " "} using eqParseResult in
utest parseExprMain (initPos "file") 0 "  1.0e-2" with
      {val = TmConst {val = CFloat {val = string2float "0.01"}, ty = tyunknown_,
                      info = infoVal "file" 1 2 1 8},
       pos = posVal "file" 1 8, str = ""} using eqParseResult in
utest parseExprMain (initPos "file") 0 " 2.5e+2  " with
      {val = TmConst {val = CFloat {val = string2float "250.0"}, ty = tyunknown_,
                      info = infoVal "file" 1 1 1 7},
       pos = posVal "file" 1 7, str = "  "} using eqParseResult in
utest parseExprMain (initPos "file") 0 "   2e3" with
      {val = TmConst {val = CFloat {val = string2float "2000.0"}, ty = tyunknown_,
                      info = infoVal "file" 1 3 1 6},
       pos = posVal "file" 1 6, str = ""} using eqParseResult in
utest parseExprMain (initPos "file") 0 "   2E3 " with
       {val = TmConst {val = CFloat {val = string2float "2000.0"}, ty = tyunknown_,
                       info = infoVal "file" 1 3 1 6},
       pos = posVal "file" 1 6, str = " "} using eqParseResult in
utest parseExprMain (initPos "file") 0 "   2.0e3" with
      {val = TmConst {val = CFloat {val = string2float "2000.0"}, ty = tyunknown_,
                      info = infoVal "file" 1 3 1 8},
       pos = posVal "file" 1 8, str = ""} using eqParseResult in
utest parseExprMain (initPos "file") 0 " 1.e2 " with
      {val = TmConst {val = CFloat {val = string2float "100.0"}, ty = tyunknown_,
                      info = infoVal "file" 1 1 1 5},
       pos = posVal "file" 1 5, str = " "} using eqParseResult in
utest parseExprMain (initPos "file") 0 " 2.e+1 " with
      {val = TmConst {val = CFloat {val = string2float "20.0"}, ty = tyunknown_,
                      info = infoVal "file" 1 1 1 6},
       pos = posVal "file" 1 6, str = " "} using eqParseResult in
utest parseExprMain (initPos "file") 0 " 3.e-4 " with
      {val = TmConst {val = CFloat {val = string2float "0.0003"}, ty = tyunknown_,
                      info = infoVal "file" 1 1 1 6},
       pos = posVal "file" 1 6, str = " "} using eqParseResult in
utest parseExprMain (initPos "file") 0 "  2.E3 " with
      {val = TmConst {val = CFloat {val = string2float "2000.0"}, ty = tyunknown_,
                      info = infoVal "file" 1 2 1 6},
       pos = posVal "file" 1 6, str = " "} using eqParseResult in
utest parseExprMain (initPos "file") 0 " 4.E+1 " with
      {val = TmConst {val = CFloat {val = string2float "40.0"}, ty = tyunknown_,
                      info = infoVal "file" 1 1 1 6},
       pos = posVal "file" 1 6, str = " "} using eqParseResult in
utest parseExprMain (initPos "file") 0 " 1.E-3 " with
      {val = TmConst {val = CFloat {val = string2float "0.001"}, ty = tyunknown_,
                      info = infoVal "file" 1 1 1 6},
       pos = posVal "file" 1 6, str = " "} using eqParseResult in
utest parseExprMain (initPos "file") 0 " 1E " with
      {val = TmConst {val = CInt {val = 1}, ty = tyunknown_,
                      info = infoVal "file" 1 1 1 2},
       pos = posVal "file" 1 2, str = "E "} using eqParseResult in
utest parseExprMain (initPos "file") 0 " 1e " with
       {val = TmConst {val = CInt {val = 1}, ty = tyunknown_,
                       info = infoVal "file" 1 1 1 2},
       pos = posVal "file" 1 2, str = "e "} using eqParseResult in
utest parseExprMain (initPos "file") 0 " 1.e++2 " with
       {val = TmConst {val = CFloat {val = string2float "1.0"}, ty = tyunknown_,
                       info = infoVal "file" 1 1 1 3},
       pos = posVal "file" 1 3, str = "e++2 "} using eqParseResult in
utest parseExprMain (initPos "file") 0 " 3.1992e--2 " with
       {val = TmConst {val = CFloat {val = string2float "3.1992"}, ty = tyunknown_,
                       info = infoVal "file" 1 1 1 7},
       pos = posVal "file" 1 7, str = "e--2 "} using eqParseResult in

--If expression
let ifexpr : ParseResult Expr = parseExprMain (initPos "") 0 "  if 1 then 22 else 3" in
utest ifexpr.pos
  with posVal "" 1 21 in
-- Boolean literal 'true'
utest parseExpr (initPos "f") " true " with
      TmConst {val = CBool {val = true}, ty = tyunknown_,
               info = infoVal "f" 1 1 1 5} using eqExpr in
-- Boolean literal 'false'
utest parseExpr (initPos "f") " true " with
      TmConst {val = CBool {val = true}, ty = tyunknown_,
               info = infoVal "f" 1 1 1 5} using eqExpr in
-- Parentheses
utest parseExpr (initPos "") " ( 123) " with
      TmConst {val = CInt {val = 123}, ty = tyunknown_,
               info = infoVal "" 1 3 1 6} using eqExpr in
-- Sequences
utest parseExpr (initPos "") "[]" with
      TmSeq {tms = [], ty = tyunknown_, info = infoVal "" 1 0 1 2}
      using eqExpr in
utest parseExpr (initPos "") " [ ] " with
      TmSeq {tms = [], ty = tyunknown_, info = infoVal "" 1 1 1 4}
      using eqExpr in
utest parseExprMain (initPos "") 0 " [ 17 ] " with
      let v = TmConst {val = CInt {val = 17}, ty = tyunknown_,
                       info = infoVal "" 1 3 1 5} in
      {val = TmSeq {tms = [v], ty = tyunknown_, info = infoVal "" 1 1 1 7},
       pos = posVal "" 1 7, str = " "} using eqParseResult in
utest parseExpr (initPos "") " [ 232 , ( 19 ) ] " with
      let v1 = TmConst {val = CInt {val = 232}, ty = tyunknown_,
                        info = infoVal "" 1 3 1 6} in
      let v2 = TmConst {val = CInt {val = 19}, ty = tyunknown_,
                        info = infoVal "" 1 11 1 13} in
      TmSeq {tms = [v1,v2], ty = tyunknown_, info = infoVal "" 1 1 1 17}
      using eqExpr in
-- Strings
let makeChar = lam k. lam c. lam n.
    TmConst {val = CChar {val = c}, ty = tyunknown_,
             info = infoVal "" 1 n 1 (addi n k)} in
let mkc = makeChar 1 in
let mkc2 = makeChar 2 in
utest parseExpr (initPos "") " \"Foo\" " with
  let str = [mkc 'F' 2, mkc 'o' 3, mkc 'o' 4] in
  TmSeq {tms = str, ty = tyunknown_, info = infoVal "" 1 1 1 6} using eqExpr in
utest parseExpr (initPos "") " \" a\\\\ \\n\" " with
  let str = [mkc ' ' 2, mkc 'a' 3, mkc2 '\\' 4, mkc ' ' 6, mkc2 '\n' 7] in
  TmSeq {tms = str, ty = tyunknown_, info = infoVal "" 1 1 1 10} using eqExpr in
-- Chars
utest parseExprMain (initPos "") 0 " \'A\' " with
  {val = TmConst {val = CChar {val = 'A'}, ty = tyunknown_,
                  info = infoVal "" 1 1 1 4},
   pos = posVal "" 1 4, str = " "} using eqParseResult in
utest parseExpr (initPos "") " \'\\n\' " with
  TmConst {val = CChar {val = '\n'}, ty = tyunknown_,
           info = infoVal "" 1 1 1 5} using eqExpr in
-- Var
let var : ParseResult Expr = parseExprMain (initPos "") 0 " _xs " in
utest var.pos with posVal "" 1 4 in
let var : ParseResult Expr = parseExprMain (initPos "") 0 " fOO_12a " in
utest var.pos with posVal "" 1 8 in
-- Lambda
let lambda : ParseResult Expr = parseExprMain (initPos "") 0 " lam x . x " in
utest lambda.pos with posVal "" 1 10 in
-- Let
let letexpr : ParseResult Expr = parseExprMain (initPos "") 0 "  let x = 5 in 8 " in
utest letexpr.pos with posVal "" 1 16 in


()
