-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "string.mc"
include "seq.mc"
include "mexpr/ast.mc"
include "mexpr/info.mc"


let tabSpace = 2

-- Base language for whitespace and comments (WASC) parsing
lang WSACParser
  sem eatWSAC (p : Pos) =
end

-- Eats whitespace
lang WhitespaceParser = WSACParser
  sem eatWSAC (p : Pos)  =
  | " " ++ xs -> eatWSAC (advanceCol p 1)  xs
  | "\t" ++ xs -> eatWSAC (advanceCol p tabSpace) xs
  | "\n" ++ xs -> eatWSAC (advanceRow p 1) xs
  | x -> {str = x, pos = p}
end

let _ = use WhitespaceParser in
  utest eatWSAC (initPos "") "  foo" with {str = "foo", pos = (posVal "" 1 2)} in
  utest eatWSAC (initPos "") " \tfoo" with {str = "foo", pos = (posVal "" 1 3)} in
  utest eatWSAC (initPos "") " \n    bar " with {str = "bar ", pos = (posVal "" 2 4)} in
  ()

-- Eat line comments of the form --
lang LineCommentParser = WSACParser
  sem eatWSAC (p : Pos)  =
  | "--" ++ xs ->
    recursive
    let remove = lam p. lam str.
      match str with "\n" ++ xs then eatWSAC (advanceRow p 1) xs else
      match str with [x] ++ xs then remove (advanceCol p 1) xs else
      eatWSAC p str
    in remove p xs
end

-- Eat multiline comment of the form *-  -*
lang MultilineCommentParser = WSACParser
  sem eatWSAC (p : Pos) =
  | "/-" ++ xs ->
    recursive
    let remove = lam p. lam str. lam d.
      match str with "/-" ++ xs then remove (advanceCol p 2) xs (addi d 1) else
      match str with "\n" ++ xs then remove (advanceRow p 1) xs d else
      match str with "-/" ++ xs then
        if eqi d 1 then eatWSAC (advanceCol p 2) xs
        else remove (advanceCol p 2) xs (subi d 1) else
      match str with [_] ++ xs then remove (advanceCol p 1) xs d else
      if eqi d 0 then eatWSAC p str else posErrorExit p "Unmatched multiline comments."
    in remove (advanceCol p 2) xs 1
end

-- Commbined WSAC parser for MExpr
lang MExprWSACParser = WhitespaceParser + LineCommentParser + MultilineCommentParser

let _ = use MExprWSACParser in
  utest eatWSAC (initPos "") " --foo \n  bar " with {str = "bar ", pos = posVal "" 2 2} in
  utest eatWSAC (initPos "") " /- foo -/ bar" with {str = "bar", pos = posVal "" 1 11} in
  utest eatWSAC (initPos "") " /- foo\n x \n -/ \nbar " with {str = "bar ", pos = posVal "" 4 0} in
  utest eatWSAC (initPos "") " /- x -- y /- foo \n -/ -/ !" with {str = "!", pos = posVal "" 2 7} in
  ()



-- Top of the expression parser. Connects WSAC with parsing of other non terminals
lang ExprParser = WSACParser
  sem parseExpr (p: Pos) (prec: Int) =
  | s ->
    let r1 = eatWSAC p s in
    let exp = parseExprImp r1.pos r1.str in
    let r2 = eatWSAC exp.pos exp.str in
    parseInfix r2.pos prec exp r2.str 

  sem parseInfix (p: Pos) (prec: Int) (exp: Expr) =

  sem parseExprImp (p: Pos) =
  | _ -> posErrorExit p "Parse error. Unknown character sequence."
end


-- Include this fragment is there are no infix operations
lang ExprParserNoInfix = ExprParser
  sem parseInfix (p: Pos) (prec: Int) (exp: Expr) =
  | _ -> exp
end

-- Parsing of boolean literals
lang BoolParser = ExprParser + ConstAst + BoolAst
  sem parseExprImp (p: Pos) =
  | "true" ++ xs ->
      let p2 = advanceCol p 4 in
      {val = TmConst {val = CBool {val = true}, fi = makeInfo p p2}, pos = p2, str = xs}
  | "false" ++ xs ->
      let p2 = advanceCol p 5 in
      {val = TmConst {val = CBool {val = false}, fi = makeInfo p p2}, pos = p2, str = xs}
end


-- Parsing of an unsigned integer
lang UIntParser = ExprParser + ConstAst + IntAst
  sem parseExprImp (p : Pos) =
  | ("0" ++ s) & xs | ("1" ++ s) & xs | ("2" ++ s) & xs | ("3" ++ s) & xs | ("4" ++ s) & xs |
    ("5" ++ s) & xs | ("6" ++ s) & xs | ("7" ++ s) & xs | ("8" ++ s) & xs | ("9" ++ s) & xs ->
    recursive
    let work = lam p2. lam str. lam num.
      match str with [x] ++ xs then
        let c = char2int x in
        if and (geqi c 48) (leqi c 57)
        then work (advanceCol p2 1) xs (snoc num x)
        else {val = TmConst {val = CInt {val = string2int num}, fi = makeInfo p p2}, pos = p2, str = str}
      else {val = TmConst {val = CInt {val = string2int num}, fi = makeInfo p p2}, pos = p2, str = str}
    in work (advanceCol p 1) s ([head xs])
end


-- Fragment for simple parsing of keyword
lang KeywordParser = WSACParser
  sem matchKeyword (keyword: String) (p: Pos) =
  | s ->
     let r = eatWSAC p s in
     if isPrefix eqc keyword r.str then
       let l = length keyword in
       {pos = advanceCol r.pos l, str = slice r.str l (subi (length r.str) l)}
     else
       posErrorExit r.pos (join ["Unknown character. Expected '", keyword, "'."])
end


-- Parsing if expressions
lang IfParser = ExprParser + KeywordParser +  MatchAst + BoolPat
  sem parseExprImp (p: Pos) =
  | "if" ++ xs ->
     let e1 = parseExpr (advanceCol p 2) 0 xs in
     let r1 = matchKeyword "then" e1.pos e1.str  in
     let e2 = parseExpr r1.pos 0 r1.str in
     let r2 = matchKeyword "else" e2.pos e2.str  in
     let e3 = parseExpr r2.pos 0 r2.str in
     {val = TmMatch {target = e1.val, pat = PBool {val = true, fi = NoInfo ()},
                     thn = e2.val, els = e3.val, fi = makeInfo p e3.pos},
      pos = e3.pos,
      str = e3.str}
 end

-- Integer arithmetic parser (intrinsics)
lang ArithIntParser = ExprParser + ConstAst + ArithIntAst
  sem parseExprImp (p: Pos) =
  | "addi" ++ xs -> let p2 = advanceCol p 4 in
      {val = TmConst {val = CAddi {}, fi = makeInfo p p2}, pos = p2, str = xs}
  | "subi" ++ xs -> let p2 = advanceCol p 4 in
      {val = TmConst {val = CSubi {}, fi = makeInfo p p2}, pos = p2, str = xs}
  | "muli" ++ xs -> let p2 = advanceCol p 4 in
      {val = TmConst {val = CMuli {}, fi = makeInfo p p2}, pos = p2, str = xs}
end


-- Parse parentheses
lang ParenthesesParser = ExprParser + KeywordParser
  sem parseExprImp (p: Pos) =
  | "(" ++ xs ->
    let e = parseExpr (advanceCol p 1) 0 xs in
    let r = matchKeyword ")" e.pos e.str in
    {val = e.val, pos = r.pos, str = r.str}
end

-- Parses a sequence of 
lang SeqParser = ExprParser + KeywordParser + SeqAst
  sem parseExprImp (p: Pos) =
  | "[" ++ xs -> 
      recursive let work = lam acc. lam first. lam p2. lam str.
        let r = eatWSAC p2 str in
  	match r.str with "]" ++ xs then
	  {val = TmSeq{tms = acc, fi = makeInfo p (advanceCol r.pos 1)},
	   pos = advanceCol r.pos 1, str = xs}
	else
	  let r2 = if first then r else matchKeyword "," r.pos r.str in
	  let e = parseExpr r2.pos 0 r2.str in
	  work (snoc acc e.val) false e.pos e.str  
      in work [] true (advanceCol p 1) xs
end

-- Sequence operations (intrinsics)
lang SeqOpParser = ExprParser + ConstAst + SeqOpAst
  sem parseExprImp (p: Pos) =
  | "concat" ++ xs -> let p2 = advanceCol p 6 in
      {val = TmConst {val = CConcat {}, fi = makeInfo p p2}, pos = p2, str = xs}
end

-- Matches a character (including escape character). 
let matchChar : Pos -> String -> {val: Char, pos: Pos, str: String} =
  lam p. lam str.
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
    -- TODO David (2020-09-27): Shoud we allow newlines etc. inside strings
    -- TODO David (2020-09-27): Add all other relevant escape characters

-- Parses strings, including escape characters
lang StringParser = ExprParser + SeqAst + CharAst
  sem parseExprImp (p: Pos) =
  | "\"" ++ xs ->
    recursive let work = lam acc. lam p2. lam str.
      match str with "\"" ++ xs then
        {val = TmSeq {tms = acc, fi = makeInfo p (advanceCol p2 1)},
	 pos = advanceCol p2 1, str = xs}
      else	  
        let r =  matchChar p2 str in
        let v = TmConst {val = CChar {val = r.val}, fi = makeInfo p2 r.pos} in
	work (snoc acc v) r.pos r.str
    in
      work [] (advanceCol p 1) xs
end

-- General fragment for handling infix operations
lang ExprInfixParser = ExprParser
  syn Associativity = 
  | LeftAssoc ()
  | RightAssoc ()

  sem parseInfix (p: Pos) (prec: Int) (exp: Expr) =
  | str ->
    let r = eatWSAC p str in
    match parseInfixImp r.pos r.str with Some op then
      if geqi op.prec prec then
        let prec2 = match op.assoc with LeftAssoc () then addi op.prec 1 else op.prec in
        let exp2 = parseExpr op.pos prec2 op.str in 
        let exp3 = {val = op.val exp.val exp2.val, pos = exp2.pos, str = exp2.str} in
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



lang MExprParserBase = BoolParser + UIntParser + IfParser + ArithIntParser +
                       ParenthesesParser + MExprWSACParser +
		       SeqParser + SeqOpParser +
		       StringParser

lang MExprParser = MExprParserBase + ExprParserNoInfix




mexpr



use MExprParser in
-- Unsigned integer
utest parseExpr (initPos "file") 0 "  123foo" with
      {val = TmConst {val = CInt {val = 123}, fi = infoVal "file" 1 2 1 5}, pos = posVal "file" 1 5, str = "foo"} in
-- If expression
utest (parseExpr (initPos "") 0 "  if 1 then 22 else 3").pos with posVal "" 1 21 in
-- Boolean literal 'true'
utest parseExpr (initPos "f") 0 " true " with
      {val = TmConst {val = CBool {val = true}, fi = infoVal "f" 1 1 1 5}, pos = posVal "f" 1 5, str = " "} in
-- Boolean literal 'false'
utest parseExpr (initPos "f") 0 " true " with
      {val = TmConst {val = CBool {val = true}, fi = infoVal "f" 1 1 1 5}, pos = posVal "f" 1 5, str = " "} in
-- Instrinsics integer arithmetic
utest parseExpr (initPos "") 0 "  addi " with
      {val = TmConst {val = CAddi {}, fi = infoVal "" 1 2 1 6}, pos = posVal "" 1 6, str = " "} in
utest parseExpr (initPos "") 0 "  subi " with
      {val = TmConst {val = CSubi {}, fi = infoVal "" 1 2 1 6}, pos = posVal "" 1 6, str = " "} in
utest parseExpr (initPos "") 0 "  muli " with
      {val = TmConst {val = CMuli {}, fi = infoVal "" 1 2 1 6}, pos = posVal "" 1 6, str = " "} in
-- Parentheses
utest parseExpr (initPos "") 0 " ( muli) " with
      {val = TmConst {val = CMuli {}, fi = infoVal "" 1 3 1 7}, pos = posVal "" 1 8, str = " "} in
-- Sequences
utest parseExpr (initPos "") 0 "[]" with
      {val = TmSeq {tms = [], fi = infoVal "" 1 0 1 2}, pos = posVal "" 1 2, str = ""} in
utest parseExpr (initPos "") 0 " [ ] " with
      {val = TmSeq {tms = [], fi = infoVal "" 1 1 1 4}, pos = posVal "" 1 4, str = " "} in
utest parseExpr (initPos "") 0 " [ 17 ] " with
      let v = TmConst {val = CInt {val = 17}, fi = infoVal "" 1 3 1 5} in
      {val = TmSeq {tms = [v], fi = infoVal "" 1 1 1 7}, pos = posVal "" 1 7, str = " "} in
utest parseExpr (initPos "") 0 " [ 232 , ( 19 ) ] " with
      let v1 = TmConst {val = CInt {val = 232}, fi = infoVal "" 1 3 1 6} in
      let v2 = TmConst {val = CInt {val = 19}, fi = infoVal "" 1 11 1 13} in
      {val = TmSeq {tms = [v1,v2], fi = infoVal "" 1 1 1 17}, pos = posVal "" 1 17, str = " "} in
-- Strings
let makeChar = lam k. lam c. lam n.
    TmConst {val = CChar {val = c}, fi = infoVal "" 1 n 1 (addi n k)} in
let mkc = makeChar 1 in
let mkc2 = makeChar 2 in
utest parseExpr (initPos "") 0 " \"Foo\" " with
  let str = [mkc 'F' 2, mkc 'o' 3, mkc 'o' 4] in
  {val = TmSeq {tms = str, fi = infoVal "" 1 1 1 6}, pos = posVal "" 1 6, str = " "} in
utest parseExpr (initPos "") 0 " \" a\\\\ \\n\" " with
  let str = [mkc ' ' 2, mkc 'a' 3, mkc2 '\\' 4, mkc ' ' 6, mkc2 '\n' 7] in
  {val = TmSeq {tms = str, fi = infoVal "" 1 1 1 10}, pos = posVal "" 1 10, str = " "} in

()
