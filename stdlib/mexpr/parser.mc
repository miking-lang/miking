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
  sem parseExpr (p : Pos) =
  | s ->
    let r = eatWSAC p s in parseExprImp r.pos r.str

  sem parseExprImp (p: Pos) =
  | _ -> posErrorExit p "Parse error. Unknown character sequence."
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
       posErrorExit r.pos (join ["Unknown character. Expected keyword '", keyword, "'."])
end


-- Parsing if expressions
lang IfParser = ExprParser + KeywordParser +  MatchAst + BoolPat
  sem parseExprImp (p: Pos) =
  | "if" ++ xs ->
     let e1 = parseExpr (advanceCol p 2) xs in
     let r1 = matchKeyword "then" e1.pos e1.str  in
     let e2 = parseExpr r1.pos r1.str in
     let r2 = matchKeyword "else" e2.pos e2.str  in
     let e3 = parseExpr r2.pos r2.str in
     {val = TmMatch {target = e1.val, pat = PBool {val = true, fi = NoInfo ()},
                     thn = e2.val, els = e3.val, fi = makeInfo p e3.pos},
      pos = e3.pos,
      str = e3.str}
 end

-- Integer arithmetic parser (intrinsics)
lang ArithIntParser = ExprParser + ArithIntAst
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
    let e = parseExpr (advanceCol p 1) xs in
    let r = matchKeyword ")" e.pos e.str in
    {val = e.val, pos = r.pos, str = r.str}
end



lang MExprParser = BoolParser + UIntParser + IfParser + ArithIntParser +
                   ParenthesesParser + MExprWSACParser


-- Expr  -> Term Expr'             Function: parseExpr openExpr
--                                 1. eatWSAC, 2. parseFirst on Term (success of fail) -> new nextTerm
--                                 3. eatWSAC 4. check end of expr, return
--                                 4. if not, parseSecond(openExpr, nextTerm)

-- Expr' -> "+" Term Expr'         Function: parseSecond openExpr nextTerm
--        | "-" Term Expr'         1. parse "op" etc. if relevant
--                                 2. if "op" higher prec than last or equal and right assoc then
--                                      call parseExpr with (lam rhs. openExpr(nextTerm "+" rhs) )
--                                    else "op" lower prec than last or equal and left assoc then
--                                      return
--        | Term Expr'             2. call parseExpr with flag "only_first"
--        | empty
--
-- Term  -> Atom Term'
-- Term' -> "*" Atom Term'
--        | "/" Atom Term'
--        | empty
--
-- Atom  -> Num
--        | "(" Expr ")"


mexpr

use MExprParser in
-- Unsigned integer
utest parseExpr (initPos "file") "  123foo" with
      {val = TmConst {val = CInt {val = 123}, fi = infoVal "file" 1 2 1 5}, pos = posVal "file" 1 5, str = "foo"} in
-- If expression
utest (parseExpr (initPos "") "  if 1 then 22 else 3").pos with posVal "" 1 21 in
-- Boolean literal 'true'
utest parseExpr (initPos "f") " true " with
      {val = TmConst {val = CBool {val = true}, fi = infoVal "f" 1 1 1 5}, pos = posVal "f" 1 5, str = " "} in
-- Boolean literal 'false'
utest parseExpr (initPos "f") " true " with
      {val = TmConst {val = CBool {val = true}, fi = infoVal "f" 1 1 1 5}, pos = posVal "f" 1 5, str = " "} in
-- Instrinsics integer arithmetic
utest parseExpr (initPos "") "  addi " with
      {val = TmConst {val = CAddi {}, fi = infoVal "" 1 2 1 6}, pos = posVal "" 1 6, str = " "} in
utest parseExpr (initPos "") "  subi " with
      {val = TmConst {val = CSubi {}, fi = infoVal "" 1 2 1 6}, pos = posVal "" 1 6, str = " "} in
utest parseExpr (initPos "") "  muli " with
      {val = TmConst {val = CMuli {}, fi = infoVal "" 1 2 1 6}, pos = posVal "" 1 6, str = " "} in
-- Parentheses
utest parseExpr (initPos "") " ( muli) " with
      {val = TmConst {val = CMuli {}, fi = infoVal "" 1 3 1 7}, pos = posVal "" 1 8, str = " "} in

()
