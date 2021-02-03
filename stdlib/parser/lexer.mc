-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "string.mc"
include "seq.mc"
include "mexpr/ast.mc"
include "mexpr/info.mc"


let tabSpace = 2

-- Base language for whitespace and comments (WSAC) parsing
lang WSACParser
  sem eatWSAC (p : Pos) =
end

-- Base language for parsing tokens preceeded by WSAC
lang TokenParser = WSACParser
  syn Token =
  sem nextToken /- : {pos : Pos, str : String} -> {token : Token, stream : {pos : Pos, str : String}} -/ =
  | stream -> match eatWSAC stream.pos stream.str with {str = str, pos = pos} then
      parseToken pos str
    else never

  sem parseToken (pos : Pos) /- : {String -> {token : Token, stream : {pos : Pos, str : String}}} -/ =
end

-- Eats whitespace
lang WhitespaceParser = WSACParser
  sem eatWSAC (p : Pos)  =
  | " " ++ xs -> eatWSAC (advanceCol p 1)  xs
  | "\t" ++ xs -> eatWSAC (advanceCol p tabSpace) xs
  | "\n" ++ xs -> eatWSAC (advanceRow p 1) xs
  | "\r" ++ xs -> eatWSAC p xs
  | x -> {str = x, pos = p}
end

let _ = use WhitespaceParser in
  utest eatWSAC (initPos "") "  foo"
    with {str = "foo", pos = (posVal "" 1 2)} in
  utest eatWSAC (initPos "") " \tfoo"
    with {str = "foo", pos = (posVal "" 1 3)} in
  utest eatWSAC (initPos "") " \n    bar "
    with {str = "bar ", pos = (posVal "" 2 4)} in
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

-- Eat multiline comment of the form /-  -/
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


-- TODO(vipa, 2021-02-03): move tests to new fragment
-- Commbined WSAC parser for MExpr
lang MExprWSACParser = WhitespaceParser + LineCommentParser + MultilineCommentParser

let _ = use MExprWSACParser in
  utest eatWSAC (initPos "") " --foo \n  bar "
    with {str = "bar ", pos = posVal "" 2 2} in
  utest eatWSAC (initPos "") " /- foo -/ bar"
    with {str = "bar", pos = posVal "" 1 11} in
  utest eatWSAC (initPos "") " /- foo\n x \n -/ \nbar "
    with {str = "bar ", pos = posVal "" 4 0} in
  utest eatWSAC (initPos "") " /- x -- y /- foo \n -/ -/ !"
    with {str = "!", pos = posVal "" 2 7} in
  ()

lang EOFTokenParser = TokenParser
  syn Token =
  | EOFTok {pos : Pos}

  sem parseToken (pos : Pos) =
  | [] -> {token = EOFTok {pos = pos}, stream = {pos = pos, str = []}}
end

-- Parses the continuation of an identifier, i.e., upper and lower
-- case letters, digits, and underscore.
let parseIdentCont : Pos -> String -> {val : String, pos : Pos, str : String} = lam p. lam str.
  recursive
  let work = lam acc. lam p. lam str.
    match str with [x] ++ xs then
      if (or (isAlphanum x) (eqChar '_' x))
      then work (snoc acc x) (advanceCol p 1) xs
      else {val = acc, pos = p, str = str}
    else {val = acc, pos = p, str = str}
  in work "" p str

utest parseIdentCont (initPos "") "+"
with {val = "", str = "+", pos = posVal "" 1 0}
utest parseIdentCont (initPos "") "a "
with {val = "a", str = " ", pos = posVal "" 1 1}
utest parseIdentCont (initPos "") "ba"
with {val = "ba", str = "", pos = posVal "" 1 2}
utest parseIdentCont (initPos "") "_asd "
with {val = "_asd", str = " ", pos = posVal "" 1 4}
utest parseIdentCont (initPos "") "Asd12 "
with {val = "Asd12", str = " ", pos = posVal "" 1 5}

lang LIdentTokenParser = TokenParser
  syn Token =
  | LIdentTok {fi : Info, val : String}

  sem parseToken (pos : Pos) =
  | [('_' | 'a' | 'b' | 'c' | 'd' | 'e' | 'f' | 'g' | 'h' | 'i' | 'j' | 'k' |
      'l' | 'm' | 'n' | 'o' | 'p' | 'q' | 'r' | 's' | 't' | 'u' | 'v' | 'w' |
      'x' | 'y' | 'z' ) & c] ++ str ->
    match parseIdentCont (advanceCol pos 1) str with {val = val, pos = pos2, str = str}
    then { token = LIdentTok {fi = makeInfo pos pos2, val = cons c val}
         , stream = {pos = pos2, str = str}
         }
    else never
end

lang UIdentTokenParser = TokenParser
  syn Token =
  | UIdentTok {fi : Info, val : String}

  sem parseToken (pos : Pos) =
  | [('A' | 'B' | 'C' | 'D' | 'E' | 'F' | 'G' | 'H' | 'I' | 'J' | 'K' |
      'L' | 'M' | 'N' | 'O' | 'P' | 'Q' | 'R' | 'S' | 'T' | 'U' | 'V' | 'W' |
      'X' | 'Y' | 'Z' ) & c] ++ str ->
    match parseIdentCont pos str with {val = val, pos = pos2, str = str}
    then { token = UIdentTok {fi = makeInfo pos pos2, val = val}
         , stream = {pos = pos2, str = str}
         }
    else never
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
  with {val = "", pos = posVal "" 1 0, str = "Not a number"}

lang UIntTokenParser = TokenParser
  syn Token =
  | IntTok {fi : Info, val : Int}

  sem parseToken (pos : Pos) =
  | (['0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _) & str ->
    match parseUInt pos str with {val = val, pos = pos2, str = str}
    then parseIntCont val pos pos2 str
    else never

  sem parseIntCont (acc : String) (pos1 : Pos) (pos2 : Pos) =
  | str ->
    { token = IntTok {fi = makeInfo pos1 pos2, val = string2int acc}
    , stream = {pos = pos2, str = str}
    }
end

let parseFloatExponent : Pos -> String -> {val: String, pos: Pos, str: String} =
  lam p. lam str.
    match str with ['+' | '-'] ++ xs & s then
      let n = parseUInt (advanceCol p 1) xs in
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
  with {val = "", pos = posVal "" 1 0, str = "Not an exponent"}

lang UFloatTokenParser = UIntTokenParser
  syn Token =
  | FloatTok {fi : Info, val : Float}

  sem parseIntCont (acc : String) (pos1 : Pos) (pos2 : Pos) =
  | ['.'] ++ str ->
    parseFloatCont acc pos1 (advanceCol pos2 1) str
  | (['.', '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _) & str ->
    match parseFloatExponent (advanceCol pos2 1) (tail str)
    with {val = val, pos = pos3, str = str}
    then parseFloatCont (join [acc, ".", val]) pos1 pos3 str
    else never
  | ( [ 'e' | 'E'] ++ _
    & ( [_, '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _
      | [_, '+' | '-', '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _
      )
    ) & str -> parseFloatCont acc pos1 pos2 str

  sem parseFloatCont (acc : String) (pos1 : Pos) (pos2 : Pos) =
  | ( [ 'e' | 'E'] ++ _
    & ( [_, '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _
      | [_, '+' | '-', '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _
      )
    ) & str ->
    match parseFloatExponent (advanceCol pos2 1) (tail str) with {val = val, pos = pos2, str = str}
    then { token = FloatTok {fi = makeInfo pos1 pos2, val = string2float (join [acc, "e", val])}
         , stream = {pos = pos2, str = str}
         }
    else never
  | str ->
    { token = FloatTok {fi = makeInfo pos1 pos2, val = string2float acc}
    , stream = {pos = pos2, str = str}
    }
end

let parseOperatorCont : Pos -> String -> {val : String, stream : {pos : Pos, str : String}} = lam p. lam str.
  recursive
  let work = lam acc. lam p. lam str.
    match str with [('%' | '<' | '>' | '!' | '?' | '~' | ':' | '.' | '$' | '&' | '*' |
                     '+' | '-' | '/' | '=' | '@' | '^' | '|') & c] ++ xs then
      work (snoc acc c) (advanceCol p 1) xs
    else {val = acc, stream = {pos = p, str = str}}
  in work "" p str

utest parseOperatorCont (initPos "") "+"
with {val = "+", stream = {str = "", pos = posVal "" 1 1}}
utest parseOperatorCont (initPos "") "a "
with {val = "", stream = {str = "a ", pos = posVal "" 1 0}}
utest parseOperatorCont (initPos "") "#ba"
with {val = "", stream = {str = "#ba", pos = posVal "" 1 0}}
utest parseOperatorCont (initPos "") "+-44"
with {val = "+-", stream = {str = "44", pos = posVal "" 1 2}}
utest parseOperatorCont (initPos "") "<&> "
with {val = "<&>", stream = {str = " ", pos = posVal "" 1 3}}

lang OperatorTokenParser = TokenParser
  syn Token =
  | OperatorTok {fi : Info, val : String}

  sem parseToken (pos : Pos) =
  | [('%' | '<' | '>' | '!' | '?' | '~' | ':' | '.' | '$' | '&' | '*' |
      '+' | '-' | '/' | '=' | '@' | '^' | '|') & c] ++ str ->
    match parseOperatorCont (advanceCol pos 1) str with {val = val, stream = stream}
    then {token = OperatorTok {fi = makeInfo pos stream.pos, val = cons c val}, stream = stream}
    else never
end

lang BracketTokenParser = TokenParser
  syn Token =
  | LParenTok {fi : Info}
  | RParenTok {fi : Info}
  | LBracketTok {fi : Info}
  | RBracketTok {fi : Info}
  | LBraceTok {fi : Info}
  | RBraceTok {fi : Info}

  sem parseToken (pos : Pos) =
  | "(" ++ str ->
    let pos2 = advanceCol pos 1 in
    {token = LParenTok {fi = makeInfo pos pos2}, stream = {pos = pos2, str = str}}
  | ")" ++ str ->
    let pos2 = advanceCol pos 1 in
    {token = RParenTok {fi = makeInfo pos pos2}, stream = {pos = pos2, str = str}}
  | "[" ++ str ->
    let pos2 = advanceCol pos 1 in
    {token = LBracketTok {fi = makeInfo pos pos2}, stream = {pos = pos2, str = str}}
  | "]" ++ str ->
    let pos2 = advanceCol pos 1 in
    {token = RBracketTok {fi = makeInfo pos pos2}, stream = {pos = pos2, str = str}}
  | "{" ++ str ->
    let pos2 = advanceCol pos 1 in
    {token = LBraceTok {fi = makeInfo pos pos2}, stream = {pos = pos2, str = str}}
  | "}" ++ str ->
    let pos2 = advanceCol pos 1 in
    {token = RBraceTok {fi = makeInfo pos pos2}, stream = {pos = pos2, str = str}}
end

lang SemiTokenParser = TokenParser
  syn Token =
  | SemiTok {fi : Info}

  sem parseToken (pos : Pos) =
  | ";" ++ str ->
    let pos2 = advanceCol pos 1 in
    {token = SemiTok {fi = makeInfo pos pos2}, stream = {pos = pos2, str = str}}
end

lang CommaTokenParser = TokenParser
  syn Token =
  | CommaTok {fi : Info}

  sem parseToken (pos : Pos) =
  | "," ++ str ->
    let pos2 = advanceCol pos 1 in
    {token = CommaTok {fi = makeInfo pos pos2}, stream = {pos = pos2, str = str}}
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
    else match str with "\n" ++ xs then posErrorExit p "Unexpected newline."
    else match str with [x] ++ xs then ret x xs 1
    else posErrorExit p "Unexpected end of file."
    -- TODO (David, 2020-09-27): Shoud we allow newlines etc. inside strings
       -- ADDENDUM NOTE(vipa, 2021-02-03): presently not parsing newlines in strings, just to never report an incorrect position, which could happen before
    -- TODO (David, 2020-09-27): Add all other relevant escape characters

lang StringTokenParser = TokenParser
  syn Token =
  | StringTok {fi : Info, val : String}

  sem parseToken (pos : Pos) =
  | "\"" ++ str ->
    recursive let work = lam acc. lam p2. lam str.
      match str with "\"" ++ str then
        {val = acc, pos = advanceCol p2 1, str = str}
      else match matchChar p2 str with {val = charval, pos = p2, str = str} then
        work (snoc acc charval) p2 str
      else never
    in match work "" (advanceCol pos 1) str with {val = val, pos = pos2, str = str} then
      { token = StringTok {fi = makeInfo pos pos2, val = val}
      , stream = {pos = pos2, str = str}
      }
    else never
end

lang CharTokenParser = TokenParser
  syn Token =
  | CharTok {fi : Info, val : Char}

  sem parseToken (pos : Pos) =
  | "'" ++ str ->
    match matchChar (advanceCol pos 1) str with {val = val, pos = pos2, str = str} then
      match str with "'" ++ str then
        let pos2 = advanceCol pos2 1 in
        { token = CharTok {fi = makeInfo pos pos2, val = val}
        , stream = {pos = pos2, str = str}
        }
      else posErrorExit pos "Expected ' to close character literal."
    else never
end

lang HashStringTokenParser = TokenParser
  syn Token =
  | HashStringTok {fi : Info, hash : String, val : String}

  sem parseToken (pos : Pos) =
  | "#" ++ str ->
    match parseIdentCont (advanceCol pos 1) str with {val = hash, pos = pos2, str = str} then
      match str with "\"" ++ str then
        recursive let work = lam acc. lam p2. lam str.
          match str with "\"" ++ str then
            {val = acc, pos = advanceCol p2 1, str = str}
          else match matchChar p2 str with {val = charval, pos = p2, str = str} then
            work (snoc acc charval) p2 str
          else never
        in match work "" (advanceCol pos2 1) str with {val = val, pos = pos2, str = str} then
          { token = HashStringTok {fi = makeInfo pos pos2, hash = hash, val = val}
          , stream = {pos = pos2, str = str}
          }
        else never
      else posErrorExit pos2 "Expected \" to begin hash string"
    else never
end

lang Lexer
  = WhitespaceParser + LineCommentParser + MultilineCommentParser
  + EOFTokenParser + LIdentTokenParser + UIdentTokenParser
  + UIntTokenParser + UFloatTokenParser
  + OperatorTokenParser + BracketTokenParser + SemiTokenParser + CommaTokenParser
  + StringTokenParser + CharTokenParser
  + HashStringTokenParser

mexpr

use Lexer in

let start = initPos "file" in
let parse = lam str. nextToken {pos = start, str = str} in

utest parse " --foo \n  bar " with
  { token = LIdentTok {val = "bar", fi = infoVal "file" 2 2 2 5}
  , stream = {pos = posVal "file" 2 5 , str = " "}
  } in

utest parse " /- foo -/ bar" with
  { token = LIdentTok {val = "bar", fi = infoVal "file" 1 11 1 14}
  , stream = {pos = posVal "file" 1 14 , str = ""}
  } in

utest parse " /- foo\n x \n -/ \nbar " with
  { token = LIdentTok {val = "bar", fi = infoVal "file" 4 0 4 3}
  , stream = {pos = posVal "file" 4 3 , str = " "}
  } in

utest parse " /- x -- y /- foo \n -/ -/ !" with
  { token = OperatorTok {val = "!", fi = infoVal "file" 2 7 2 8}
  , stream = {pos = posVal "file" 2 8 , str = ""}
  } in

utest parse "  123foo" with
  { token = IntTok {val = 123, fi = infoVal "file" 1 2 1 5}
  , stream = {pos = posVal "file" 1 5 , str = "foo"}
  } in

utest parse "  1.0" with
  { token = FloatTok {val = 1.0, fi = infoVal "file" 1 2 1 5}
  , stream = {pos = posVal "file" 1 5 , str = ""}
  } in

utest parse " 1234.  " with
  { token = FloatTok {val = 1234.0, fi = infoVal "file" 1 1 1 6}
  , stream = {pos = posVal "file" 1 6 , str = "  "}
  } in

utest parse " 13.37 " with
  { token = FloatTok {val = 13.37, fi = infoVal "file" 1 1 1 6}
  , stream = {pos = posVal "file" 1 6, str = " "}
  } in

utest parse "  1.0e-2" with
  { token = FloatTok {val = 0.01, fi = infoVal "file" 1 2 1 8}
  , stream = {pos = posVal "file" 1 8, str = ""}
  } in

utest parse " 2.5e+2  " with
  { token = FloatTok {val = 250.0, fi = infoVal "file" 1 1 1 7}
  , stream = {pos = posVal "file" 1 7, str = "  "}
  } in

utest parse "   2e3" with
  { token = FloatTok {val = 2000.0, fi = infoVal "file" 1 3 1 6}
  , stream = {pos = posVal "file" 1 6, str = ""}
  } in

utest parse "   2E3" with
  { token = FloatTok {val = 2000.0, fi = infoVal "file" 1 3 1 6}
  , stream = {pos = posVal "file" 1 6, str = ""}
  } in

utest parse "   2.0E3" with
  { token = FloatTok {val = 2000.0, fi = infoVal "file" 1 3 1 8}
  , stream = {pos = posVal "file" 1 8, str = ""}
  } in

utest parse "   2.E3" with
  { token = FloatTok {val = 2000.0, fi = infoVal "file" 1 3 1 7}
  , stream = {pos = posVal "file" 1 7, str = ""}
  } in

utest parse " 1.e2 " with
  { token = FloatTok {val = 100.0, fi = infoVal "file" 1 1 1 5}
  , stream = {pos = posVal "file" 1 5, str = " "}
  } in

utest parse " 3.e-4 " with
  { token = FloatTok {val = 0.0003, fi = infoVal "file" 1 1 1 6}
  , stream = {pos = posVal "file" 1 6, str = " "}
  } in

utest parse " 4.E+1 " with
  { token = FloatTok {val = 40.0, fi = infoVal "file" 1 1 1 6}
  , stream = {pos = posVal "file" 1 6, str = " "}
  } in

utest parse " 1.E-3 " with
  { token = FloatTok {val = 0.001, fi = infoVal "file" 1 1 1 6}
  , stream = {pos = posVal "file" 1 6, str = " "}
  } in

utest parse " 1E " with
  { token = IntTok {val = 1, fi = infoVal "file" 1 1 1 2}
  , stream = {pos = posVal "file" 1 2, str = "E "}
  } in

utest parse " 1e " with
  { token = IntTok {val = 1, fi = infoVal "file" 1 1 1 2}
  , stream = {pos = posVal "file" 1 2, str = "e "}
  } in

utest parse " 1.e++2 " with
  { token = FloatTok {val = 1.0, fi = infoVal "file" 1 1 1 3}
  , stream = {pos = posVal "file" 1 3, str = "e++2 "}
  } in

utest parse " 3.1992e--2 " with
  { token = FloatTok {val = 3.1992, fi = infoVal "file" 1 1 1 7}
  , stream = {pos = posVal "file" 1 7, str = "e--2 "}
  } in

utest parse "  if 1 then 22 else 3" with
  { token = LIdentTok {val = "if", fi = infoVal "file" 1 2 1 4}
  , stream = {pos = posVal "file" 1 4, str = " 1 then 22 else 3"}
  } in

utest parse " true " with
  { token = LIdentTok {val = "true", fi = infoVal "file" 1 1 1 5}
  , stream = {pos = posVal "file" 1 5, str = " "}
  } in

utest parse " ( 123) " with
  { token = LParenTok {fi = infoVal "file" 1 1 1 2}
  , stream = {pos = posVal "file" 1 2, str = " 123) "}
  } in

utest parse "[]" with
  { token = LBracketTok {fi = infoVal "file" 1 0 1 1}
  , stream = {pos = posVal "file" 1 1, str = "]"}
  } in

utest parse " [ ] " with
  { token = LBracketTok {fi = infoVal "file" 1 1 1 2}
  , stream = {pos = posVal "file" 1 2, str = " ] "}
  } in

utest parse " [ 17 ] " with
  { token = LBracketTok {fi = infoVal "file" 1 1 1 2}
  , stream = {pos = posVal "file" 1 2, str = " 17 ] "}
  } in

utest parse " [ 232 , ( 19 ) ] " with
  { token = LBracketTok {fi = infoVal "file" 1 1 1 2}
  , stream = {pos = posVal "file" 1 2, str = " 232 , ( 19 ) ] "}
  } in

utest parse " \"Foo\" " with
  { token = StringTok {val = "Foo", fi = infoVal "file" 1 1 1 6}
  , stream = {pos = posVal "file" 1 6, str = " "}
  } in

utest parse " \" a\\\\ \\n\" " with
  { token = StringTok {val = " a\\ \n", fi = infoVal "file" 1 1 1 10}
  , stream = {pos = posVal "file" 1 10, str = " "}
  } in

utest parse " \'A\' " with
  { token = CharTok {val = 'A', fi = infoVal "file" 1 1 1 4}
  , stream = {pos = posVal "file" 1 4, str = " "}
  } in

utest parse " \'\\n\' " with
  { token = CharTok {val = '\n', fi = infoVal "file" 1 1 1 5}
  , stream = {pos = posVal "file" 1 5, str = " "}
  } in

utest parse " _xs " with
  { token = LIdentTok {val = "_xs", fi = infoVal "file" 1 1 1 4}
  , stream = {pos = posVal "file" 1 4, str = " "}
  } in

utest parse " fOO_12a " with
  { token = LIdentTok {val = "fOO_12a", fi = infoVal "file" 1 1 1 8}
  , stream = {pos = posVal "file" 1 8, str = " "}
  } in

utest parse " lam x . x " with
  { token = LIdentTok {val = "lam", fi = infoVal "file" 1 1 1 4}
  , stream = {pos = posVal "file" 1 4, str = " x . x "}
  } in

utest parse "  let x = 5 in 8 " with
  { token = LIdentTok {val = "let", fi = infoVal "file" 1 2 1 5}
  , stream = {pos = posVal "file" 1 5, str = " x = 5 in 8 "}
  } in

utest parse " += 47;" with
  { token = OperatorTok {val = "+=", fi = infoVal "file" 1 1 1 3}
  , stream = {pos = posVal "file" 1 3, str = " 47;"}
  } in

utest parse " ; println foo" with
  { token = SemiTok {fi = infoVal "file" 1 1 1 2}
  , stream = {pos = posVal "file" 1 2, str = " println foo"}
  } in

utest parse " #foo\"Zomething\"more" with
  { token = HashStringTok {hash = "foo", val = "Zomething", fi = infoVal "file" 1 1 1 16}
  , stream = {pos = posVal "file" 1 16, str = "more"}
  } in

utest parse " #\"Zomething\"more" with
  { token = HashStringTok {hash = "", val = "Zomething", fi = infoVal "file" 1 1 1 13}
  , stream = {pos = posVal "file" 1 13, str = "more"}
  } in

utest parse " #123\"Zomething\"more" with
  { token = HashStringTok {hash = "123", val = "Zomething", fi = infoVal "file" 1 1 1 16}
  , stream = {pos = posVal "file" 1 16, str = "more"}
  } in

()
