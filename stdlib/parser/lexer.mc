-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "string.mc"
include "seq.mc"
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

  sem parseToken (pos : Pos) /- : String -> {token : Token, lit : String, info : Info, stream : {pos : Pos, str : String}} -/ =
  sem tokKindEq (tok : Token) /- : Token -> Bool -/ =
  sem tokInfo /- : Token -> Info -/ =
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

-- Commbined WSAC parser for MExpr
lang MExprWSACParser = WhitespaceParser + LineCommentParser + MultilineCommentParser

lang EOFTokenParser = TokenParser
  syn Token =
  | EOFTok {info : Info}

  sem parseToken (pos : Pos) =
  | [] ->
    let info = makeInfo pos pos in
    {token = EOFTok {info = info}, lit = "", info = info, stream = {pos = pos, str = []}}

  sem tokKindEq (tok : Tok) =
  | EOFTok _ -> match tok with EOFTok _ then true else false

  sem tokInfo =
  | EOFTok {info = info} -> info
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
  | LIdentTok {info : Info, val : String}

  sem parseToken (pos : Pos) =
  | [('_' | 'a' | 'b' | 'c' | 'd' | 'e' | 'f' | 'g' | 'h' | 'i' | 'j' | 'k' |
      'l' | 'm' | 'n' | 'o' | 'p' | 'q' | 'r' | 's' | 't' | 'u' | 'v' | 'w' |
      'x' | 'y' | 'z' ) & c] ++ str ->
    match parseIdentCont (advanceCol pos 1) str with {val = val, pos = pos2, str = str}
    then
      let val = cons c val in
      let info = makeInfo pos pos2 in
      { token = LIdentTok {info = info, val = val}
      , lit = val
      , info = info
      , stream = {pos = pos2, str = str}
      }
    else never

  sem tokKindEq (tok : Tok) =
  | LIdentTok _ -> match tok with LIdentTok _ then true else false

  sem tokInfo =
  | LIdentTok {info = info} -> info
end

lang UIdentTokenParser = TokenParser
  syn Token =
  | UIdentTok {info : Info, val : String}

  sem parseToken (pos : Pos) =
  | [('A' | 'B' | 'C' | 'D' | 'E' | 'F' | 'G' | 'H' | 'I' | 'J' | 'K' |
      'L' | 'M' | 'N' | 'O' | 'P' | 'Q' | 'R' | 'S' | 'T' | 'U' | 'V' | 'W' |
      'X' | 'Y' | 'Z' ) & c] ++ str ->
    match parseIdentCont (advanceCol pos 1) str with {val = val, pos = pos2, str = str}
    then
      let val = cons c val in
      let info = makeInfo pos pos2 in
      { token = UIdentTok {info = info, val = val}
      , lit = val
      , info = info
      , stream = {pos = pos2, str = str}
      }
    else never

  sem tokKindEq (tok : Tok) =
  | UIdentTok _ -> match tok with UIdentTok _ then true else false

  sem tokInfo =
  | UIdentTok {info = info} -> info
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
  | IntTok {info : Info, val : Int}

  sem parseToken (pos : Pos) =
  | (['0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _) & str ->
    match parseUInt pos str with {val = val, pos = pos2, str = str}
    then parseIntCont val pos pos2 str
    else never

  sem parseIntCont (acc : String) (pos1 : Pos) (pos2 : Pos) =
  | str ->
    let info = makeInfo pos1 pos2 in
    { token = IntTok {info = info, val = string2int acc}
    , lit = ""
    , info = info
    , stream = {pos = pos2, str = str}
    }

  sem tokKindEq (tok : Tok) =
  | IntTok _ -> match tok with IntTok _ then true else false

  sem tokInfo =
  | IntTok {info = info} -> info
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
  | FloatTok {info : Info, val : Float}

  sem parseIntCont (acc : String) (pos1 : Pos) (pos2 : Pos) =
  | ['.'] ++ str ->
    parseFloatCont acc pos1 (advanceCol pos2 1) str
  | (['.', '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _) & str ->
    match parseFloatExponent (advanceCol pos2 1) (tail str)
    with {val = val, pos = pos3, str = str}
    then
      let acc = join [acc, ".", val] in
      parseFloatCont acc pos1 pos3 str
    else never
  | ( [ 'e' | 'E'] ++ _
    & ( [_, '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _
      | [_, '+' | '-', '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _
      )
    ) & str -> parseFloatCont acc pos1 pos2 str

  sem parseFloatCont (acc : String) (pos1 : Pos) (pos2 : Pos) =
  | ( [ ('e' | 'E') & e] ++ _
    & ( [_, '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _
      | [_, '+' | '-', '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _
      )
    ) & str ->
    match parseFloatExponent (advanceCol pos2 1) (tail str) with {val = val, pos = pos2, str = str}
    then
      let info = makeInfo pos1 pos2 in
      { token = FloatTok {info = info, val = string2float (join [acc, "e", val])}
      , lit = ""
      , info = info
      , stream = {pos = pos2, str = str}
      }
    else never
  | str ->
    let info = makeInfo pos1 pos2 in
    { token = FloatTok {info = info, val = string2float acc}
    , lit = ""
    , info = info
    , stream = {pos = pos2, str = str}
    }

  sem tokKindEq (tok : Tok) =
  | FloatTok _ -> match tok with FloatTok _ then true else false

  sem tokInfo =
  | FloatTok {info = info} -> info
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
  | OperatorTok {info : Info, val : String}

  sem parseToken (pos : Pos) =
  | [('%' | '<' | '>' | '!' | '?' | '~' | ':' | '.' | '$' | '&' | '*' |
      '+' | '-' | '/' | '=' | '@' | '^' | '|') & c] ++ str ->
    match parseOperatorCont (advanceCol pos 1) str with {val = val, stream = stream}
    then
      let val = cons c val in
      let info = makeInfo pos stream.pos in
      { token = OperatorTok {info = info, val = val}
      , lit = val
      , info = info
      , stream = stream}
    else never

  sem tokKindEq (tok : Tok) =
  | OperatorTok _ -> match tok with OperatorTok _ then true else false

  sem tokInfo =
  | OperatorTok {info = info} -> info
end

lang BracketTokenParser = TokenParser
  syn Token =
  | LParenTok {info : Info}
  | RParenTok {info : Info}
  | LBracketTok {info : Info}
  | RBracketTok {info : Info}
  | LBraceTok {info : Info}
  | RBraceTok {info : Info}

  sem parseToken (pos : Pos) =
  | "(" ++ str ->
    let pos2 = advanceCol pos 1 in
    let info = makeInfo pos pos2 in
    {token = LParenTok {info = info}, lit = "(", info = info, stream = {pos = pos2, str = str}}
  | ")" ++ str ->
    let pos2 = advanceCol pos 1 in
    let info = makeInfo pos pos2 in
    {token = RParenTok {info = info}, lit = ")", info = info, stream = {pos = pos2, str = str}}
  | "[" ++ str ->
    let pos2 = advanceCol pos 1 in
    let info = makeInfo pos pos2 in
    {token = LBracketTok {info = info}, lit = "[", info = info, stream = {pos = pos2, str = str}}
  | "]" ++ str ->
    let pos2 = advanceCol pos 1 in
    let info = makeInfo pos pos2 in
    {token = RBracketTok {info = info}, lit = "]", info = info, stream = {pos = pos2, str = str}}
  | "{" ++ str ->
    let pos2 = advanceCol pos 1 in
    let info = makeInfo pos pos2 in
    {token = LBraceTok {info = info}, lit = "{", info = info, stream = {pos = pos2, str = str}}
  | "}" ++ str ->
    let pos2 = advanceCol pos 1 in
    let info = makeInfo pos pos2 in
    {token = RBraceTok {info = info}, lit = "}", info = info, stream = {pos = pos2, str = str}}

  sem tokKindEq (tok : Tok) =
  | LParenTok _ -> match tok with LParenTok _ then true else false
  | RParenTok _ -> match tok with RParenTok _ then true else false
  | LBracketTok _ -> match tok with LBracketTok _ then true else false
  | RBracketTok _ -> match tok with RBracketTok _ then true else false
  | LBraceTok _ -> match tok with LBraceTok _ then true else false
  | RBraceTok _ -> match tok with RBraceTok _ then true else false

  sem tokInfo =
  | LParenTok {info = info} -> info
  | RParenTok {info = info} -> info
  | LBracketTok {info = info} -> info
  | RBracketTok {info = info} -> info
  | LBraceTok {info = info} -> info
  | RBraceTok {info = info} -> info
end

lang SemiTokenParser = TokenParser
  syn Token =
  | SemiTok {info : Info}

  sem parseToken (pos : Pos) =
  | ";" ++ str ->
    let pos2 = advanceCol pos 1 in
    let info = makeInfo pos pos2 in
    {token = SemiTok {info = info}, lit = ";", info = info, stream = {pos = pos2, str = str}}

  sem tokKindEq (tok : Tok) =
  | SemiTok _ -> match tok with SemiTok _ then true else false

  sem tokInfo =
  | SemiTok {info = info} -> info
end

lang CommaTokenParser = TokenParser
  syn Token =
  | CommaTok {info : Info}

  sem parseToken (pos : Pos) =
  | "," ++ str ->
    let pos2 = advanceCol pos 1 in
    let info = makeInfo pos pos2 in
    {token = CommaTok {info = info}, lit = ",", info = info, stream = {pos = pos2, str = str}}

  sem tokKindEq (tok : Tok) =
  | CommaTok _ -> match tok with CommaTok _ then true else false

  sem tokInfo =
  | CommaTok {info = info} -> info
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
  | StringTok {info : Info, val : String}

  sem parseToken (pos : Pos) =
  | "\"" ++ str ->
    recursive let work = lam acc. lam p2. lam str.
      match str with "\"" ++ str then
        {val = acc, pos = advanceCol p2 1, str = str}
      else match matchChar p2 str with {val = charval, pos = p2, str = str} then
        work (snoc acc charval) p2 str
      else never
    in match work "" (advanceCol pos 1) str with {val = val, pos = pos2, str = str} then
      let info = makeInfo pos pos2 in
      { token = StringTok {info = info, val = val}
      , lit = ""
      , info = info
      , stream = {pos = pos2, str = str}
      }
    else never

  sem tokKindEq (tok : Tok) =
  | StringTok _ -> match tok with StringTok _ then true else false

  sem tokInfo =
  | StringTok {info = info} -> info
end

lang CharTokenParser = TokenParser
  syn Token =
  | CharTok {info : Info, val : Char}

  sem parseToken (pos : Pos) =
  | "'" ++ str ->
    match matchChar (advanceCol pos 1) str with {val = val, pos = pos2, str = str} then
      match str with "'" ++ str then
        let pos2 = advanceCol pos2 1 in
        let info = makeInfo pos pos2 in
        { token = CharTok {info = info, val = val}
        , lit = ""
        , info = info
        , stream = {pos = pos2, str = str}
        }
      else posErrorExit pos "Expected ' to close character literal."
    else never

  sem tokKindEq (tok : Tok) =
  | CharTok _ -> match tok with CharTok _ then true else false

  sem tokInfo =
  | CharTok {info = info} -> info
end

lang HashStringTokenParser = TokenParser
  syn Token =
  | HashStringTok {info : Info, hash : String, val : String}

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
          let info = makeInfo pos pos2 in
          { token = HashStringTok {info = info, hash = hash, val = val}
          , lit = ""
          , info = info
          , stream = {pos = pos2, str = str}
          }
        else never
      else posErrorExit pos2 "Expected \" to begin hash string"
    else never

  sem tokKindEq (tok : Tok) =
  | HashStringTok {hash = hash} -> match tok with HashStringTok {hash = hash2}
    then eqString hash hash2
    else false

  sem tokInfo =
  | HashStringTok {info = info} -> info
end

lang Lexer
  = WhitespaceParser + LineCommentParser + MultilineCommentParser
  + EOFTokenParser + LIdentTokenParser + UIdentTokenParser
  + UIntTokenParser + UFloatTokenParser
  + OperatorTokenParser + BracketTokenParser + SemiTokenParser + CommaTokenParser
  + StringTokenParser + CharTokenParser
  + HashStringTokenParser

-- NOTE(vipa, 2021-02-05): This is not a semantic function in a
-- language fragment since the output for each case must be distinct
-- from the output for any other fragment, meaning that there would be
-- an invisible dependency between them
let _tokKindInt = use Lexer in lam tok.
  match tok with EOFTok _ then 1 else
  match tok with LIdentTok _ then 2 else
  match tok with UIdentTok _ then 3 else
  match tok with IntTok _ then 4 else
  match tok with FloatTok _ then 5 else
  match tok with OperatorTok _ then 6 else
  match tok with LParenTok _ then 7 else
  match tok with RParenTok _ then 8 else
  match tok with LBracketTok _ then 9 else
  match tok with RBracketTok _ then 10 else
  match tok with LBraceTok _ then 11 else
  match tok with RBraceTok _ then 12 else
  match tok with SemiTok _ then 13 else
  match tok with CommaTok _ then 14 else
  match tok with StringTok _ then 15 else
  match tok with CharTok _ then 16 else
  match tok with HashStringTok _ then 17 else
  never

let compareTokKind = use Lexer in lam ltok. lam rtok.
  let pair = (ltok, rtok) in
  match pair with (HashStringTok {hash = h1}, HashStringTok {hash = h2}) then cmpString h1 h2 else
  match pair with (HashStringTok _, _) then negi 1 else
  match pair with (_, HashStringTok _) then 1 else
  subi (_tokKindInt ltok) (_tokKindInt rtok)

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



use Lexer in

let start = initPos "file" in
let parse = lam str. nextToken {pos = start, str = str} in

utest parse " --foo \n  bar " with
  { token = LIdentTok {val = "bar", info = infoVal "file" 2 2 2 5}
  , lit = "bar"
  , info = infoVal "file" 2 2 2 5
  , stream = {pos = posVal "file" 2 5 , str = " "}
  } in

utest parse " /- foo -/ bar" with
  { token = LIdentTok {val = "bar", info = infoVal "file" 1 11 1 14}
  , lit = "bar"
  , info = infoVal "file" 1 11 1 14
  , stream = {pos = posVal "file" 1 14 , str = ""}
  } in

utest parse " /- foo\n x \n -/ \nbar " with
  { token = LIdentTok {val = "bar", info = infoVal "file" 4 0 4 3}
  , lit = "bar"
  , info = infoVal "file" 4 0 4 3
  , stream = {pos = posVal "file" 4 3 , str = " "}
  } in

utest parse " /- x -- y /- foo \n -/ -/ !" with
  { token = OperatorTok {val = "!", info = infoVal "file" 2 7 2 8}
  , lit = "!"
  , info = infoVal "file" 2 7 2 8
  , stream = {pos = posVal "file" 2 8 , str = ""}
  } in

utest parse "  123foo" with
  { token = IntTok {val = 123, info = infoVal "file" 1 2 1 5}
  , lit = ""
  , info = infoVal "file" 1 2 1 5
  , stream = {pos = posVal "file" 1 5 , str = "foo"}
  } in

utest parse "  1.0" with
  { token = FloatTok {val = 1.0, info = infoVal "file" 1 2 1 5}
  , lit = ""
  , info = infoVal "file" 1 2 1 5
  , stream = {pos = posVal "file" 1 5 , str = ""}
  } in

utest parse " 1234.  " with
  { token = FloatTok {val = 1234.0, info = infoVal "file" 1 1 1 6}
  , lit = ""
  , info = infoVal "file" 1 1 1 6
  , stream = {pos = posVal "file" 1 6 , str = "  "}
  } in

utest parse " 13.37 " with
  { token = FloatTok {val = 13.37, info = infoVal "file" 1 1 1 6}
  , lit = ""
  , info = infoVal "file" 1 1 1 6
  , stream = {pos = posVal "file" 1 6, str = " "}
  } in

utest parse "  1.0e-2" with
  { token = FloatTok {val = 0.01, info = infoVal "file" 1 2 1 8}
  , lit = ""
  , info = infoVal "file" 1 2 1 8
  , stream = {pos = posVal "file" 1 8, str = ""}
  } in

utest parse " 2.5e+2  " with
  { token = FloatTok {val = 250.0, info = infoVal "file" 1 1 1 7}
  , lit = ""
  , info = infoVal "file" 1 1 1 7
  , stream = {pos = posVal "file" 1 7, str = "  "}
  } in

utest parse "   2e3" with
  { token = FloatTok {val = 2000.0, info = infoVal "file" 1 3 1 6}
  , lit = ""
  , info = infoVal "file" 1 3 1 6
  , stream = {pos = posVal "file" 1 6, str = ""}
  } in

utest parse "   2E3" with
  { token = FloatTok {val = 2000.0, info = infoVal "file" 1 3 1 6}
  , lit = ""
  , info = infoVal "file" 1 3 1 6
  , stream = {pos = posVal "file" 1 6, str = ""}
  } in

utest parse "   2.0E3" with
  { token = FloatTok {val = 2000.0, info = infoVal "file" 1 3 1 8}
  , lit = ""
  , info = infoVal "file" 1 3 1 8
  , stream = {pos = posVal "file" 1 8, str = ""}
  } in

utest parse "   2.E3" with
  { token = FloatTok {val = 2000.0, info = infoVal "file" 1 3 1 7}
  , lit = ""
  , info = infoVal "file" 1 3 1 7
  , stream = {pos = posVal "file" 1 7, str = ""}
  } in

utest parse " 1.e2 " with
  { token = FloatTok {val = 100.0, info = infoVal "file" 1 1 1 5}
  , lit = ""
  , info = infoVal "file" 1 1 1 5
  , stream = {pos = posVal "file" 1 5, str = " "}
  } in

utest parse " 3.e-4 " with
  { token = FloatTok {val = 0.0003, info = infoVal "file" 1 1 1 6}
  , lit = ""
  , info = infoVal "file" 1 1 1 6
  , stream = {pos = posVal "file" 1 6, str = " "}
  } in

utest parse " 4.E+1 " with
  { token = FloatTok {val = 40.0, info = infoVal "file" 1 1 1 6}
  , lit = ""
  , info = infoVal "file" 1 1 1 6
  , stream = {pos = posVal "file" 1 6, str = " "}
  } in

utest parse " 1.E-3 " with
  { token = FloatTok {val = 0.001, info = infoVal "file" 1 1 1 6}
  , lit = ""
  , info = infoVal "file" 1 1 1 6
  , stream = {pos = posVal "file" 1 6, str = " "}
  } in

utest parse " 1E " with
  { token = IntTok {val = 1, info = infoVal "file" 1 1 1 2}
  , lit = ""
  , info = infoVal "file" 1 1 1 2
  , stream = {pos = posVal "file" 1 2, str = "E "}
  } in

utest parse " 1e " with
  { token = IntTok {val = 1, info = infoVal "file" 1 1 1 2}
  , lit = ""
  , info = infoVal "file" 1 1 1 2
  , stream = {pos = posVal "file" 1 2, str = "e "}
  } in

utest parse " 1.e++2 " with
  { token = FloatTok {val = 1.0, info = infoVal "file" 1 1 1 3}
  , lit = ""
  , info = infoVal "file" 1 1 1 3
  , stream = {pos = posVal "file" 1 3, str = "e++2 "}
  } in

utest parse " 3.1992e--2 " with
  { token = FloatTok {val = 3.1992, info = infoVal "file" 1 1 1 7}
  , lit = ""
  , info = infoVal "file" 1 1 1 7
  , stream = {pos = posVal "file" 1 7, str = "e--2 "}
  } in

utest parse "  if 1 then 22 else 3" with
  { token = LIdentTok {val = "if", info = infoVal "file" 1 2 1 4}
  , lit = "if"
  , info = infoVal "file" 1 2 1 4
  , stream = {pos = posVal "file" 1 4, str = " 1 then 22 else 3"}
  } in

utest parse " true " with
  { token = LIdentTok {val = "true", info = infoVal "file" 1 1 1 5}
  , lit = "true"
  , info = infoVal "file" 1 1 1 5
  , stream = {pos = posVal "file" 1 5, str = " "}
  } in

utest parse " ( 123) " with
  { token = LParenTok {info = infoVal "file" 1 1 1 2}
  , lit = "("
  , info = infoVal "file" 1 1 1 2
  , stream = {pos = posVal "file" 1 2, str = " 123) "}
  } in

utest parse "[]" with
  { token = LBracketTok {info = infoVal "file" 1 0 1 1}
  , lit = "["
  , info = infoVal "file" 1 0 1 1
  , stream = {pos = posVal "file" 1 1, str = "]"}
  } in

utest parse " [ ] " with
  { token = LBracketTok {info = infoVal "file" 1 1 1 2}
  , lit = "["
  , info = infoVal "file" 1 1 1 2
  , stream = {pos = posVal "file" 1 2, str = " ] "}
  } in

utest parse " [ 17 ] " with
  { token = LBracketTok {info = infoVal "file" 1 1 1 2}
  , lit = "["
  , info = infoVal "file" 1 1 1 2
  , stream = {pos = posVal "file" 1 2, str = " 17 ] "}
  } in

utest parse " [ 232 , ( 19 ) ] " with
  { token = LBracketTok {info = infoVal "file" 1 1 1 2}
  , lit = "["
  , info = infoVal "file" 1 1 1 2
  , stream = {pos = posVal "file" 1 2, str = " 232 , ( 19 ) ] "}
  } in

utest parse " \"Foo\" " with
  { token = StringTok {val = "Foo", info = infoVal "file" 1 1 1 6}
  , lit = ""
  , info = infoVal "file" 1 1 1 6
  , stream = {pos = posVal "file" 1 6, str = " "}
  } in

utest parse " \" a\\\\ \\n\" " with
  { token = StringTok {val = " a\\ \n", info = infoVal "file" 1 1 1 10}
  , lit = ""
  , info = infoVal "file" 1 1 1 10
  , stream = {pos = posVal "file" 1 10, str = " "}
  } in

utest parse " \'A\' " with
  { token = CharTok {val = 'A', info = infoVal "file" 1 1 1 4}
  , lit = ""
  , info = infoVal "file" 1 1 1 4
  , stream = {pos = posVal "file" 1 4, str = " "}
  } in

utest parse " \'\\n\' " with
  { token = CharTok {val = '\n', info = infoVal "file" 1 1 1 5}
  , lit = ""
  , info = infoVal "file" 1 1 1 5
  , stream = {pos = posVal "file" 1 5, str = " "}
  } in

utest parse " _xs " with
  { token = LIdentTok {val = "_xs", info = infoVal "file" 1 1 1 4}
  , lit = "_xs"
  , info = infoVal "file" 1 1 1 4
  , stream = {pos = posVal "file" 1 4, str = " "}
  } in

utest parse " fOO_12a " with
  { token = LIdentTok {val = "fOO_12a", info = infoVal "file" 1 1 1 8}
  , lit = "fOO_12a"
  , info = infoVal "file" 1 1 1 8
  , stream = {pos = posVal "file" 1 8, str = " "}
  } in

utest parse " lam x . x " with
  { token = LIdentTok {val = "lam", info = infoVal "file" 1 1 1 4}
  , lit = "lam"
  , info = infoVal "file" 1 1 1 4
  , stream = {pos = posVal "file" 1 4, str = " x . x "}
  } in

utest parse " Lam x . x " with
  { token = UIdentTok {val = "Lam", info = infoVal "file" 1 1 1 4}
  , lit = "Lam"
  , info = infoVal "file" 1 1 1 4
  , stream = {pos = posVal "file" 1 4, str = " x . x "}
  } in

utest parse "  let x = 5 in 8 " with
  { token = LIdentTok {val = "let", info = infoVal "file" 1 2 1 5}
  , lit = "let"
  , info = infoVal "file" 1 2 1 5
  , stream = {pos = posVal "file" 1 5, str = " x = 5 in 8 "}
  } in

utest parse " += 47;" with
  { token = OperatorTok {val = "+=", info = infoVal "file" 1 1 1 3}
  , lit = "+="
  , info = infoVal "file" 1 1 1 3
  , stream = {pos = posVal "file" 1 3, str = " 47;"}
  } in

utest parse " ; println foo" with
  { token = SemiTok {info = infoVal "file" 1 1 1 2}
  , lit = ";"
  , info = infoVal "file" 1 1 1 2
  , stream = {pos = posVal "file" 1 2, str = " println foo"}
  } in

utest parse " #foo\"Zomething\"more" with
  { token = HashStringTok {hash = "foo", val = "Zomething", info = infoVal "file" 1 1 1 16}
  , lit = ""
  , info = infoVal "file" 1 1 1 16
  , stream = {pos = posVal "file" 1 16, str = "more"}
  } in

utest parse " #\"Zomething\"more" with
  { token = HashStringTok {hash = "", val = "Zomething", info = infoVal "file" 1 1 1 13}
  , lit = ""
  , info = infoVal "file" 1 1 1 13
  , stream = {pos = posVal "file" 1 13, str = "more"}
  } in

utest parse " #123\"Zomething\"more" with
  { token = HashStringTok {hash = "123", val = "Zomething", info = infoVal "file" 1 1 1 16}
  , lit = ""
  , info = infoVal "file" 1 1 1 16
  , stream = {pos = posVal "file" 1 16, str = "more"}
  } in

()
