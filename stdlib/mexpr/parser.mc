

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
  | "*-" ++ xs ->
    recursive
    let remove = lam p. lam str. lam d.
      match str with "*-" ++ xs then remove (advanceCol p 2) xs (addi d 1) else
      match str with "\n" ++ xs then remove (advanceRow p 1) xs d else
      match str with "-*" ++ xs then
        if eqi d 0 then eatWSAC (advanceCol p 2) xs
        else remove (advanceCol p 2) xs (subi d 1) else
      match str with [_] ++ xs then remove (advanceCol p 1) xs d else
      eatWSAC p str
    in remove (advanceCol p 2) xs 0
end

-- Commbined WSAC parser for MCore
lang MCoreWSACParser = WhitespaceParser + LineCommentParser + MultilineCommentParser

let _ = use MCoreWSACParser in
  utest eatWSAC (initPos "") " --foo \n  bar " with {str = "bar ", pos = posVal "" 2 2} in
  utest eatWSAC (initPos "") " *- foo -* bar" with {str = "bar", pos = posVal "" 1 11} in
  utest eatWSAC (initPos "") " *- foo\n x \n -* \nbar " with {str = "bar ", pos = posVal "" 4 0} in
  utest eatWSAC (initPos "") " *- x -- y *- foo \n -* z -* !" with {str = "!", pos = posVal "" 2 9} in
  ()


lang MExprParser = WhitespaceParser
