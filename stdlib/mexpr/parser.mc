

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

-- Eat line comments of the form '--'
lang LineCommentParser = WSACParser
  sem eatWSAC (p : Pos)  =
  | "--" ++ xs ->
    recursive
    let remove = lam str. lam p.
      match str with "\n" ++ xs then eatWSAC (advanceRow p 1) xs else
      match str with [x] ++ xs then remove xs (advanceCol p 1) else
      eatWSAC p str
    in remove xs p
end

-- Commbined WSAC parser for MCore
lang MCoreWSACParser = WhitespaceParser + LineCommentParser

let _ = use MCoreWSACParser in
  utest eatWSAC (initPos "") " --foo \n  bar " with {str = "bar ", pos = posVal "" 2 2} in
  ()


lang MExprParser = WhitespaceParser
