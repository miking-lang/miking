-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "seq.mc"
include "char.mc"
include "string.mc"


type Rule
con T  : (String) -> Rule         -- Terminal node
con NT : (String,String) -> Rule  -- Nonterminal node


-- In this first draft version, "Ident" and "Num" are built in special non-term


let parse = lam str. lam rules.
  "1"


recursive
  let letTok = lam x. match x with "let" ++ xs then (xs,"let") else (x,"")
  let eqTok = lam x. match x with "=" ++ xs then (xs,"=") else (x,"")
  let must = lam r. if eqstr r.1 "" then error "Unexpected token" else r
  let ignore = lam x. lam acc.
    match x with " " ++ xs then ignore xs (concat acc " ") else
    match x with "\n" ++ xs then ignore xs (concat acc "\n") else
    match x with "\t" ++ xs then ignore xs (concat acc "\t") else
    (x,acc)
  let ident = lam x. lam acc.
    match x with [y] ++ xs then
      if or (or (and (geqchar y 'A') (leqchar y 'Z'))
                (and (geqchar y 'a') (leqchar y 'z'))) (eqchar y '_')
      then ident xs (snoc acc y) else (x,acc)
    else ([],acc)
  let pExpr = lam x.
    let r1 = ignore x "" in
    let r2 = must (letTok r1.0) in
    let r3 = ignore r2.0 "" in
    let r4 = must (ident r3.0 "") in
    let r5 = ignore r4.0 "" in
    let r6 = must (eqTok r5.0) in
    let r7 = ignore r6.0 "" in
    r7.0
end


let testRules = [
-- #syn let = Expr -> "let" x:ident "=" e1:Expr "in" e2:Expr
("let", ("Expr", [T("0","let"), NT("x",":ident:"), T("2","="), NT("e1","Expr"), T("4","in"), NT("e2","Expr")])),
-- #syn ident = Expr -> x:ident
("ident", ("Expr", [T("x",":ident:")])),
-- #syn num = Expr -> x:num
("num", ("Expr", [T("x",":num:")])),
-- #syn add = Expr -> e1:Expr "+" e2:Expr
("add", ("Expr", [NT("e1","Expr"), T("0","+"), NT("e2","Expr")])),
-- #syn mul = Expr -> e1:Expr "*" e2:Expr
("mul", ("Expr", [NT("e1","Expr"), T("0","*"), NT("e2","Expr")])),
-- #syn app = Expr -> e1:Expr e2:Expr
("app", ("Expr", [NT("e1","Expr"), NT("e2","Expr")]))
]

-- Functions for eating white space and comments (WSAC).
-- Returns a tuple where the first element is the remaining
-- string and the second element is the eaten WASC
let eatWSAC = lam str.
  recursive
  let eatWhitespace = lam x. lam acc.
    match x with " " ++ xs then eatWhitespace xs (snoc acc ' ') else
    match x with "\n" ++ xs then eatWhitespace xs (snoc acc '\n') else
    match x with "\t" ++ xs then eatWhitespace xs (snoc acc '\t') else
    match x with "--" ++ xs then eatLineComment xs (concat acc "--") else
    (x,acc)
  let eatLineComment = lam x. lam acc.
    match x with "\n" ++ xs then eatWhitespace xs (snoc acc '\n') else
    match x with [x] ++ xs then eatLineComment xs (snoc acc x) else never
  in eatWhitespace str []

utest eatWSAC "foo" with ("foo","")
utest eatWSAC " \n bar foo" with ("bar foo"," \n ")
utest eatWSAC "   -- comment\n  foo" with ("foo","   -- comment\n  ")

-- Parses a program
let parse = lam rules. lam prod. lam str.
  ()


--utest parse testRules "Expr" "let x = 5 in x" with ""




mexpr














()
