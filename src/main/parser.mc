-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "set.mc"
include "seq.mc"
include "char.mc"
include "string.mc"




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







type ProdName = Name     -- Production name
type TName = Name        -- Terminal name
type NTName = Name       -- Nonterminal name

type PSymbol
con T  : NonTermName -> PSymbol   -- Terminal node symbol
con NT : TermName -> PSymbol  -- Nonterminal node symbol


type ParseState = {
  tokens: SymTable,          -- The index is the token symbol identifier
  nonTerminals: SymTable,    -- The index is the symbol identifier for the non terminal
  productions: [(NonTermName,[(ProdName,[PSymbol])])] -- Associate map from non
}

-- An empty parse state
let emptyParseState = {
  tokens = symtableEmpty,
  nonTerminals = symtableEmpty,
  productions = []
}




let addProduction : ProdName -> NonTermName -> [PSymbol] -> ParseState -> ParseState option
  = lam prodName. lam. ntName. lam.  lam pstate. ()




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
-- Returns a record {remstr:string, wsac:string} where 'remstr'
-- is the remaining string, and 'wsac' is the eaten WASC
let eatWSAC = lam str.
  recursive
  let eatWhitespace = lam x. lam acc.
    match x with " " ++ xs then eatWhitespace xs (snoc acc ' ') else
    match x with "\n" ++ xs then eatWhitespace xs (snoc acc '\n') else
    match x with "\t" ++ xs then eatWhitespace xs (snoc acc '\t') else
    match x with "--" ++ xs then eatLineComment xs (concat acc "--") else
    {remstr=x,wsac=acc}
  let eatLineComment = lam x. lam acc.
    match x with "\n" ++ xs then eatWhitespace xs (snoc acc '\n') else
    match x with [x] ++ xs then eatLineComment xs (snoc acc x) else
    {remstr=x,wsac=acc}
  in eatWhitespace str []

utest eatWSAC "foo" with {remstr="foo",wsac=""}
utest eatWSAC " \n bar foo" with {remstr="bar foo",wsac=" \n "}
utest eatWSAC "   -- comment\n  foo" with {remstr="foo",wsac="   -- comment\n  "}
utest eatWSAC " -- foo " with {remstr="",wsac=" -- foo "}

-- Returns a list of unique tokens. The index in this list will be used
-- as unqiue symbols when matching tokens in the future.
let getTokenList = lam rules.
    foldl (lam acc. lam e.
       match e with (_,(_,lst)) then
         foldl (lam acc. lam e. match e with T(_,x)
	                        then setInsert eqstr x acc else acc) acc lst
       else never
    ) "" rules

utest getTokenList testRules with ["let","=","in",":ident:",":num:","+","*"]

-- Temp function before we can handle regex. Note that an identifier cannot include numbers
-- Returns an optional record matching an identier.
-- Some{val:string, remstr:string}
let getIdent = lam str.
  recursive
  let ident = lam x. lam acc. lam first.
    match x with [y] ++ xs then
      if or (or (or (and (geqchar y 'A') (leqchar y 'Z'))
                (and (geqchar y 'a') (leqchar y 'z'))) (eqchar y '_'))
             (and (not first) (and (geqchar y '0') (leqchar y '9')))
      then ident xs (snoc acc y) false
      else if eqi (length acc) 0 then None() else Some{val=acc,remstr=x}
    else if eqi (length acc) 0 then None() else Some{val=acc,remstr=[]}
  in ident str [] true

utest getIdent "foo bar" with Some{val="foo", remstr=" bar"}
utest getIdent "12foo bar" with None()

-- Temp function before we can handle regex. Get a number literal.
-- Returns an optional record matching an identier.
-- Some{val:string, remstr:string}
let getNum = lam str.
  recursive
  let num = lam x. lam acc.
    match x with [y] ++ xs then
      if and (geqchar y '0') (leqchar y '9')
      then num xs (snoc acc y)
      else if eqi (length acc) 0 then None() else Some{val=acc,remstr=x}
    else if eqi (length acc) 0 then None() else Some{val=acc,remstr=[]}
  in num str []

utest getNum "123 bar" with Some{val="123",remstr=" bar"}
utest getNum "foo" with None()



-- Matches and returns the next token as record type
-- {wsac:string, tok:int, val:string, remstr:string})
-- If it is the end, then tok = -1.
let getToken = lam tokenList. lam str.
  let w = eatWSAC str in
  if eqi (length w.remstr) 0 then {wsac=w.wsac, tok=negi 1, val="", remstr=""}
  else match index (lam tok. isPrefix eqc tok w.remstr) tokenList with Some n then
    let x = get tokenList n in
    {wsac=w.wsac, tok=n, val=x, remstr=slice w.remstr (length x) (subi (length w.remstr) (length x))}
  else
    let tokId = lam x. optionGetOr (negi 1) (index (eqstr x) tokenList) in
    match getIdent w.remstr with Some r then
      {wsac=w.wsac, tok=tokId ":ident:", val=r.val, remstr=r.remstr}
    else match getNum w.remstr with Some r then
      {wsac=w.wsac, tok=tokId ":num:", val=r.val, remstr=r.remstr}
    else error "Lexical error"

let _rules = getTokenList testRules
let _tokId = lam x. optionGetOr (negi 1) (index (eqstr x) _rules)
utest getToken _rules "  +let" with
  {wsac="  ", tok=_tokId "+", val="+", remstr="let"}
utest getToken _rules " let+ " with
  {wsac=" ", tok=_tokId "let", val="let", remstr="+ "}
utest getToken _rules "   123let+ " with
  {wsac="   ", tok=_tokId ":num:", val="123", remstr="let+ "}
utest getToken _rules " something+boo " with
  {wsac=" ", tok=_tokId ":ident:", val="something", remstr="+boo "}
utest getToken _rules " _foo12 more" with
  {wsac=" ", tok=_tokId ":ident:", val="_foo12", remstr=" more"}
utest getToken _rules "  " with
  {wsac="  ", tok=negi 1, val="", remstr=""}


mexpr

()
