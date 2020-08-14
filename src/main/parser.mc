-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "seq.mc"
include "string.mc"
include "name.mc"
include "symtable.mc"
include "seqExtra.mc"


type ProdName = Name       -- Production name
type Termame = Name        -- Terminal name
type NonTermName = Name    -- Nonterminal name

type PSymbol
con TermSym    : (String, TermName) -> PSymbol     -- Terminal node symbol
con NonTermSym : (String, NonTermName) -> PSymbol  -- Nonterminal node symbol

-- The main state of the lexer and parser
type ParseState = {
  terminals: SymTable,
  nonTerminals: SymTable,
  productions: [(NonTermName, [(ProdName, [PSymbol])])]
}


-- Token (terminal) that marks end of file (end of string)
let _symInit = symtableAdd (nameNoSym ":EOF:") symtableEmpty
let tokenEOF = _symInit.name


-- An empty parse state
let emptyParseState = {
  terminals = _symInit.table,
  nonTerminals = symtableEmpty,
  productions = []
}


-- Add production. TODO: Checking of validity of production rules
-- 'addProd prodStr ntStr symList pState' returns a new parse state, where
--   'prodStr' is the name of the production,
--   'ntStr' is the left-hand side nonterminal,
--   'symList' is a list of non-terminals and terminals for the production, and
--   'pState' is the previous parse state.
let addProduction : String -> String -> [PSymbol] -> ParseState -> ParseState =
  lam prodStr. lam ntStr. lam symList. lam pState.
    let v = foldl (lam acc. lam e.
      match acc with (state, lst) then
        match e with TermSym (x, n) then
          let r = symtableAdd n state.terminals in
          ({state with terminals = r.table}, cons (TermSym (x, r.name)) lst)
        else match e with NonTermSym (x, n) then
          let r = symtableAdd n state.nonTerminals in
          ({state with nonTerminals = r.table}, cons (NonTermSym (x, r.name)) lst)
        else never
      else never) (pState, []) symList in
    let r = symtableAdd (nameNoSym ntStr) (v.0).nonTerminals in
    let state = {v.0 with nonTerminals = r.table} in
    let prod = (nameSym prodStr, reverse v.1) in
    let prodList = match findAssoc (nameEqSym r.name) state.productions with Some prodList
                   then prodList else [] in
    let newProds = addAssoc nameEqSym r.name (cons prod prodList) state.productions in
    {state with productions = newProds}


-- Functions for eating white space and comments (WSAC).
-- Returns a record {remaining:string, wsac:string} where 'remaining'
-- is the remaining string, and 'wsac' is the eaten WASC
let eatWSAC = lam str.
  recursive
  let eatWhitespace = lam x. lam acc.
    match x with " " ++ xs then eatWhitespace xs (snoc acc ' ') else
    match x with "\n" ++ xs then eatWhitespace xs (snoc acc '\n') else
    match x with "\t" ++ xs then eatWhitespace xs (snoc acc '\t') else
    match x with "--" ++ xs then eatLineComment xs (concat acc "--") else
    {remaining=x,wsac=acc}
  let eatLineComment = lam x. lam acc.
    match x with "\n" ++ xs then eatWhitespace xs (snoc acc '\n') else
    match x with [x] ++ xs then eatLineComment xs (snoc acc x) else
    {remaining=x,wsac=acc}
  in eatWhitespace str []

utest eatWSAC "foo" with {remaining="foo",wsac=""}
utest eatWSAC " \n bar foo" with {remaining="bar foo",wsac=" \n "}
utest eatWSAC "   -- comment\n  foo" with {remaining="foo",wsac="   -- comment\n  "}
utest eatWSAC " -- foo " with {remaining="",wsac=" -- foo "}


-- Temp function before we can handle regex. Note that an identifier cannot include numbers
-- Returns an optional record matching an identier.
-- Some{val:string, remaining:string}
let getIdent = lam str.
  recursive
  let ident = lam x. lam acc. lam first.
    match x with [y] ++ xs then
      if or (or (or (and (geqchar y 'A') (leqchar y 'Z'))
                (and (geqchar y 'a') (leqchar y 'z'))) (eqchar y '_'))
             (and (not first) (and (geqchar y '0') (leqchar y '9')))
      then ident xs (snoc acc y) false
      else if eqi (length acc) 0 then None() else Some{val=acc,remaining=x}
    else if eqi (length acc) 0 then None() else Some{val=acc,remaining=[]}
  in ident str [] true

utest getIdent "foo bar" with Some{val="foo", remaining=" bar"}
utest getIdent "12foo bar" with None()


-- Temp function before we can handle regex. Get a number literal.
-- Returns an optional record matching an identier.
-- Some{val:string, remaining:string}
let getNum = lam str.
  recursive
  let num = lam x. lam acc.
    match x with [y] ++ xs then
      if and (geqchar y '0') (leqchar y '9')
      then num xs (snoc acc y)
      else if eqi (length acc) 0 then None () else Some {val=acc, remaining=x}
    else if eqi (length acc) 0 then None () else Some {val=acc, remaining=[]}
  in num str []

utest getNum "123 bar" with Some{val="123", remaining=" bar"}
utest getNum "foo" with None()


-- A special named token that is returned if a token is not found
let tokenNotFound = nameSym "NOT_FOUND"


-- 'findToken x ps' searches for a token with name 'x' among the terminals
-- in parse state 'ps' and returns the name if found. If not found,
-- 'tokNotFound' is returned.
let findToken : String -> ParseState -> Name =
  lam x. lam ps.
    match find (nameEqStr (nameNoSym x)) ps.terminals with Some n then n
    else tokenNotFound

utest findToken ":EOF:" emptyParseState with tokenEOF
utest findToken "nothing" emptyParseState with tokenNotFound


-- Constructor function of terminal symbol
let t : String -> String -> PSymbol =
  lam var. lam tString. TermSym (var, nameNoSym tString)


-- Constructor function of non-terminal symbol
let nt : String -> String -> PSymbol =
  lam var. lam ntString. NonTermSym (var, nameNoSym ntString)


-- A test state for parsing. A simple expression language
let _testParseState =
  let s = emptyParseState in
  let s = addProduction "let" "Expr"
      [(t "0" "let"), (t "x" ":ident:"), (t "2" "="), (nt "e1" "Expr"), (t "4" "in"), (nt "e2" "Expr")] s in
  let s = addProduction "ident" "Expr" [(t "x" ":ident:")] s in
  let s = addProduction "num" "Expr" [(t "x" ":num:")] s in
  let s = addProduction "add" "Expr" [(nt "e1" "Expr"), (t "0" "+"), (nt "e2" "Expr")] s in
  let s = addProduction "mul" "Expr" [(nt "e1" "Expr"), (t "0" "*"), (nt "e2" "Expr")] s in
  let s = addProduction "app" "Expr" [(nt "e1" "Expr"), (nt "e2" "Expr")] s in
  s


-- 'getToken ps str' returns the next state, using the parse state 'ps' and reading
-- from string 'str'.
-- Matches and returns the next token as record type
-- {wsac:String, token:Name, val:String, remaining:String})
-- TODO: implement a more efficient and complete scanner using regular expressions
let getToken = lam ps. lam str.
  let w = eatWSAC str in
  if eqi (length w.remaining) 0 then {wsac = w.wsac, token = tokenEOF, val = "", remaining = ""}
  else match find (lam tok. isPrefix eqc (nameGetStr tok) w.remaining) ps.terminals with Some n then
    let x = nameGetStr n in
    {wsac = w.wsac, token = n, val = x,
     remaining = slice w.remaining (length x) (subi (length w.remaining) (length x))}
  else
    match getIdent w.remaining with Some r then
      {wsac = w.wsac, token = findToken ":ident:" ps, val = r.val, remaining = r.remaining}
    else match getNum w.remaining with Some r then
      {wsac = w.wsac, token = findToken ":num:" ps, val = r.val, remaining = r.remaining}
    else error "Lexical error"


-- Test the scanner using _testParseState
utest getToken _testParseState "  +let" with
  {wsac = "  ", token = findToken "+" _testParseState, val = "+", remaining = "let"}
utest getToken _testParseState " let+ " with
  {wsac = " ", token = findToken "let" _testParseState, val = "let", remaining = "+ "}
utest getToken _testParseState "   123let+ " with
  {wsac = "   ", token =findToken ":num:" _testParseState, val = "123", remaining = "let+ "}
utest getToken _testParseState " something+boo " with
  {wsac = " ", token = findToken ":ident:" _testParseState, val = "something", remaining = "+boo "}
utest getToken _testParseState " _foo12 more" with
  {wsac = " ", token = findToken ":ident:" _testParseState, val = "_foo12", remaining = " more"}
utest getToken _testParseState "  " with
  {wsac = "  ", token = tokenEOF, val = "", remaining = ""}




mexpr

()
