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

type ParseState = {
  terminals: SymTable,
  nonTerminals: SymTable,
  productions: [(NonTermName, [(ProdName, [PSymbol])])]
}

-- An empty parse state
let emptyParseState = {
  terminals = symtableEmpty,
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




-- Constructor function of terminal symbol
let t : String -> String -> PSymbol =
  lam var. lam tString. TermSym (var, nameNoSym tString)

-- Constructor function of non-terminal symbol
let nt : String -> String -> PSymbol =
  lam var. lam ntString. NonTermSym (var, nameNoSym ntString)

-- A test state for parsing
let testParseState =
  let s = emptyParseState in
  let s = addProduction "let" "Expr"
      [(t "0" "let"), (t "x" ":ident:"), (t "2" "="), (nt "e1" "Expr"), (t "4" "in"), (nt "e2" "Expr")] s in
  let s = addProduction "ident" "Expr" [(t "x" ":ident:")] s in
  let s = addProduction "num" "Expr" [(t "x" ":num:")] s in
  let s = addProduction "add" "Expr" [(nt "e1" "Expr"), (t "0" "+"), (nt "e2" "Expr")] s in
  let s = addProduction "mul" "Expr" [(nt "e1" "Expr"), (t "0" "*"), (nt "e2" "Expr")] s in
  let s = addProduction "app" "Expr" [(nt "e1" "Expr"), (nt "e2" "Expr")] s in
  s



mexpr

()
