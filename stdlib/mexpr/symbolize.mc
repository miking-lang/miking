-- Symbolization of the MExpr ast.

include "name.mc"
include "string.mc"
include "assoc.mc"

include "mexpr/ast.mc"
include "mexpr/pprint.mc"

---------------------------
-- SYMBOLIZE ENVIRONMENT --
---------------------------
-- TODO The environment differs from boot, since we do not have access to the
-- unique string identifiers from ustring.ml. Instead, we use strings directly.

type Ident
con IdVar   : String -> Ident
con IdCon   : String -> Ident
con IdType  : String -> Ident
con IdLabel : String -> Ident
let identEq : Ident -> Ident -> Bool =
  lam i1. lam i2. match (i1,i2) with
      (IdVar   s1, IdVar   s2)
    | (IdCon   s1, IdCon   s2)
    | (IdType  s1, IdType  s2)
    | (IdLabel s1, IdLabel s2)
    then eqstr s1 s2
    else false

type Env = AssocMapIdentSymbol -- i.e., [(Ident, Symbol)]

let lookup = assocLookup {eq = identEq}
let insert = assocInsert {eq = identEq}
let recmap = assocMap {eq = identEq}
let mapAccum = assocMapAccum {eq = identEq}

-----------
-- TERMS --
-----------

lang VarSym = VarAst
  sem symbolize (env : Env) =
  | TmVar {ident = (str, _)} ->
    match lookup (IdVar str) env
    with Some sym then TmVar {ident = (str, sym)}
    else error (concat "Unknown variable in symbolize: " str)
end

lang AppSym = AppAst
  sem symbolize (env : Env) =
  | TmApp {lhs = lhs, rhs = rhs} ->
    TmApp {lhs = symbolize env lhs, rhs = symbolize env rhs}
end

lang FunSym = FunAst
  sem symbolize (env : Env) =
  | TmLam {ident = (str, _), tpe = tpe, body = body} ->
    let sym = gensym () in
    let env = insert (IdVar str) sym env in
    TmLam {ident = (str,sym), tpe = tpe, body = symbolize env body}
end

lang RecordSym = RecordAst
  sem symbolize (env : Env) =
  | TmRecord {bindings = bindings} ->
    TmRecord {bindings = recmap (symbolize env) bindings}

  | TmRecordUpdate {rec = rec, key = key, value = value} ->
    TmRecordUpdate {rec = symbolize env rec, key = key,
                    value = symbolize env value}
end

lang LetSym = LetAst
  sem symbolize (env : Env) =
  | TmLet {ident = (str, _),  body = body, inexpr = inexpr} ->
    let body = symbolize env body in
    let sym = gensym () in
    let env = insert (IdVar str) sym env in
    TmLet {ident = (str,sym), body = body, inexpr = symbolize env inexpr}
end

lang RecLetsSym = RecLetsAst
  sem symbolize (env : Env) =
  | TmRecLets {bindings = bindings, inexpr = inexpr} ->
    let bindings =
      map (lam bind. {bind with ident = nameSetNewSym bind.ident}) bindings in
    let env =
      foldl
        (lam env. lam bind.
           insert (IdVar (nameGetStr bind.ident)) (nameGetSym bind.ident) env)
        env bindings in
    TmRecLets {bindings = bindings, inexpr = symbolize env inexpr}
end

lang ConstSym = ConstAst
  sem symbolize (env : Env) =
  | TmConst t -> TmConst t
end

lang DataSym = DataAst
  sem symbolize (env : Env) =
  | TmConDef {ident = (str,_), tpe = tpe, inexpr = inexpr} ->
    let sym = gensym () in
    let env = insert (IdCon str) sym env in
    TmConDef {ident = (str,sym), tpe = tpe, inexpr = symbolize env inexpr}
  | TmConApp {ident = (str,_), body = body} ->
    match lookup (IdCon str) env
    with Some sym then TmConApp {ident = (str, sym), body = symbolize env body}
    else error (concat "Unknown constructor in symbolize: " str)
end

lang MatchSym = MatchAst
  sem symbolizePat (env : Env) =
  -- Intentionally left blank

  sem symbolize (env : Env) =
  | TmMatch {target = target, pat = pat, thn = thn, els = els} ->
    match symbolizePat env pat
    with (thnenv, pat) then
      TmMatch {target = symbolize env target,
               pat = pat, thn = symbolize thnenv thn, els = symbolize env els}
    else never
end

lang UtestSym = UtestAst
  sem symbolize (env : Env) =
  | TmUtest {test = test, expected = expected, next = next} ->
    TmUtest {test = symbolize env test,
             expected = symbolize env expected,
             next = symbolize env next}
end

lang SeqSym = SeqAst
  sem symbolize (env : Env) =
  | TmSeq {tms = tms} -> TmSeq {tms = map (symbolize env) tms}
end

lang NeverSym = NeverAst
  sem symbolize (env : Env) =
  | TmNever {} -> TmNever {}
end

--------------
-- PATTERNS --
--------------

lang VarPatSym = VarPat
  sem symbolizePat (env : Env) =
  | PVar {ident = PName (str,_)} ->
    let l = lookup (IdVar str) env in
    match l with Some sym then
      (env, PVar {ident = PName (str,sym)})
    else match l with None () then
      let sym = gensym () in
      let env = insert (IdVar str) sym env in
      (env, PVar {ident = PName (str,sym)})
    else never
  | PVar {ident = PWildcard name} ->
    (env, PVar {ident = PWildcard name})
end

lang SeqTotPatSym = SeqTotPat
  -- TODO
end

lang SeqEdgPatSym = SeqEdgPat
  -- TODO
end

lang RecordPatSym = RecordPat
  sem symbolizePat (env : Env) =
  | PRecord {bindings = bindings} ->
    mapAccum (lam env. lam _. lam p. symbolizePat env p) env bindings
end

lang DataPatSym = DataPat
  sem symbolizePat (env : Env) =
  | PCon {ident = (str,_), subpat = subpat} ->
    match lookup (IdCon str) env
    with Some sym then
      match symbolizePat env subpat with (env, subpat) then
        (env, PCon {ident = (str, sym), subpat = subpat})
      else never
    else error (concat "Unknown constructor in symbolize: " str)
end

lang IntPatSym = IntPat
  sem symbolizePat (env : Env) =
  | PInt i -> (env, PInt i)
end

lang CharPatSym = CharPat
  sem symbolizePat (env : Env) =
  | PChar c -> (env, PChar c)
end

lang BoolPatSym = BoolPat
  sem symbolizePat (env : Env) =
  | PBool b -> (env, PBool b)
end

lang AndPatSym = AndPat
  -- TODO
end

lang OrPatSym = OrPat
  -- TODO
end

lang NotPatSym = NotPat
  -- TODO
end

------------------------------
-- MEXPR SYMBOLIZE FRAGMENT --
------------------------------

lang MExprSym = MExprPrettyPrint +

  -- Terms
  VarSym + AppSym + FunSym + RecordSym + LetSym + RecLetsSym + ConstSym +
  DataSym + MatchSym + UtestSym + SeqSym + NeverSym

  -- Patterns
  + VarPatSym + SeqTotPatSym + SeqEdgPatSym + RecordPatSym + DataPatSym +
  IntPatSym + CharPatSym + BoolPatSym + AndPatSym + OrPatSym + NotPatSym

-----------
-- TESTS --
-----------
-- It is difficult to directly do unit testing for the above due to the nature
-- of symbols, so we are just checking for crashes or errors below. Unit
-- testing in eval.mc also covers symbolize.

mexpr

use MExprSym in

let debugPrint = lam e. lam es.
  let _ = printLn "--- BEFORE SYMBOLIZE ---" in
  let _ = printLn (pprintCode 0 e) in
  let _ = print "\n" in
  let _ = printLn "--- AFTER SYMBOLIZE ---" in
  let _ = printLn (pprintCode 0 es) in
  let _ = print "\n" in
  ()
in

let expr1 = (ulam_ "x" (ulam_ "y" (app_ (var_ "x") (var_ "y")))) in
let expr1s = symbolize [] expr1 in
let _ = debugPrint expr1 expr1s in

let expr2 = record_ [("k1", expr1), ("k2", expr1), ("k3", expr1)] in
let expr2s = symbolize [] expr2 in
let _ = debugPrint expr2 expr2s in

()

