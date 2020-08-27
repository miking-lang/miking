-- Symbolization of the MExpr ast.

include "name.mc"
include "string.mc"
include "assoc.mc"

include "mexpr/ast.mc"
-- include "mexpr/pprint.mc"

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

let lookupId = assocLookup {eq = identEq}
let insertId = assocInsert {eq = identEq}
let recmapId = assocMap {eq = identEq}
let mapAccumId = assocMapAccum {eq = identEq}

-----------
-- TERMS --
-----------

lang VarSym = VarAst
  sem symbolize (env : Env) =
  | TmVar {ident = (str, _)} ->
    match lookupId (IdVar str) env
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
    let env = insertId (IdVar str) sym env in
    TmLam {ident = (str,sym), tpe = tpe, body = symbolize env body}
end

lang RecordSym = RecordAst
  sem symbolize (env : Env) =
  | TmRecord {bindings = bindings} ->
    TmRecord {bindings = recmapId (symbolize env) bindings}

  | TmRecordUpdate {rec = rec, key = key, value = value} ->
    TmRecordUpdate {rec = symbolize env rec, key = key,
                    value = symbolize env value}
end

lang LetSym = LetAst
  sem symbolize (env : Env) =
  | TmLet {ident = (str, _),  body = body, inexpr = inexpr} ->
    let body = symbolize env body in
    let sym = gensym () in
    let env = insertId (IdVar str) sym env in
    TmLet {ident = (str,sym), body = body, inexpr = symbolize env inexpr}
end

lang RecLetsSym = RecLetsAst
  sem symbolize (env : Env) =
  | TmRecLets {bindings = bindings, inexpr = inexpr} ->

    -- Generate fresh symbols for all identifiers
    let bindings =
      map (lam bind. {bind with ident = nameSetNewSym bind.ident}) bindings in

    -- Add all identifiers to environment
    let env =
      foldl
        (lam env. lam bind.
           insertId (IdVar (nameGetStr bind.ident))
             (match nameGetSym bind.ident with Some sym then sym
              else error "Impossible: symbol missing in RecLetsSym")
             env)
        env bindings in

    -- Symbolize all bodies with the new environment
    let bindings =
      map (lam bind. {bind with body = symbolize env bind.body})
        bindings in

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
    let env = insertId (IdCon str) sym env in
    TmConDef {ident = (str,sym), tpe = tpe, inexpr = symbolize env inexpr}
  | TmConApp {ident = (str,_), body = body} ->
    match lookupId (IdCon str) env
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
    let l = lookupId (IdVar str) env in
    match l with Some sym then
      (env, PVar {ident = PName (str,sym)})
    else match l with None () then
      let sym = gensym () in
      let env = insertId (IdVar str) sym env in
      (env, PVar {ident = PName (str,sym)})
    else never
  | PVar {ident = PWildcard ()} ->
    (env, PVar {ident = PWildcard ()})
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
    match mapAccumId (lam env. lam _. lam p. symbolizePat env p) env bindings
    with (env,bindings) then
      (env, PRecord {bindings = bindings})
    else never
end

lang DataPatSym = DataPat
  sem symbolizePat (env : Env) =
  | PCon {ident = (str,_), subpat = subpat} ->
    match lookupId (IdCon str) env
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

lang MExprSym = -- MExprPrettyPrint +

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
-- of symbols, so we are just evaluating the below for errors. Unit
-- testing in eval.mc also implicitly covers symbolize.

mexpr

use MExprSym in

-- let debugPrint = lam e. lam es.
--   let _ = printLn "--- BEFORE SYMBOLIZE ---" in
--   let _ = printLn (pprintCode 0 e) in
--   let _ = print "\n" in
--   let _ = printLn "--- AFTER SYMBOLIZE ---" in
--   let _ = printLn (pprintCode 0 es) in
--   let _ = print "\n" in
--   ()
-- in

let base = (ulam_ "x" (ulam_ "y" (app_ (var_ "x") (var_ "y")))) in
let sbase = symbolize [] base in
-- let _ = debugPrint base sbase in

let rec = record_ [("k1", base), ("k2", (int_ 1)), ("k3", (int_ 2))] in
let srec = symbolize [] rec in
-- let _ = debugPrint rec srec in

let letin = bind_ (let_ "x" rec) (app_ (var_ "x") base) in
let sletin = symbolize [] letin in
-- let _ = debugPrint letin sletin in

let rlets =
  bind_ (reclets_ [("x", (var_ "y")), ("y", (var_ "x"))])
    (app_ (var_ "x") (var_ "y")) in
let srlets = symbolize [] rlets in
-- let _ = debugPrint rlets srlets in

let const = int_ 1 in
let sconst = symbolize [] const in
-- let _ = debugPrint const sconst in

let data = bind_ (ucondef_ "Test") (conapp_ "Test" base) in
let sdata = symbolize [] data in
-- let _ = debugPrint data sdata in

let varpat = match_ unit_ (pvar_ "x") (var_ "x") base in
let svarpat = symbolize [] varpat in
-- let _ = debugPrint varpat svarpat in

let recpat =
  match_ base
    (prec_ [("k1", (pvar_ "x")), ("k2", pvarw_), ("k3", (pvar_ "x"))])
    (var_ "x") unit_ in
let srecpat = symbolize [] recpat in
-- let _ = debugPrint recpat srecpat in

let datapat =
  bind_ (ucondef_ "Test")
    (match_ unit_ (pcon_ "Test" (pvar_ "x")) (var_ "x") unit_) in
let sdatapat = symbolize [] datapat in
-- let _ = debugPrint datapat sdatapat in

let litpat =
  match_ unit_ (pint_ 1)
    (match_ unit_ (pchar_ 'c')
       (match_ unit_ (ptrue_)
            base
          unit_)
       unit_)
    unit_ in
let slitpat = symbolize [] litpat in
-- let _ = debugPrint litpat slitpat in

let ut = utest_ base base base in
let sut = symbolize [] ut in
-- let _ = debugPrint ut sut in

let seq = seq_ [base, data, const] in
let sseq = seq_ [base, data, const] in
-- let _ = debugPrint seq sseq in

let nev = never_ in
let snever = symbolize [] never_ in
-- let _ = debugPrint nev snever in

()

