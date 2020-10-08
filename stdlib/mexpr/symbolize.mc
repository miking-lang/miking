-- Symbolization of the MExpr ast.
--
-- TODO(dlunde,2020-09-25): Add support for leaving existing symbols intact when
-- running symbolize on an already partially symbolized term?

include "name.mc"
include "string.mc"
include "assoc.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"

---------------------------
-- SYMBOLIZE ENVIRONMENT --
---------------------------
-- NOTE(dlunde,2020-09-25): The environment differs from boot, since we do not
-- have access to the unique string identifiers from ustring.ml. Instead, we
-- use strings directly.

-- TODO(dlunde,2020-09-25): We should probably use separate environments for the
-- below instead (as in eq.mc)
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
    then eqString s1 s2
    else false

type Env = AssocMap Ident Name

let _symLookup = assocLookup {eq = identEq}
let _symInsert = assocInsert {eq = identEq}
let _symRecMap = assocMap {eq = identEq}
let _symMapAccum = assocMapAccum {eq = identEq}
let _symOverwrite = assocMergePreferRight {eq = identEq}

-----------
-- TERMS --
-----------

lang Sym
  sem symbolizeExpr (env : Env) =
  -- Intentionally left blank

  sem symbolize =
  | expr -> symbolizeExpr assocEmpty expr

end

lang VarSym = Sym + VarAst
  sem symbolizeExpr (env : Env) =
  | TmVar {ident = ident} ->
    let str = nameGetStr ident in
    match _symLookup (IdVar str) env
    with Some ident then TmVar {ident = ident}
    else error (concat "Unknown variable in symbolizeExpr: " str)
end

lang AppSym = Sym + AppAst
  sem symbolizeExpr (env : Env) =
  | TmApp {lhs = lhs, rhs = rhs} ->
    TmApp {lhs = symbolizeExpr env lhs, rhs = symbolizeExpr env rhs}
end

lang FunSym = Sym + FunAst + VarSym + AppSym
  sem symbolizeExpr (env : Env) =
  | TmLam {ident = ident, tpe = tpe, body = body} ->
    let ident = nameSetNewSym ident in
    let str = nameGetStr ident in
    let env = _symInsert (IdVar str) ident env in
    TmLam {ident = ident, tpe = tpe, body = symbolizeExpr env body}
end

lang RecordSym = Sym + RecordAst
  sem symbolizeExpr (env : Env) =
  | TmRecord {bindings = bindings} ->
    TmRecord {bindings = _symRecMap (symbolizeExpr env) bindings}

  | TmRecordUpdate {rec = rec, key = key, value = value} ->
    TmRecordUpdate {rec = symbolizeExpr env rec, key = key,
                    value = symbolizeExpr env value}
end

lang LetSym = Sym + LetAst
  sem symbolizeExpr (env : Env) =
  | TmLet {ident = ident,  body = body, inexpr = inexpr} ->
    let ident = nameSetNewSym ident in
    let str = nameGetStr ident in
    let body = symbolizeExpr env body in
    let env = _symInsert (IdVar str) ident env in
    TmLet {ident = ident, body = body, inexpr = symbolizeExpr env inexpr}
end

lang RecLetsSym = Sym + RecLetsAst
  sem symbolizeExpr (env : Env) =
  | TmRecLets {bindings = bindings, inexpr = inexpr} ->

    -- Generate fresh symbols for all identifiers
    let bindings =
      map (lam bind. {bind with ident = nameSetNewSym bind.ident}) bindings in

    -- Add all identifiers to environment
    let env =
      foldl
        (lam env. lam bind.
           _symInsert (IdVar (nameGetStr bind.ident)) bind.ident env)
        env bindings in

    -- Symbolize all bodies with the new environment
    let bindings =
      map (lam bind. {bind with body = symbolizeExpr env bind.body})
        bindings in

    TmRecLets {bindings = bindings, inexpr = symbolizeExpr env inexpr}

end

lang ConstSym = Sym + ConstAst
  sem symbolizeExpr (env : Env) =
  | TmConst t -> TmConst t
end

lang DataSym = Sym + DataAst
  sem symbolizeExpr (env : Env) =
  | TmConDef {ident = ident, tpe = tpe, inexpr = inexpr} ->
    let str = nameGetStr ident in
    let ident = nameSetNewSym ident in
    let env = _symInsert (IdCon str) ident env in
    TmConDef {ident = ident, tpe = tpe, inexpr = symbolizeExpr env inexpr}
  | TmConApp {ident = ident, body = body} ->
    let str = nameGetStr ident in
    match _symLookup (IdCon str) env
    with Some ident then
      TmConApp {ident = ident, body = symbolizeExpr env body}
    else error (concat "Unknown constructor in symbolizeExpr: " str)
end

lang MatchSym = Sym + MatchAst
  -- TODO(vipa, 2020-09-23): env is constant throughout symbolizePat,
  -- so it would be preferrable to pass it in some other way, a reader
  -- monad or something. patEnv on the other hand changes, it would be
  -- nice to pass via state monad or something.  env is the
  -- environment from the outside, plus the names added thus far in
  -- the pattern patEnv is only the newly added names
  sem symbolizePat (env : Env) (patEnv : Env) =
  -- Intentionally left blank

  sem symbolizeExpr (env : Env) =
  | TmMatch {target = target, pat = pat, thn = thn, els = els} ->
    match symbolizePat env assocEmpty pat
    with (thnPatEnv, pat) then
      TmMatch {target = symbolizeExpr env target,
               pat = pat, thn = symbolizeExpr (_symOverwrite env thnPatEnv) thn, els = symbolizeExpr env els}
    else never
end

lang UtestSym = Sym + UtestAst
  sem symbolizeExpr (env : Env) =
  | TmUtest {test = test, expected = expected, next = next} ->
    TmUtest {test = symbolizeExpr env test,
             expected = symbolizeExpr env expected,
             next = symbolizeExpr env next}
end

lang SeqSym = Sym + SeqAst
  sem symbolizeExpr (env : Env) =
  | TmSeq {tms = tms} -> TmSeq {tms = map (symbolizeExpr env) tms}
end

lang NeverSym = Sym + NeverAst
  sem symbolizeExpr (env : Env) =
  | TmNever {} -> TmNever {}
end

--------------
-- PATTERNS --
--------------

let _symbolize_patname: Env ->  (Env, PatName) = lam patEnv. lam pname.
  match pname with PName name then
    let str = nameGetStr name in
    let res = _symLookup (IdVar str) patEnv in
    match res with Some name then
      (patEnv, PName name)
    else match res with None () then
      let name = nameSetNewSym name in
      let patEnv = _symInsert (IdVar str) name patEnv in
      (patEnv, PName name)
    else never
  else match pname with PWildcard () then
    (patEnv, PWildcard ())
  else never

lang VarPatSym = VarPat
  sem symbolizePat (env : Env) (patEnv : Env) =
  | PVar p ->
    match _symbolize_patname patEnv p.ident with (patEnv, patname) then
      (patEnv, PVar {p with ident = patname})
    else never
end

lang SeqTotPatSym = SeqTotPat
  sem symbolizePat (env : Env) (patEnv : Env) =
  | PSeqTot p ->
    let res = mapAccumL (symbolizePat env) patEnv p.pats in
    (res.0, PSeqTot {p with pats = res.1})
end

lang SeqEdgePatSym = SeqEdgePat
  sem symbolizePat (env : Env) (patEnv : Env) =
  | PSeqEdge p ->
    let preRes = mapAccumL (symbolizePat env) patEnv p.prefix in
    let midRes = _symbolize_patname preRes.0 p.middle in
    let postRes = mapAccumL (symbolizePat env) midRes.0 p.postfix in
    (postRes.0, PSeqEdge
      {{{p with prefix = preRes.1} with middle = midRes.1} with postfix = postRes.1})
end

lang RecordPatSym = RecordPat
  sem symbolizePat (env : Env) (patEnv : Env) =
  | PRecord {bindings = bindings} ->
    match _symMapAccum (lam patEnv. lam _. lam p. symbolizePat env patEnv p) env bindings
    with (env,bindings) then
      (env, PRecord {bindings = bindings})
    else never
end

lang DataPatSym = DataPat
  sem symbolizePat (env : Env) (patEnv : Env) =
  | PCon {ident = ident, subpat = subpat} ->
    let str = nameGetStr ident in
    match _symLookup (IdCon str) env
    with Some ident then
      match symbolizePat env patEnv subpat with (patEnv, subpat) then
        (patEnv, PCon {ident = ident, subpat = subpat})
      else never
    else error (concat "Unknown constructor in symbolizeExpr: " str)
end

lang IntPatSym = IntPat
  sem symbolizePat (env : Env) (patEnv : Env) =
  | PInt i -> (patEnv, PInt i)
end

lang CharPatSym = CharPat
  sem symbolizePat (env : Env) (patEnv : Env) =
  | PChar c -> (patEnv, PChar c)
end

lang BoolPatSym = BoolPat
  sem symbolizePat (env : Env) (patEnv : Env) =
  | PBool b -> (patEnv, PBool b)
end

lang AndPatSym = AndPat
  sem symbolizePat (env : Env) (patEnv : Env) =
  | PAnd p ->
    let lRes = symbolizePat env patEnv p.lpat in
    let rRes = symbolizePat env lRes.0 p.rpat in
    (rRes.0, PAnd {{p with lpat = lRes.1} with rpat = rRes.1})
end

lang OrPatSym = OrPat
  sem symbolizePat (env : Env) (patEnv : Env) =
  | POr p ->
    let lRes = symbolizePat env patEnv p.lpat in
    let rRes = symbolizePat env lRes.0 p.rpat in
    (rRes.0, POr {{p with lpat = lRes.1} with rpat = rRes.1})
end

lang NotPatSym = NotPat
  sem symbolizePat (env : Env) (patEnv : Env) =
  | PNot p ->
    -- NOTE(vipa, 2020-09-23): new names in a not-pattern do not
    -- matter since they will never bind (it should probably be an
    -- error to bind a name inside a not-pattern, but we're not doing
    -- that kind of static checks yet.  Note that we still need to run
    -- symbolizeExpr though, constructors must refer to the right symbol.
    let res = symbolizePat env patEnv p.subpat in
    (patEnv, PNot {p with subpat = res.1})
end

------------------------------
-- MEXPR SYMBOLIZE FRAGMENT --
------------------------------

lang MExprSym =

  -- Terms
  VarSym + AppSym + FunSym + RecordSym + LetSym + RecLetsSym + ConstSym +
  DataSym + MatchSym + UtestSym + SeqSym + NeverSym

  -- Patterns
  + VarPatSym + SeqTotPatSym + SeqEdgePatSym + RecordPatSym + DataPatSym +
  IntPatSym + CharPatSym + BoolPatSym + AndPatSym + OrPatSym + NotPatSym

-----------
-- TESTS --
-----------
-- It is difficult to directly do unit testing for the above due to the nature
-- of symbols, so we are just evaluating the below for errors. Unit
-- testing in eval.mc also implicitly covers symbolizeExpr.

lang TestLang = MExprSym + MExprPrettyPrint

mexpr

use TestLang in

let base = (ulam_ "x" (ulam_ "y" (app_ (var_ "x") (var_ "y")))) in

let rec = record_ [("k1", base), ("k2", (int_ 1)), ("k3", (int_ 2))] in

let letin = bind_ (let_ "x" rec) (app_ (var_ "x") base) in

let rlets =
  bind_ (reclets_ [("x", (var_ "y")), ("y", (var_ "x"))])
    (app_ (var_ "x") (var_ "y")) in

let const = int_ 1 in

let data = bind_ (ucondef_ "Test") (conapp_ "Test" base) in

let varpat = match_ unit_ (pvar_ "x") (var_ "x") base in

let recpat =
  match_ base
    (prec_ [("k1", (pvar_ "x")), ("k2", pvarw_), ("k3", (pvar_ "x"))])
    (var_ "x") unit_ in

let datapat =
  bind_ (ucondef_ "Test")
    (match_ unit_ (pcon_ "Test" (pvar_ "x")) (var_ "x") unit_) in

let litpat =
  match_ unit_ (pint_ 1)
    (match_ unit_ (pchar_ 'c')
       (match_ unit_ (ptrue_)
            base
          unit_)
       unit_)
    unit_ in

let ut = utest_ base base base in

let seq = seq_ [base, data, const] in

let nev = never_ in

let matchand = bind_ (let_ "a" (int_ 2)) (match_ (int_ 1) (pand_ (pint_ 1) (pvar_ "a")) (var_ "a") (never_)) in

let matchor = bind_ (let_ "a" (int_ 2)) (match_ (int_ 1) (por_ (pvar_ "a") (pvar_ "a")) (var_ "a") (never_)) in

-- NOTE(vipa, 2020-09-23): (var_ "a") should refer to the "a" from let_, not the pattern, that's intended, in case someone happens to notice and finds it odd
let matchnot = bind_ (let_ "a" (int_ 2)) (match_ (int_ 1) (pnot_ (pvar_ "a")) (var_ "a") (never_)) in

let matchoredge = bind_ (let_ "a" (int_ 2)) (match_ (int_ 1) (por_ (pseqedge_ [pchar_ 'a'] "a" []) (pseqedge_ [pchar_ 'b'] "a" [])) (var_ "a") (never_)) in

let debug = false in

let debugPrint = lam t.
  let r = symbolize t in
  if debug then
    let _ = printLn "--- BEFORE SYMBOLIZE ---" in
    let _ = printLn (expr2str t) in
    let _ = print "\n" in
    let _ = printLn "--- AFTER SYMBOLIZE ---" in
    let _ = printLn (expr2str r) in
    let _ = print "\n" in
    ()
  else ()
in

let _ =
  map debugPrint [
    base,
    rec,
    letin,
    rlets,
    const,
    data,
    varpat,
    recpat,
    datapat,
    litpat,
    ut,
    seq,
    nev,
    matchand,
    matchor,
    matchnot,
    matchoredge
  ]
in

()
