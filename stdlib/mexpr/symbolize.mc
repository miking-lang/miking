-- Symbolization of the MExpr ast.

include "name.mc"
include "string.mc"
include "assoc.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"

---------------------------
-- SYMBOLIZE ENVIRONMENT --
---------------------------
-- NOTE The environment differs from boot, since we do not have access to the
-- unique string identifiers from ustring.ml. Instead, we use strings directly.

-- NOTE We should probably use separate environments for the below instead (as
-- in eq.mc)
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

type Env = AssocMap Ident Name -- i.e., [(Ident, Symbol)]

let _symLookup = assocLookup {eq = identEq}
let _symInsert = assocInsert {eq = identEq}
let _symRecMap = assocMap {eq = identEq}
let _symMapAccum = assocMapAccum {eq = identEq}
let _symOverwrite = assocMergePreferRight {eq = identEq}

-----------
-- TERMS --
-----------

lang VarSym = VarAst
  sem symbolize (env : Env) =
  | TmVar {ident = ident} ->
    let str = nameGetStr ident in
    match _symLookup (IdVar str) env
    with Some ident then TmVar {ident = ident}
    else error (concat "Unknown variable in symbolize: " str)
end

lang AppSym = AppAst
  sem symbolize (env : Env) =
  | TmApp {lhs = lhs, rhs = rhs} ->
    TmApp {lhs = symbolize env lhs, rhs = symbolize env rhs}
end

lang FunSym = FunAst + VarSym + AppSym
  sem symbolize (env : Env) =
  | TmLam {ident = ident, tpe = tpe, body = body} ->
    let ident = nameSetNewSym ident in
    let str = nameGetStr ident in
    let env = _symInsert (IdVar str) ident env in
    TmLam {ident = ident, tpe = tpe, body = symbolize env body}
end

lang RecordSym = RecordAst
  sem symbolize (env : Env) =
  | TmRecord {bindings = bindings} ->
    TmRecord {bindings = _symRecMap (symbolize env) bindings}

  | TmRecordUpdate {rec = rec, key = key, value = value} ->
    TmRecordUpdate {rec = symbolize env rec, key = key,
                    value = symbolize env value}
end

lang LetSym = LetAst
  sem symbolize (env : Env) =
  | TmLet {ident = ident,  body = body, inexpr = inexpr} ->
    let ident = nameSetNewSym ident in
    let str = nameGetStr ident in
    let body = symbolize env body in
    let env = _symInsert (IdVar str) ident env in
    TmLet {ident = ident, body = body, inexpr = symbolize env inexpr}
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
           _symInsert (IdVar (nameGetStr bind.ident)) bind.ident env)
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
  | TmConDef {ident = ident, tpe = tpe, inexpr = inexpr} ->
    let str = nameGetStr ident in
    let ident = nameSetNewSym ident in
    let env = _symInsert (IdCon str) ident env in
    TmConDef {ident = ident, tpe = tpe, inexpr = symbolize env inexpr}
  | TmConApp {ident = ident, body = body} ->
    let str = nameGetStr ident in
    match _symLookup (IdCon str) env
    with Some ident then
      TmConApp {ident = ident, body = symbolize env body}
    else error (concat "Unknown constructor in symbolize: " str)
end

lang MatchSym = MatchAst
  -- TODO(vipa, 2020-09-23): env is constant throughout symbolizePat,
  -- so it would be preferrable to pass it in some other way, a reader
  -- monad or something. patEnv on the other hand changes, it would be
  -- nice to pass via state monad or something.  env is the
  -- environment from the outside, plus the names added thus far in
  -- the pattern patEnv is only the newly added names
  sem symbolizePat (env : Env) (patEnv : Env) =
  -- Intentionally left blank

  sem symbolize (env : Env) =
  | TmMatch {target = target, pat = pat, thn = thn, els = els} ->
    match symbolizePat env assocEmpty pat
    with (thnPatEnv, pat) then
      TmMatch {target = symbolize env target,
               pat = pat, thn = symbolize (_symOverwrite env thnPatEnv) thn, els = symbolize env els}
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
    else error (concat "Unknown constructor in symbolize: " str)
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
    -- symbolize though, constructors must refer to the right symbol.
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

  -- Debugging
  + MExprPrettyPrint

-----------
-- TESTS --
-----------
-- It is difficult to directly do unit testing for the above due to the nature
-- of symbols, so we are just evaluating the below for errors. Unit
-- testing in eval.mc also implicitly covers symbolize.

mexpr

use MExprSym in

let debug = false in

let debugPrint = lam e. lam es.
  if debug then
    let _ = printLn "--- BEFORE SYMBOLIZE ---" in
    let _ = printLn (expr2str e) in
    let _ = print "\n" in
    let _ = printLn "--- AFTER SYMBOLIZE ---" in
    let _ = printLn (expr2str es) in
    let _ = print "\n" in
    ()
  else ()
in

let ae = assocEmpty in

let base = (ulam_ "x" (ulam_ "y" (app_ (var_ "x") (var_ "y")))) in
let sbase = symbolize ae base in
let _ = debugPrint base sbase in

let rec = record_ [("k1", base), ("k2", (int_ 1)), ("k3", (int_ 2))] in
let srec = symbolize ae rec in
let _ = debugPrint rec srec in

let letin = bind_ (let_ "x" rec) (app_ (var_ "x") base) in
let sletin = symbolize ae letin in
let _ = debugPrint letin sletin in

let rlets =
  bind_ (reclets_ [("x", (var_ "y")), ("y", (var_ "x"))])
    (app_ (var_ "x") (var_ "y")) in
let srlets = symbolize ae rlets in
let _ = debugPrint rlets srlets in

let const = int_ 1 in
let sconst = symbolize ae const in
let _ = debugPrint const sconst in

let data = bind_ (ucondef_ "Test") (conapp_ "Test" base) in
let sdata = symbolize ae data in
let _ = debugPrint data sdata in

let varpat = match_ unit_ (pvar_ "x") (var_ "x") base in
let svarpat = symbolize ae varpat in
let _ = debugPrint varpat svarpat in

let recpat =
  match_ base
    (prec_ [("k1", (pvar_ "x")), ("k2", pvarw_), ("k3", (pvar_ "x"))])
    (var_ "x") unit_ in
let srecpat = symbolize ae recpat in
let _ = debugPrint recpat srecpat in

let datapat =
  bind_ (ucondef_ "Test")
    (match_ unit_ (pcon_ "Test" (pvar_ "x")) (var_ "x") unit_) in
let sdatapat = symbolize ae datapat in
let _ = debugPrint datapat sdatapat in

let litpat =
  match_ unit_ (pint_ 1)
    (match_ unit_ (pchar_ 'c')
       (match_ unit_ (ptrue_)
            base
          unit_)
       unit_)
    unit_ in
let slitpat = symbolize ae litpat in
let _ = debugPrint litpat slitpat in

let ut = utest_ base base base in
let sut = symbolize ae ut in
let _ = debugPrint ut sut in

let seq = seq_ [base, data, const] in
let sseq = symbolize ae seq in
let _ = debugPrint seq sseq in

let nev = never_ in
let snever = symbolize ae never_ in
let _ = debugPrint nev snever in

let matchand = bind_ (let_ "a" (int_ 2)) (match_ (int_ 1) (pand_ (pint_ 1) (pvar_ "a")) (var_ "a") (never_)) in
let smatchand = symbolize ae matchand in
let _ = debugPrint matchand smatchand in

let matchor = bind_ (let_ "a" (int_ 2)) (match_ (int_ 1) (por_ (pvar_ "a") (pvar_ "a")) (var_ "a") (never_)) in
let smatchor = symbolize ae matchor in
let _ = debugPrint matchor smatchor in

-- NOTE(vipa, 2020-09-23): (var_ "a") should refer to the "a" from let_, not the pattern, that's intended, in case someone happens to notice and finds it odd
let matchnot = bind_ (let_ "a" (int_ 2)) (match_ (int_ 1) (pnot_ (pvar_ "a")) (var_ "a") (never_)) in
let smatchnot = symbolize ae matchnot in
let _ = debugPrint matchnot smatchnot in

let matchoredge = bind_ (let_ "a" (int_ 2)) (match_ (int_ 1) (por_ (pseqedge_ [pchar_ 'a'] "a" []) (pseqedge_ [pchar_ 'b'] "a" [])) (var_ "a") (never_)) in
let smatchoredge = symbolize ae matchoredge in
let _ = debugPrint matchoredge smatchoredge in

()
