
include "char.mc"
include "option.mc"
include "seq.mc"
include "string.mc"
include "name.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

----------------------------
-- PRETTY PRINT INDENTING --
----------------------------

-- Indentation consisting of [indent] spaces
let pprintSpacing = lam indent. makeSeq indent ' '

-- Newline followed by [indent] spaces
let pprintNewline = lam indent. concat "\n" (pprintSpacing indent)

-- Increment [indent] by 2
let pprintIncr = lam indent. addi indent 2

---------------------------------
-- PRETTY PRINTING ENVIRONMENT --
---------------------------------

type PprintEnv = {

  -- Used to keep track of strings assigned to names
  nameMap: AssocMap Name String,

  -- Count the number of occurrences of each (base) string to assist with
  -- assigning unique strings.
  count: AssocMap String Int

}

-- TODO(dlunde,2020-09-29) Make it possible to debug the actual symbols

let pprintEnvEmpty = {nameMap = assocEmpty, count = assocEmpty}

-- Look up the string associated with a name in the environment
let pprintEnvLookup : Name -> PprintEnv -> Option String = lam name. lam env.
  match env with { nameMap = nameMap } then
    assocLookup {eq = nameEq} name nameMap
  else never

-- Check if a string is free in the environment.
let pprintEnvFree : String -> PprintEnv -> Bool = lam str. lam env.
  match env with { nameMap = nameMap } then
    let f = lam _. lam v. eqString str v in
    not (assocAny f nameMap)
  else never

-- Add a binding to the environment
let pprintEnvAdd : Name -> String -> Int -> PprintEnv -> PprintEnv =
  lam name. lam str. lam i. lam env.
    match env with {nameMap = nameMap, count = count} then
      let baseStr = nameGetStr name in
      let count = assocInsert {eq = eqString} baseStr i count in
      let nameMap = assocInsert {eq = nameEq} name str nameMap in
      {nameMap = nameMap, count = count}
    else never

-- Get a string for the current name. Returns both the string and a new
-- environment.
let pprintEnvGetStr : Name -> PprintEnv -> (PprintEnv, String) = lam name. lam env.
  match pprintEnvLookup name env with Some str then (env,str)
  else
    let baseStr = nameGetStr name in
    if pprintEnvFree baseStr env then (pprintEnvAdd name baseStr 1 env, baseStr)
    else
      match env with {count = count} then
        let start =
          match assocLookup {eq = eqString} baseStr count
          with Some i then i else 1 in
        recursive let findFree : String -> Int -> (String, Int) =
          lam baseStr. lam i.
            let proposal = concat baseStr (int2string i) in
            if pprintEnvFree proposal env then (proposal, i)
            else findFree baseStr (addi i 1)
        in
        match findFree baseStr start with (str, i) then
          (pprintEnvAdd name str (addi i 1) env, str)
        else never
      else never

----------------------
-- HELPER FUNCTIONS --
----------------------

-- Ensure string can be parsed
let parserStr = lam str. lam prefix. lam cond.
  if eqi (length str) 0 then concat prefix "\"\""
  else if cond str then str
  else join [prefix, "\"", str, "\""]

-- Constructor string parser translation
let conString = lam str.
  parserStr str "#con" (lam str. isUpperAlpha (head str))

-- Variable string parser translation
let varString = lam str.
  parserStr str "#var" (lam str. isLowerAlpha (head str))

-- Label string parser translation for records
let labelString = lam str.
  parserStr str "#label" (lam str. isLowerAlpha (head str))

-- Get an optional list of tuple expressions for a record. If the record does
-- not represent a tuple, None () is returned.
let _record2tuple = lam tm.
  use RecordAst in
  match tm with TmRecord t then
    let keys = assocKeys {eq=eqString} t.bindings in
    match all stringIsInt keys with false then None () else
    let intKeys = map string2int keys in
    let sortedKeys = sort subi intKeys in
    -- Check if keys are a sequence 0..(n-1)
    match and (eqi 0 (head sortedKeys))
              (eqi (subi (length intKeys) 1) (last sortedKeys)) with true then
      -- Note: Quadratic complexity. Sorting the association list directly
      -- w.r.t. key would improve complexity to n*log(n).
      Some (map (lam key. assocLookupOrElse {eq=eqString}
                            (lam _. error "Key not found")
                            (int2string key) t.bindings)
                 sortedKeys)
    else None ()
  else error "Not a record"


-----------
-- TERMS --
-----------

lang PrettyPrint
  sem isAtomic =
  -- Intentionally left blank

  sem pprintCode (indent : Int) (env: PprintEnv) =
  -- Intentionally left blank

  sem expr2str =
  | expr -> match pprintCode 0 pprintEnvEmpty expr with (_,str)
            then str else never

  -- Helper function for printing parentheses
  sem printParen (indent : Int) (env: PprintEnv) =
  | expr ->
    let i = if isAtomic expr then indent else addi 1 indent in
    match pprintCode i env expr with (env,str) then
      if isAtomic expr then (env,str)
      else (env,join ["(", str, ")"])
    else never

  -- Helper function for printing a list of arguments
  sem printArgs (indent : Int) (env : PprintEnv) =
  | exprs ->
    match mapAccumL (printParen indent) env exprs with (env,args) then
      (env, strJoin (pprintNewline indent) args)
    else never

end

lang VarPrettyPrint = PrettyPrint + VarAst
  sem isAtomic =
  | TmVar _ -> true

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmVar {ident = ident} ->
    match pprintEnvGetStr ident env with (env,str)
    then (env,varString str) else never
end

lang AppPrettyPrint = PrettyPrint + AppAst
  sem isAtomic =
  | TmApp _ -> false

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmApp t ->
    recursive let appseq =
      lam t. match t with TmApp {lhs = lhs, rhs = rhs} then
        snoc (appseq lhs) rhs
      else [t]
    in
    let apps = appseq (TmApp t) in

    match printParen indent env (head apps) with (env,fun) then
      let aindent = pprintIncr indent in
      match printArgs aindent env (tail apps) with (env,args) then
        (env, join [fun, pprintNewline aindent, args])
      else never
    else error "Impossible"
end

lang FunPrettyPrint = PrettyPrint + FunAst
  sem isAtomic =
  | TmLam _ -> false

  sem getTypeStringCode (indent : Int) =
  -- Intentionally left blank

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmLam t ->
    match pprintEnvGetStr t.ident env with (env,str) then
      let ident = varString str in
      let tpe =
        match t.tpe with Some t1 then
          concat " : " (getTypeStringCode indent t1)
        else ""
      in
      match pprintCode (pprintIncr indent) env t.body with (env,body) then
        (env,
         join ["lam ", ident, tpe, ".", pprintNewline (pprintIncr indent),
               body])
      else never
    else never
end

lang RecordPrettyPrint = PrettyPrint + RecordAst
  sem isAtomic =
  | TmRecord _ -> true
  | TmRecordUpdate _ -> true

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmRecord t ->
    if eqi (length t.bindings) 0 then (env,"{}")
    else match _record2tuple (TmRecord t) with Some tms then
      match mapAccumL (lam env. lam e. pprintCode indent env e) env tms
      with (env,tupleExprs) then
        let merged = match tupleExprs with [e] then
                       concat e ","
                     else strJoin ", " tupleExprs in
        (env, join ["(", merged, ")"])
      else never
    else
      let innerIndent = pprintIncr (pprintIncr indent) in
      match
        assocMapAccum {eq=eqString}
          (lam env. lam k. lam v.
             match pprintCode innerIndent env v with (env, str) then
               (env, join [labelString k, " =", pprintNewline innerIndent, str])
             else never)
           env t.bindings
      with (env, bindMap) then
        let binds = assocValues {eq=eqString} bindMap in
        let merged =
          strJoin (concat "," (pprintNewline (pprintIncr indent))) binds
        in
        (env,join ["{ ", merged, " }"])
      else never

  | TmRecordUpdate t ->
    let i = pprintIncr indent in
    let ii = pprintIncr i in
    match pprintCode i env t.rec with (env,rec) then
      match pprintCode ii env t.value with (env,value) then
        (env,join ["{ ", rec, pprintNewline i,
                   "with", pprintNewline i,
                   labelString t.key, " =", pprintNewline ii, value, " }"])
      else never
    else never
end

lang LetPrettyPrint = PrettyPrint + LetAst
  sem isAtomic =
  | TmLet _ -> false

  sem getTypeStringCode (indent : Int) =
  -- Intentionally left blank

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmLet t ->
    match pprintEnvGetStr t.ident env with (env,str) then
      let ident = varString str in
      match pprintCode (pprintIncr indent) env t.body with (env,body) then
        match pprintCode indent env t.inexpr with (env,inexpr) then
          (env, join ["let ", ident, " =", pprintNewline (pprintIncr indent),
                      body, pprintNewline indent,
                      "in", pprintNewline indent,
                      inexpr])
        else never
      else never
    else never
end

lang RecLetsPrettyPrint = PrettyPrint + RecLetsAst
  sem isAtomic =
  | TmRecLets _ -> false

  sem getTypeStringCode (indent : Int) =
  -- Intentionally left blank

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmRecLets t ->
    let lname = lam env. lam bind.
      match pprintEnvGetStr bind.ident env with (env,str) then
        (env,varString str)
      else never in
    let lbody = lam env. lam bind.
      match pprintCode (pprintIncr (pprintIncr indent)) env bind.body
      with (env,str) then (env,str)
      else never in
    match mapAccumL lname env t.bindings with (env,idents) then
      match mapAccumL lbody env t.bindings with (env,bodies) then
        match pprintCode indent env t.inexpr with (env,inexpr) then
          let fzip = lam ident. lam body.
            join [pprintNewline (pprintIncr indent),
                  "let ", ident, " =",
                  pprintNewline (pprintIncr (pprintIncr indent)), body]
          in
          (env,join ["recursive", join (zipWith fzip idents bodies),
                 pprintNewline indent, "in", pprintNewline indent, inexpr])
        else never
      else never
    else never
end

lang ConstPrettyPrint = PrettyPrint + ConstAst
  sem isAtomic =
  | TmConst _ -> true

  sem getConstStringCode (indent : Int) =
  -- intentionally left blank

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmConst t -> (env,getConstStringCode indent t.val)
end

lang DataPrettyPrint = PrettyPrint + DataAst
  sem isAtomic =
  | TmConDef _ -> false
  | TmConApp _ -> false

  sem getTypeStringCode (indent : Int) =
  -- Intentionally left blank

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmConDef t ->
    match pprintEnvGetStr t.ident env with (env,str) then
      let str = conString str in
      let tpe =
        match t.tpe with Some t1 then
          concat " : " (getTypeStringCode indent t1)
        else ""
      in
      match pprintCode indent env t.inexpr with (env,inexpr) then
        (env,join ["con ", str, tpe, " in", pprintNewline indent, inexpr])
      else never
    else never

  | TmConApp t ->
    match pprintEnvGetStr t.ident env with (env,str) then
      let l = conString str in
      match printParen (pprintIncr indent) env t.body with (env,body) then
        (env, join [l, pprintNewline (pprintIncr indent), body])
      else never
    else never
end

lang MatchPrettyPrint = PrettyPrint + MatchAst
  sem isAtomic =
  | TmMatch _ -> false

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  -- intentionally left blank

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmMatch t ->
    let i = indent in
    let ii = pprintIncr indent in
    match pprintCode ii env t.target with (env,target) then
      match getPatStringCode ii env t.pat with (env,pat) then
        match pprintCode ii env t.thn with (env,thn) then
          match pprintCode ii env t.els with (env,els) then
            (env,join ["match", pprintNewline ii, target, pprintNewline i,
                       "with", pprintNewline ii, pat, pprintNewline i,
                       "then", pprintNewline ii, thn, pprintNewline i,
                       "else", pprintNewline ii, els])
          else never
        else never
      else never
    else never
end

lang UtestPrettyPrint = PrettyPrint + UtestAst
  sem isAtomic =
  | TmUtest _ -> false

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmUtest t ->
    match pprintCode indent env t.test with (env,test) then
      match pprintCode indent env t.expected with (env,expected) then
        match pprintCode indent env t.next with (env,next) then
          (env,join ["utest ", test, pprintNewline indent,
                 "with ", expected, pprintNewline indent,
                 "in", pprintNewline indent, next])
        else never
      else never
    else never
end

lang SeqPrettyPrint = PrettyPrint + SeqAst + ConstPrettyPrint + CharAst
  sem isAtomic =
  | TmSeq _ -> true

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmSeq t ->
    let extract_char = lam e.
      match e with TmConst t1 then
        match t1.val with CChar c then
          Some (c.val)
        else None ()
      else None ()
    in
    let is_char =
        lam e. match extract_char e with Some c then true else false
    in
    if all is_char t.tms then
      (env,concat "\""
        (concat
           (map (lam e. match extract_char e with Some c then c else '?') t.tms)  -- TODO(vipa, 2020-09-23): escape characters
           "\""))
    else
    match mapAccumL (lam env. lam tm. pprintCode (pprintIncr indent) env tm)
                    env t.tms
    with (env,tms) then
      let merged =
        strJoin (concat "," (pprintNewline (pprintIncr indent))) tms
      in
      (env,join ["[ ", merged, " ]"])
    else never
end

lang NeverPrettyPrint = PrettyPrint + NeverAst
  sem isAtomic =
  | TmNever _ -> true

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmNever {} -> (env,"never")
end

---------------
-- CONSTANTS --
---------------
-- All constants in boot have not been implemented. Missing ones can be added
-- as needed.

lang IntPrettyPrint = IntAst + IntPat + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CInt t -> int2string t.val
end

lang ArithIntPrettyPrint = ArithIntAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CAddi _ -> "addi"
  | CSubi _ -> "subi"
  | CMuli _ -> "muli"
end

lang FloatPrettyPrint = FloatAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CFloat t -> float2string t.val
end

lang ArithFloatPrettyPrint = ArithFloatAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CAddf _ -> "addf"
  | CSubf _ -> "subf"
  | CMulf _ -> "mulf"
  | CDivf _ -> "divf"
  | CNegf _ -> "negf"
end

lang BoolPrettyPrint = BoolAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CBool b -> if b.val then "true" else "false"
  | CNot _ -> "not"
end

lang CmpIntPrettyPrint = CmpIntAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CEqi _ -> "eqi"
  | CLti _ -> "lti"
end

lang CmpFloatPrettyPrint = CmpFloatAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CEqf _ -> "eqf"
  | CLtf _ -> "ltf"
end

lang CharPrettyPrint = CharAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CChar c -> ['\'', c.val, '\'']
end

lang SymbPrettyPrint = SymbAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CSymb _ -> "sym"
end

lang CmpSymbPrettyPrint = CmpSymbAst + ConstPrettyPrint
   sem getConstStringCode (indent : Int) =
   | CEqsym _ -> "eqsym"
end

lang SeqOpPrettyPrint = SeqOpAst + ConstPrettyPrint + CharAst
  sem getConstStringCode (indent : Int) =
  | CGet _ -> "get"
  | CCons _ -> "cons"
  | CSnoc _ -> "snoc"
  | CConcat _ -> "concat"
  | CLength _ -> "length"
  | CHead _ -> "head"
  | CTail _ -> "tail"
  | CNull _ -> "null"
  | CReverse _ -> "reverse"
end

--------------
-- PATTERNS --
--------------

let _pprint_patname: PprintEnv -> PatName -> (PprintEnv, String) =
lam env. lam pname.
  match pname with PName name then
    match pprintEnvGetStr name env with (env, str)
    then (env, varString str) else never
  else match pname with PWildcard () then
    (env, "_")
  else never

lang VarPatPrettyPrint = VarPat
  sem patIsAtomic =
  | PVar _ -> true

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PVar {ident = patname} -> _pprint_patname env patname
end

let _pprint_patseq: (Int -> PprintEnv -> Pat -> (PprintEnv, String)) -> Int ->
                    PprintEnv -> [Pat] -> (PprintEnv, String) =
lam recur. lam indent. lam env. lam pats.
  use CharPat in
  let extract_char = lam e.
    match e with PChar c then Some c.val
    else None () in
  match optionMapM extract_char pats with Some str then
    (env, join ["\"", str, "\""])
  else match mapAccumL (recur (pprintIncr indent)) env pats
  with (env, pats) then
    let merged =
      strJoin (concat "," (pprintNewline (pprintIncr indent))) pats in
    (env, join ["[ ", merged, " ]"])
  else never

lang SeqTotPatPrettyPrint = SeqTotPat + CharPat
  sem patIsAtomic =
  | PSeqTot _ -> true

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | PSeqTot {pats = pats} -> _pprint_patseq getPatStringCode indent env pats
end

lang SeqEdgePatPrettyPrint = SeqEdgePat
  sem patIsAtomic =
  | PSeqEdge _ -> false

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | PSeqEdge {prefix = pre, middle = patname, postfix = post} ->
    match _pprint_patseq getPatStringCode indent env pre with (env, pre) then
    match _pprint_patname env patname with (env, pname) then
    match _pprint_patseq getPatStringCode indent env post with (env, post) then
      (env, join [pre, " ++ ", pname, " ++ ", post])
    else never else never else never
end

lang RecordPatPrettyPrint = RecordPat
  sem patIsAtomic =
  | PRecord _ -> true

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PRecord {bindings = bindings} ->
    match
      assocMapAccum {eq=eqString}
        (lam env. lam k. lam v.
           match getPatStringCode indent env v with (env,str) then
             (env,join [labelString k, " = ", str])
           else never)
         env bindings
    with (env,bindMap) then
      (env,join ["{", strJoin ", " (assocValues {eq=eqString} bindMap), "}"])
    else never
end

lang DataPatPrettyPrint = DataPat
  sem patIsAtomic =
  | PCon _ -> false

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PCon t ->
    match pprintEnvGetStr t.ident env with (env,str) then
      let name = conString str in
      match getPatStringCode indent env t.subpat with (env,subpat) then
        let subpat = if patIsAtomic t.subpat then subpat
                     else join ["(", subpat, ")"]
        in (env, join [name, " ", subpat])
      else never
    else never
end

lang IntPatPrettyPrint = IntPat
  sem patIsAtomic =
  | PInt _ -> true

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PInt t -> (env, int2string t.val)
end

lang CharPatPrettyPrint = CharPat
  sem patIsAtomic =
  | PChar _ -> true

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PChar t -> (env, ['\'', t.val, '\''])  -- TODO(vipa, 2020-09-23): should escape t.val probably?
end

lang BoolPatPrettyPrint = BoolPat
  sem patIsAtomic =
  | PBool _ -> true

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PBool b -> (env, if b.val then "true" else "false")
end

lang AndPatPrettyPrint = AndPat
  sem patIsAtomic =
  | PAnd _ -> false

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | PAnd {lpat = l, rpat = r} ->
    match getPatStringCode indent env l with (env, l2) then
    match getPatStringCode indent env r with (env, r2) then
    let l2 = if patIsAtomic l then l2 else join ["(", l2, ")"] in
    let r2 = if patIsAtomic r then r2 else join ["(", r2, ")"] in
    (env, join [l2, " & ", r2])
    else never else never
end

lang OrPatPrettyPrint = OrPat
  sem patIsAtomic =
  | POr _ -> false

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | POr {lpat = l, rpat = r} ->
    match getPatStringCode indent env l with (env, l2) then
    match getPatStringCode indent env r with (env, r2) then
    let l2 = if patIsAtomic l then l2 else join ["(", l2, ")"] in
    let r2 = if patIsAtomic r then r2 else join ["(", r2, ")"] in
    (env, join [l2, " | ", r2])
    else never else never
end

lang NotPatPrettyPrint = NotPat
  sem patIsAtomic =
  | PNot _ -> false  -- OPT(vipa, 2020-09-23): this could possibly be true, just because it binds stronger than everything else

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | PNot {subpat = p} ->
    match getPatStringCode indent env p with (env, p2) then
    let p2 = if patIsAtomic p then p2 else join ["(", p2, ")"] in
    (env, join ["!", p2])
    else never
end

-----------
-- TYPES --
-----------
-- TODO(dlunde,2020-09-29) Update (also not up to date in boot?)

lang TypePrettyPrint = FunTypeAst + DynTypeAst + UnitTypeAst + CharTypeAst +
                       SeqTypeAst + TupleTypeAst + RecordTypeAst + DataTypeAst +
                       ArithTypeAst + BoolTypeAst + AppTypeAst + FunAst +
                       DataPrettyPrint + TypeVarAst

    sem getTypeStringCode (indent : Int) =
    | TyArrow t -> join ["(", getTypeStringCode indent t.from, ") -> (",
                               getTypeStringCode indent t.to, ")"]
    | TyDyn _ -> "Dyn"
    | TyUnit _ -> "()"
    | TyChar _ -> "Char"
    | TyString _ -> "String"
    | TySeq t -> join ["[", getTypeStringCode indent t.tpe, "]"]
    | TyProd t ->
      let tpes = map (lam x. getTypeStringCode indent x) t.tpes in
      join ["(", strJoin ", " tpes, ")"]
    | TyRecord t ->
      let conventry = lam entry.
          join [entry.ident, " : ", getTypeStringCode indent entry.tpe]
      in
      join ["{", strJoin ", " (map conventry t.tpes), "}"]
    | TyCon t -> t.ident  -- TODO(vipa, 2020-09-23): format properly with #con
    | TyInt _ -> "Int"
    | TyBool _ -> "Bool"
    | TyApp t ->
      join ["(", getTypeStringCode indent t.lhs, ") (",
            getTypeStringCode indent t.rhs, ")"]
    | TyVar t -> t.ident  -- TODO(vipa, 2020-09-23): format properly with #var
end

---------------------------
-- MEXPR PPRINT FRAGMENT --
---------------------------

lang MExprPrettyPrint =

  -- Terms
  VarPrettyPrint + AppPrettyPrint + FunPrettyPrint + RecordPrettyPrint +
  LetPrettyPrint + RecLetsPrettyPrint + ConstPrettyPrint + DataPrettyPrint +
  MatchPrettyPrint + UtestPrettyPrint + SeqPrettyPrint + NeverPrettyPrint

  -- Constants
  + IntPrettyPrint + ArithIntPrettyPrint + FloatPrettyPrint +
  ArithFloatPrettyPrint + BoolPrettyPrint + CmpIntPrettyPrint +
  CmpFloatPrettyPrint + CharPrettyPrint + SymbPrettyPrint + CmpSymbPrettyPrint
  + SeqOpPrettyPrint

  -- Patterns
  + VarPatPrettyPrint + SeqTotPatPrettyPrint + SeqEdgePatPrettyPrint +
  RecordPatPrettyPrint + DataPatPrettyPrint + IntPatPrettyPrint +
  CharPatPrettyPrint + BoolPatPrettyPrint + AndPatPrettyPrint +
  OrPatPrettyPrint + NotPatPrettyPrint

  -- Types
  + TypePrettyPrint

end

-----------
-- TESTS --
-----------

mexpr
use MExprPrettyPrint in

let cons_ = appf2_ (var_ "cons") in
let concat_ = appf2_ (var_ "concat") in

-- let foo = lam a. lam b.
--     let bar = lam x. addi b x in
--     let babar = 3 in
--     addi (bar babar) a
-- in
let func_foo =
  let_ "foo" (
    lam_ "a" (None ()) (
      lam_ "b" (None ()) (
        bindall_ [
          let_ "bar" (
            lam_ "x" (None ()) (
              addi_ (var_ "b") (var_ "x")
            )
          ),
          let_ "babar" (int_ 3),
          addi_ (app_ (var_ "bar")
                      (var_ "babar"))
                (var_ "a")
        ]
      )
    )
  )
in

-- recursive let factorial = lam n.
--     if eqi n 0 then
--       1
--     else
--       muli n (factorial (subi n 1))
-- in
let func_factorial =
    reclets_add "factorial"
        (lam_ "n" (Some (tyint_))
            (if_ (eqi_ (var_ "n") (int_ 0))
                 (int_ 1)
                 (muli_ (var_ "n")
                        (app_ (var_ "factorial")
                              (subi_ (var_ "n")
                                     (int_ 1))))))
    reclets_empty
in

-- recursive
--     let even = lam x.
--         if eqi x 0
--         then true
--         else not (odd (subi x 1))
--     let odd = lam x.
--         if eqi x 1
--         then true
--         else not (even (subi x 1))
-- in
let funcs_evenodd =
    reclets_add "even"
        (lam_ "x" (None ())
            (if_ (eqi_ (var_ "x") (int_ 0))
                 (true_)
                 (not_ (app_ (var_ "odd")
                             (subi_ (var_ "x") (int_ 1))))))
    (reclets_add "odd"
        (lam_ "x" (None ())
            (if_ (eqi_ (var_ "x") (int_ 1))
                 (true_)
                 (not_ (app_ (var_ "even")
                             (subi_ (var_ "x") (int_ 1))))))
    reclets_empty)
in


-- let recget = {i = 5, s = "hello!"} in
let func_recget =
    let_ "recget" (
        record_add "i" (int_ 5) (
        record_add "s" (str_ "hello!")
        record_empty))
in

-- let recconcs = lam rec. lam s. {rec with s = concat rec.s s} in
let func_recconcs =
    let_ "recconcs" (lam_ "rec" (None ()) (lam_ "s" (Some (tystr_)) (
        recordupdate_ (var_ "rec")
                      "s"
                      (concat_ (recordproj_ "s" (var_ "rec"))
                               (var_ "s")))))
in

-- con MyConA in
let func_mycona = condef_ "MyConA" (None ()) in

-- con #con"myConB" : (Bool, Int) in
let func_myconb = condef_ "myConB" (Some (typrod_ [tybool_, tyint_])) in

-- let isconb : Bool = lam c : #con"myConB".
--     match c with #con"myConB" (true, 17) then
--         true
--     else
--         false
let func_isconb =
    let_ "isconb" (
        lam_ "c" (Some (tycon_ "myConB")) (
            match_ (var_ "c")
                   (pcon_ "myConB" (ptuple_ [ptrue_, pint_ 17]))
                   (true_)
                   (false_)))
in

-- let addone : Int -> Int = lam i : Int. (lam x : Int. addi x 1) i
let func_addone =
  let_ "addone" (
      lam_ "i" (Some (tyint_)) (
        app_ (lam_ "x" (Some (tyint_)) (addi_ (var_ "x") (int_ 1)))
             (var_ "i")
      )
  )
in

-- let beginsWithBinaryDigit : String -> Bool = lam s : String.
--   match s with ['0' | '1'] ++ _ then true else false
let func_beginsWithBinaryDigit =
  let_ "beginsWithBinaryDigit" (
    lam_ "s" (Some (tycon_ "Bool")) (
      match_ (var_ "s")
             (pseqedgew_
               [por_ (pchar_ '0') (pchar_ '1')]
               [])
             (true_)
             (false_)
    )
  )
in

-- let pedanticIsSome : Option a -> Bool = lam o : Option a.
--   match o with !(None ()) & Some _ then true else false
let func_pedanticIsSome =
  let_ "pedanticIsSome" (
    lam_ "s" (Some (tyapp_ (tycon_ "Option") (tyvar_ "a"))) (
      match_ (var_ "o")
             (pand_
               (pnot_ (pcon_ "None" punit_))
               (pcon_ "Some" pvarw_))
             (true_)
             (false_)
    )
  )
in

let func_is123 =
  let_ "is123" (
    lam_ "l" (Some (tyseq_ tyint_)) (
      match_ (var_ "l")
             (pseqtot_ [pint_ 1, pint_ 2, pint_ 3])
             (true_)
             (false_)
    )
  )
in

let sample_ast =
  bindall_ [
    func_foo,
    func_factorial,
    funcs_evenodd,
    func_recget,
    func_recconcs,
    func_mycona,
    func_myconb,
    func_isconb,
    func_addone,
    func_beginsWithBinaryDigit,
    func_pedanticIsSome,
    func_is123
  ]
in

-- let _ = print "\n\n" in
-- let _ = print (expr2str sample_ast) in
-- let _ = print "\n\n" in

utest length (expr2str sample_ast) with 0 using geqi in
()
