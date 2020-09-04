
include "char.mc"
include "option.mc"
include "seq.mc"
include "string.mc"
include "name.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

let spacing = lam indent. makeSeq indent ' '
let newline = lam indent. concat "\n" (spacing indent)

-- Set spacing on increment
let incr = lam indent. addi indent 2

let symbolDelim = "'"

---------------------------------
-- PRETTY PRINTING ENVIRONMENT --
---------------------------------

type Env = {

  -- Used to keep track of strings assigned to names with symbols
  nameMap: AssocMap Name String,

  -- Used to keep track of strings assigned to names without symbols
  strMap: AssocMap String String,

  -- Count the number of occurrences of each (base) string to assist with
  -- assigning unique strings.
  count: AssocMap String Int

}

-- TODO Make it possible to debug the actual symbols

let _emptyEnv = {nameMap = assocEmpty, strMap = assocEmpty, count = assocEmpty}

-- Ensure string can be parsed
let parserStr = lam str. lam prefix. lam cond.
  if eqi (length str) 0 then concat prefix "\"\""
  else if cond str then str
  else join [prefix, "\"", str, "\""]

-- Constructor string parser translation
let conString = lam str.
  parserStr str "#con" (lam str. is_upper_alpha (head str))

-- Variable string parser translation
let varString = lam str.
  parserStr str "#var" (lam str. is_lower_alpha (head str))

-- Label string parser translation for records
let labelString = lam str.
  parserStr str "#label" (lam str. is_lower_alpha (head str))

let _ppLookupName = assocLookup {eq = nameEqSym}
let _ppLookupStr = assocLookup {eq = eqstr}
let _ppInsertName = assocInsert {eq = nameEqSym}
let _ppInsertStr = assocInsert {eq = eqstr}

-- Look up the string associated with a name in the environment
let _lookup : Name -> Env -> Option String = lam name. lam env.
  match env with { nameMap = nameMap, strMap = strMap } then
    match _ppLookupName name nameMap with Some str then
      Some str
    else match _ppLookupStr (nameGetStr name) strMap with Some str then
      Some str
    else None ()
  else never

-- Check if a string is free in the environment.
let _free : String -> Env -> Bool = lam str. lam env.
  match env with { nameMap = nameMap, strMap = strMap } then
    let f = lam _. lam v. eqstr str v in
    not (or (assocAny f nameMap) (assocAny f strMap))
  else never

-- Add a binding to the environment
let _add : Name -> String -> Int -> Env -> Env =
  lam name. lam str. lam i. lam env.
    let baseStr = nameGetStr name in
    match env with {nameMap = nameMap, strMap = strMap, count = count} then
      let count = _ppInsertStr baseStr i count in
      if nameHasSym name then
        let nameMap = _ppInsertName name str nameMap in
        {nameMap = nameMap, strMap = strMap, count = count}
      else
        let strMap = _ppInsertStr baseStr str strMap in
        {nameMap = nameMap, strMap = strMap, count = count}
    else never

-- Get a string for the current name. Returns both the string and a new
-- environment.
let _getStr : Name -> Env -> (Env, String) = lam name. lam env.
  match _lookup name env with Some str then (env,str)
  else
    let baseStr = nameGetStr name in
    if _free baseStr env then (_add name baseStr 1 env, baseStr)
    else
      match env with {count = count} then
        let start = match _ppLookupStr baseStr count with Some i then i else 1 in
        recursive let findFree : String -> Int -> (String, Int) =
          lam baseStr. lam i.
            let proposal = concat baseStr (int2string i) in
            if _free proposal env then (proposal, i)
            else findFree baseStr (addi i 1)
        in
        match findFree baseStr start with (str, i) then
          (_add name str (addi i 1) env, str)
        else never
      else never

-- Get an optional list of tuple expressions for a record. If the record does
-- not represent a tuple, None () is returned.
let _record2tuple = lam tm.
  use RecordAst in
  match tm with TmRecord t then
    let keys = assocKeys {eq=eqstr} t.bindings in
    match all stringIsInt keys with false then None () else
    let intKeys = map string2int keys in
    let sortedKeys = sort subi intKeys in
    -- Check if keys are a sequence 0..(n-1)
    match and (eqi 0 (head sortedKeys))
              (eqi (subi (length intKeys) 1) (last sortedKeys)) with true then
      -- Note: Quadratic complexity. Sorting the association list directly
      -- w.r.t. key would improve complexity to n*log(n).
      Some (map (lam key. assocLookupOrElse {eq=eqstr}
                            (lam _. error "Key not found")
                            (int2string key) t.bindings)
                 sortedKeys)
    else None ()
  else error "Not a record"


-----------
-- TERMS --
-----------

lang VarPrettyPrint = VarAst
  sem isAtomic =
  | TmVar _ -> true

  sem pprintCode (indent : Int) (env: Env) =
  | TmVar {ident = ident} ->
    match _getStr ident env with (env,str) then (env,varString str) else never
end

lang AppPrettyPrint = AppAst
  sem isAtomic =
  | TmApp _ -> false

  sem pprintCode (indent : Int) (env: Env) =
  | TmApp t ->
    recursive let appseq =
      lam t. match t with TmApp {lhs = lhs, rhs = rhs} then
        snoc (appseq lhs) rhs
      else [t]
    in
    let apps = appseq (TmApp t) in

    let f = lam indent. lam env. lam t.
      let i = if isAtomic t then indent else addi 1 indent in
      match pprintCode i env t with (env,str) then
        if isAtomic t then (env,str)
        else (env,join ["(", str, ")"])
      else never
    in

    match f indent env (head apps) with (env,fun) then
      let aindent = incr indent in
      match mapAccumL (f aindent) env (tail apps) with (env,args) then
        (env, join [fun, newline aindent, strJoin (newline aindent) args])
      else never
    else error "Impossible"
end

lang FunPrettyPrint = FunAst
  sem isAtomic =
  | TmLam _ -> false

  sem getTypeStringCode (indent : Int) =
  -- Intentionally left blank

  sem pprintCode (indent : Int) (env: Env) =
  | TmLam t ->
    match _getStr t.ident env with (env,str) then
      let ident = varString str in
      let tpe =
        match t.tpe with Some t1 then
          concat " : " (getTypeStringCode indent t1)
        else ""
      in
      match pprintCode (incr indent) env t.body with (env,body) then
        (env,join ["lam ", ident, tpe, ".", newline (incr indent), body])
      else never
    else never
end

lang RecordPrettyPrint = RecordAst
  sem isAtomic =
  | TmRecord _ -> true
  | TmRecordUpdate _ -> true

  sem pprintCode (indent : Int) (env: Env) =
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
      let innerIndent = incr (incr indent) in
      match
        assocMapAccum {eq=eqstr}
          (lam env. lam k. lam v.
             match pprintCode innerIndent env v with (env, str) then
               (env, join [labelString k, " =", newline innerIndent, str])
             else never)
           env t.bindings
      with (env, bindMap) then
        let binds = assocValues {eq=eqstr} bindMap in
        let merged = strJoin (concat "," (newline (incr indent))) binds in
        (env,join ["{ ", merged, " }"])
      else never

  | TmRecordUpdate t ->
    let i = incr indent in
    let ii = incr i in
    match pprintCode i env t.rec with (env,rec) then
      match pprintCode ii env t.value with (env,value) then
        (env,join ["{ ", rec, newline i,
                   "with", newline i,
                   labelString t.key, " =", newline ii, value, " }"])
      else never
    else never
end

lang LetPrettyPrint = LetAst
  sem isAtomic =
  | TmLet _ -> false

  sem getTypeStringCode (indent : Int) =
  -- Intentionally left blank

  sem pprintCode (indent : Int) (env: Env) =
  | TmLet t ->
    match _getStr t.ident env with (env,str) then
      let ident = varString str in
      match pprintCode (incr indent) env t.body with (env,body) then
        match pprintCode indent env t.inexpr with (env,inexpr) then
          (env, join ["let ", ident, " =", newline (incr indent),
                      body, newline indent,
                      "in", newline indent,
                      inexpr])
        else never
      else never
    else never
end

lang RecLetsPrettyPrint = RecLetsAst
  sem isAtomic =
  | TmRecLets _ -> false

  sem getTypeStringCode (indent : Int) =
  -- Intentionally left blank

  sem pprintCode (indent : Int) (env: Env) =
  | TmRecLets t ->
    let lname = lam env. lam bind.
      match _getStr bind.ident env with (env,str) then
        (env,varString str)
      else never in
    let lbody = lam env. lam bind.
      match pprintCode (incr (incr indent)) env bind.body with (env,str) then
        (env,varString str)
      else never in
    match mapAccumL lname env t.bindings with (env,idents) then
      match mapAccumL lbody env t.bindings with (env,bodies) then
        match pprintCode indent env t.inexpr with (env,inexpr) then
          let fzip = lam ident. lam body.
            join [newline (incr indent),
                  "let ", ident, " =", newline (incr (incr indent)), body]
          in
          (env,join ["recursive", join (zipWith fzip idents bodies),
                 newline indent, "in", newline indent, inexpr])
        else never
      else never
    else never
end

lang ConstPrettyPrint = ConstAst
  sem isAtomic =
  | TmConst _ -> true

  sem getConstStringCode (indent : Int) =
  -- intentionally left blank

  sem pprintCode (indent : Int) (env: Env) =
  | TmConst t -> (env,getConstStringCode indent t.val)
end

lang DataPrettyPrint = DataAst
  sem isAtomic =
  | TmConDef _ -> false
  | TmConApp _ -> false

  sem getTypeStringCode (indent : Int) =
  -- Intentionally left blank

  sem pprintCode (indent : Int) (env: Env) =
  | TmConDef t ->
    match _getStr t.ident env with (env,str) then
      let str = conString str in
      let tpe =
        match t.tpe with Some t1 then
          concat " : " (getTypeStringCode indent t1)
        else ""
      in
      match pprintCode indent env t.inexpr with (env,inexpr) then
        (env,join ["con ", str, tpe, " in", newline indent, inexpr])
      else never
    else never

  | TmConApp t ->
    match _getStr t.ident env with (env,str) then
      let l = conString str in
      let i = if isAtomic t.body then incr indent else addi 1 (incr indent) in
      match pprintCode i env t.body with (env,r) then
        let str = if isAtomic t.body then r else join ["(", r, ")"] in
          (env,join [l, newline (incr indent), str])
      else never
    else never
end

lang MatchPrettyPrint = MatchAst
  sem isAtomic =
  | TmMatch _ -> false

  sem getPatStringCode (indent : Int) (env: Env) =
  -- intentionally left blank

  sem pprintCode (indent : Int) (env: Env) =
  | TmMatch t ->
    let i = indent in
    let ii = incr indent in
    match pprintCode ii env t.target with (env,target) then
      match getPatStringCode ii env t.pat with (env,pat) then
        match pprintCode ii env t.thn with (env,thn) then
          match pprintCode ii env t.els with (env,els) then
            (env,join ["match", newline ii, target, newline i,
                       "with", newline ii, pat, newline i,
                       "then", newline ii, thn, newline i,
                       "else", newline ii, els])
          else never
        else never
      else never
    else never
end

lang UtestPrettyPrint = UtestAst
  sem isAtomic =
  | TmUtest _ -> false

  sem pprintCode (indent : Int) (env: Env) =
  | TmUtest t ->
    match pprintCode indent env t.test with (env,test) then
      match pprintCode indent env t.expected with (env,expected) then
        match pprintCode indent env t.next with (env,next) then
          (env,join ["utest ", test, newline indent,
                 "with ", expected, newline indent,
                 "in", newline indent, next])
        else never
      else never
    else never
end

lang SeqPrettyPrint = SeqAst + ConstPrettyPrint + CharAst
  sem isAtomic =
  | TmSeq _ -> true

  sem pprintCode (indent : Int) (env: Env) =
  | TmSeq t ->
    let extract_char = lam e.
      match e with TmConst t1 then
        match t1.val with CChar c then
          Some (c.val)
        else None ()
      else None ()
    in
    let is_char = lam e. match extract_char e with Some c then true else false in
    if all is_char t.tms then
      (env,concat "\""
        (concat
           (map (lam e. match extract_char e with Some c then c else '?') t.tms)
           "\""))
    else
    match mapAccumL (lam env. lam tm. pprintCode (incr indent) env tm) env t.tms
    with (env,tms) then
      let merged = strJoin (concat "," (newline (incr indent))) tms in
      (env,join ["[ ", merged, " ]"])
    else never
end

lang NeverPrettyPrint = NeverAst
  sem isAtomic =
  | TmNever _ -> true

  sem pprintCode (indent : Int) (env: Env) =
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
   | CEqs _ -> "eqs"
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

lang VarPatPrettyPrint = VarPat
  sem getPatStringCode (indent : Int) (env: Env) =
  | PVar {ident = PName name} ->
    match _getStr name env with (env,str) then (env,varString str) else never
  | PVar {ident = PWildcard ()} -> (env,"_")
end

lang SeqTotPatPrettyPrint = SeqTotPat
  -- TODO
end

lang SeqEdgePatPrettyPrint = SeqEdgePat
  -- TODO
end

lang RecordPatPrettyPrint = RecordPat
  sem getPatStringCode (indent : Int) (env: Env) =
  | PRecord {bindings = bindings} ->
    match
      assocMapAccum {eq=eqstr}
        (lam env. lam k. lam v.
           match getPatStringCode indent env v with (env,str) then
             (env,join [labelString k, " = ", str])
           else never)
         env bindings
    with (env,bindMap) then
      (env,join ["{", strJoin ", " (assocValues {eq=eqstr} bindMap), "}"])
    else never
end

lang DataPatPrettyPrint = DataPat
  sem getPatStringCode (indent : Int) (env: Env) =
  | PCon t ->
    match _getStr t.ident env with (env,str) then
      let name = conString str in
      match getPatStringCode indent env t.subpat with (env,subpat) then
        (env,join [name, " (", subpat, ")"])
      else never
    else never
end

lang IntPatPrettyPrint = IntPat
  sem getPatStringCode (indent : Int) (env: Env) =
  | PInt t -> (env, int2string t.val)
end

lang CharPatPrettyPrint = CharPat
  sem getPatStringCode (indent : Int) (env: Env) =
  | PChar t -> (env, ['\'', t.val, '\''])
end

lang BoolPatPrettyPrint = BoolPat
  sem getPatStringCode (indent : Int) (env: Env) =
  | PBool b -> (env, if b.val then "true" else "false")
end

lang AndPatPrettyPrint = AndPat
  -- TODO
end

lang OrPatPrettyPrint = OrPat
  -- TODO
end

lang NotPatPrettyPrint = NotPat
  -- TODO
end

-----------
-- TYPES --
-----------
-- TODO Update (also not up to date in boot?)

lang TypePrettyPrint = FunTypeAst + DynTypeAst + UnitTypeAst + CharTypeAst + SeqTypeAst +
                       TupleTypeAst + RecordTypeAst + DataTypeAst + ArithTypeAst +
                       BoolTypeAst + AppTypeAst + FunAst + DataPrettyPrint
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
    | TyCon t -> t.ident
    | TyInt _ -> "Int"
    | TyBool _ -> "Bool"
    | TyApp t ->
      -- Unsure about how this should be formatted or what this type even means.
      getTypeStringCode indent (TyArrow {from = t.lhs, to = t.rhs})
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

---------------------------
-- CONVENIENCE FUNCTIONS --
---------------------------

let expr2str = use MExprPrettyPrint in
  lam expr. match pprintCode 0 _emptyEnv expr with (_,str) then str else never

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
    func_addone
  ]
in

-- let _ = print "\n\n" in
-- let _ = print (expr2str sample_ast) in
-- let _ = print "\n\n" in

utest geqi (length (expr2str sample_ast)) 0 with true in
()
