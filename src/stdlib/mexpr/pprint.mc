
include "char.mc"
include "option.mc"
include "seq.mc"
include "string.mc"
include "stringid.mc"
include "name.mc"
include "map.mc"

include "ast.mc"
include "ast-builder.mc"
include "builtin.mc"
include "keywords.mc"
include "record.mc"

----------------------------
-- PRETTY PRINT INDENTING --
----------------------------

-- Indentation consisting of [indent] spaces
let pprintSpacing = lam indent. make indent ' '

-- Newline followed by [indent] spaces
let pprintNewline = lam indent. concat "\n" (pprintSpacing indent)

-- Increment [indent] by 2
let pprintIncr = lam indent. addi indent 2

---------------------------------
-- PRETTY PRINTING ENVIRONMENT --
---------------------------------

type PprintEnv = {

  -- Used to keep track of strings assigned to names
  nameMap: Map Name String,

  -- Count the number of occurrences of each (base) string to assist with
  -- assigning unique strings.
  count: Map String Int,

  -- Set of strings currently in use in the environment. Equals the set of
  -- values in 'nameMap'.
  -- OPT(Linnea, 2021-01-27): Maps offer the most efficient lookups as for now.
  -- Could be replaced by an efficient set data structure, were we to have one.
  strings: Set String

}

-- TODO(dlunde,2020-09-29) Make it possible to debug the actual symbols

let pprintEnvEmpty = { nameMap = mapEmpty nameCmp,
                       count = mapEmpty cmpString,
                       strings = setEmpty cmpString }


-- Look up the string associated with a name in the environment
let pprintEnvLookup : Name -> PprintEnv -> Option String = lam name. lam env : PprintEnv.
  match env with { nameMap = nameMap } in
  mapLookup name nameMap

-- Check if a string is free in the environment.
let pprintEnvFree : String -> PprintEnv -> Bool = lam str. lam env : PprintEnv.
  match env with { strings = strings } in
  not (setMem str strings)

-- Add a binding to the environment
let pprintEnvAdd : Name -> String -> Int -> PprintEnv -> PprintEnv =
  lam name. lam str. lam i. lam env : PprintEnv.
    match env with {nameMap = nameMap, count = count, strings = strings} in
    let baseStr = nameGetStr name in
    let count = mapInsert baseStr i count in
    let nameMap = mapInsert name str nameMap in
    let strings = setInsert str strings in
    {nameMap = nameMap, count = count, strings = strings}

-- Adds the given name to the environment, if its exact string is not already
-- mapped to. If the exact string is already mapped to, return None (). This
-- function is useful if you have names which must be printed with their exact
-- strings (e.g., library functions or similar).
let pprintAddStr : PprintEnv -> Name -> Option PprintEnv =
  lam env. lam name.
    let baseStr = nameGetStr name in
    if pprintEnvFree baseStr env then Some (pprintEnvAdd name baseStr 1 env)
    else None ()

---------------------------------
-- IDENTIFIER PARSER FUNCTIONS --
---------------------------------

-- Ensure string can be parsed
let _parserStr = lam str. lam prefix. lam cond.
  if eqi (length str) 0 then concat prefix "\"\""
  else if cond str then str
  else join [prefix, "\"", str, "\""]

let _isValidIdentContents = lam str.
  forAll (lam c. or (isAlphanum c) (eqc c '_')) str

let _isValidLowerIdent = lam str.
  match str with [x]
  then isLowerAlpha x
  else if isLowerAlphaOrUnderscore (head str) then
    _isValidIdentContents (tail str)
  else false

-- Variable string parser translation
let pprintVarString = lam str.
  _parserStr str "#var" _isValidLowerIdent

-- Frozen variable string parser translation
let pprintFrozenString = lam str.
  _parserStr str "#frozen" (lam. false)

-- Constructor string parser translation
let pprintConString = lam str.
  _parserStr str "#con" (lam str. isUpperAlpha (head str))

-- Type constructor string parser translation
let pprintTypeString = lam str.
  _parserStr str "#type" (lam str. isUpperAlpha (head str))

-----------
-- TERMS --
-----------

lang IdentifierPrettyPrint
  sem pprintVarName : PprintEnv -> Name -> (PprintEnv, String)
  sem pprintConName : PprintEnv -> Name -> (PprintEnv, String)
  sem pprintTypeName : PprintEnv -> Name -> (PprintEnv, String)
  sem pprintLabelString : SID -> String

  -- Get a string for the given name. Returns both the string and a new
  -- environment.
  sem pprintEnvGetStr (env : PprintEnv) =
  | name ->
    match pprintEnvLookup name env with Some str then (env,str)
    else
      let baseStr = nameGetStr name in
      if pprintEnvFree baseStr env then (pprintEnvAdd name baseStr 1 env, baseStr)
      else
        match env with {count = count} in
        let start =
          match mapLookup baseStr count
          with Some i then i else 1 in
        recursive let findFree : String -> Int -> (String, Int) =
          lam baseStr. lam i.
            let proposal = concat baseStr (int2string i) in
            if pprintEnvFree proposal env then (proposal, i)
            else findFree baseStr (addi i 1)
        in
        match findFree baseStr start with (str, i) in
        (pprintEnvAdd name str (addi i 1) env, str)
end

lang MExprIdentifierPrettyPrint = IdentifierPrettyPrint
  sem pprintVarName (env: PprintEnv) =
  | name ->
    match pprintEnvGetStr env name with (env,str) in
    let s = pprintVarString str in
    (env, s)

  sem pprintFrozenName (env: PprintEnv) =
  | name ->
    match pprintEnvGetStr env name with (env,str) in
    let s = pprintFrozenString str in
    (env, s)

  sem pprintConName (env: PprintEnv) =
  | name ->
    match pprintEnvGetStr env name with (env,str) in
    let s = pprintConString str in
    (env, s)

  sem pprintTypeName (env: PprintEnv) =
  | name ->
    match pprintEnvGetStr env name with (env,str) in
    let s = pprintTypeString str in
    (env, s)

  sem pprintLabelString =
  | sid ->
    _parserStr (sidToString sid) "#label" _isValidLowerIdent

  sem pprintProjString =
  | sid ->
    _parserStr (sidToString sid) "#label"
    (lam str. if forAll isDigit str then true else _isValidLowerIdent str)
end

lang PrettyPrint = IdentifierPrettyPrint
  sem isAtomic =
  -- Intentionally left blank
  sem patIsAtomic =
  -- Intentionally left blank
  sem typePrecedence =
  | ty -> 100000

  sem pprintCode (indent : Int) (env: PprintEnv) =
  -- Intentionally left blank
  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  -- Intentionally left blank
  sem getTypeStringCode (indent : Int) (env : PprintEnv) =
  -- Intentionally left blank

  sem exprToString (env: PprintEnv) =
  | expr ->
    match pprintCode 0 env expr with (_,str) in str

  sem exprToStringKeywords (keywords: [String]) =
  | expr ->
    let addName = lam env. lam name.
      match pprintAddStr env name with Some env then env
      else error
        (join ["Duplicate keyword in exprToStringKeywords: ", nameGetStr name])
    in
    let env = foldl addName pprintEnvEmpty (map nameSym keywords) in
    exprToString env expr

  sem typeToString (env: PprintEnv) =
  | ty ->
    match getTypeStringCode 0 env ty with (_,str) in str

  sem expr2str =
  | expr -> exprToString pprintEnvEmpty expr

  sem type2str =
  | ty -> typeToString pprintEnvEmpty ty

  -- Helper function for printing parentheses
  sem printParen (indent : Int) (env: PprintEnv) =
  | expr ->
    let i = if isAtomic expr then indent else addi 1 indent in
    match pprintCode i env expr with (env,str) in
    if isAtomic expr then (env,str)
    else (env,join ["(", str, ")"])

  -- Helper function for printing a list of arguments
  sem printArgs (indent : Int) (env : PprintEnv) =
  | exprs ->
    match mapAccumL (printParen indent) env exprs with (env,args) in
    (env, strJoin (pprintNewline indent) args)

  -- Helper function for printing parentheses (around patterns)
  sem printPatParen (indent : Int) (env : PprintEnv) =
  | pat ->
    let i = if patIsAtomic pat then indent else addi 1 indent in
    match getPatStringCode i env pat with (env, str) in
    if patIsAtomic pat then (env, str)
    else (env, join ["(", str, ")"])

  -- Helper function for printing parentheses (around types)
  sem printTypeParen (indent : Int) (prec : Int) (env : PprintEnv) =
  | ty ->
    match getTypeStringCode indent env ty with (env, str) in
    if leqi prec (typePrecedence ty) then (env, str)
    else (env, join ["(", str, ")"])
end

lang VarPrettyPrint = MExprIdentifierPrettyPrint + VarAst
  sem isAtomic =
  | TmVar _ -> true

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmVar {ident = ident, frozen = frozen} ->
    if frozen
    then pprintFrozenName env ident
    else pprintVarName env ident
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
      match printArgs aindent env (tail apps) with (env,args) in
      (env, join [fun, pprintNewline aindent, args])
    else errorSingle [t.info] "Impossible"
end

lang LamPrettyPrint = PrettyPrint + LamAst + UnknownTypeAst
  sem isAtomic =
  | TmLam _ -> false

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmLam t ->
    match pprintVarName env t.ident with (env,str) in
    match getTypeStringCode indent env t.tyAnnot with (env, ty) in
    let ty = if eqString ty "Unknown" then "" else concat ": " ty in
    match pprintCode (pprintIncr indent) env t.body with (env,body) in
    (env,
     join ["lam ", str, ty, ".", pprintNewline (pprintIncr indent),
           body])
end

lang RecordPrettyPrint = PrettyPrint + RecordAst
  sem isAtomic =
  | TmRecord _ -> true
  | TmRecordUpdate _ -> true

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmRecord {bindings = bindings} ->
    if mapIsEmpty bindings then (env,"{}")
    else match record2tuple bindings with Some tms then
      match mapAccumL (lam env. lam e. pprintCode indent env e) env tms
      with (env,tupleExprs) in
      let merged = match tupleExprs with [e] then
                     concat e ","
                   else strJoin ", " tupleExprs in
      (env, join ["(", merged, ")"])
    else
      let innerIndent = pprintIncr (pprintIncr indent) in
      match
        mapMapAccum
          (lam env. lam k. lam v.
             match pprintCode innerIndent env v with (env, str) in
             (env,
              join [pprintLabelString k, " =", pprintNewline innerIndent,
                    str]))
           env bindings
      with (env, bindMap) in
      let binds = mapValues bindMap in
      let merged =
        strJoin (concat "," (pprintNewline (pprintIncr indent))) binds
      in
      (env,join ["{ ", merged, " }"])

  | TmRecordUpdate t ->
    let i = pprintIncr indent in
    let ii = pprintIncr i in
    match pprintCode i env t.rec with (env,rec) in
      match pprintCode ii env t.value with (env,value) in
        (env,join ["{ ", rec, pprintNewline i,
                   "with", pprintNewline i,
                   pprintLabelString t.key, " =", pprintNewline ii, value,
                   " }"])
end

lang LetPrettyPrint = PrettyPrint + LetAst + UnknownTypeAst
  sem isAtomic =
  | TmLet _ -> false

  sem pprintLetAssignmentCode (indent : Int) (env: PprintEnv) =
  | {ident = ident, body = body, tyAnnot = tyAnnot} ->
    match pprintEnvGetStr env ident with (env,baseStr) in
    match
      match tyAnnot with TyUnknown _ then (env,"") else
      match getTypeStringCode indent env tyAnnot with (env, ty) in
      (env, concat ": " ty)
    with (env, tyStr) in
    match pprintCode (pprintIncr indent) env body with (env,bodyStr) in
    (env,
     join ["let ", pprintVarString baseStr, tyStr, " =",
           pprintNewline (pprintIncr indent), bodyStr])

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmLet t ->
    match pprintEnvGetStr env t.ident with (env,baseStr) in
    match pprintCode indent env t.inexpr with (env,inexpr) in
    if eqString baseStr "" then
      match printParen (pprintIncr indent) env t.body with (env,body)
      in (env, join [body, pprintNewline indent, "; ", inexpr])
    else
      match pprintLetAssignmentCode indent env {
              ident = t.ident, body = t.body, tyAnnot = t.tyAnnot}
      with (env, letStr) in
      (env,
       join [letStr,
             pprintNewline indent, "in",
             pprintNewline indent, inexpr])
end

lang ExtPrettyPrint = PrettyPrint + ExtAst + UnknownTypeAst
  sem isAtomic =
  | TmExt _ -> false

  sem getTypeStringCode (indent : Int) (env : PprintEnv) =
  -- Intentionally left blank

  sem pprintExtCode (indent : Int) (env: PprintEnv) =
  | {ident = ident, tyIdent = tyIdent, effect = effect} ->
    match pprintVarName env ident with (env,str) in
    match getTypeStringCode indent env tyIdent with (env,ty) in
      let e = if effect then "!" else "" in
      (env,
       join ["external ", str, e, " : ", ty])

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmExt t ->
    match pprintExtCode indent env {
      ident = t.ident, tyIdent = t.tyIdent, effect = t.effect}
    with (env, extStr) in
    match pprintCode indent env t.inexpr with (env,inexpr) in
    (env, join [extStr, pprintNewline indent,
                "in", pprintNewline indent,
                inexpr])
end

lang TypePrettyPrint = PrettyPrint + TypeAst + UnknownTypeAst + VariantTypeAst
  sem isAtomic =
  | TmType _ -> false

  sem pprintTypeCode (indent : Int) (env : PprintEnv) =
  | {ident = ident, params = params, tyIdent = tyIdent} ->
    match pprintTypeName env ident with (env,identStr) in
    match mapAccumL pprintEnvGetStr env params with (env, paramsStr) in
    let paramStr = strJoin " " (cons "" paramsStr) in
    match tyIdent with TyUnknown _ | TyVariant _ then
      (env, join ["type ", identStr, paramStr])
    else
      match getTypeStringCode indent env tyIdent with (env, tyIdentStr) in
      (env, join ["type ", identStr, paramStr, " =",
                pprintNewline (pprintIncr indent),
                tyIdentStr])

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmType t ->
    match pprintTypeCode indent env {
      ident = t.ident, params = t.params, tyIdent = t.tyIdent}
    with (env, typeStr) in
    match pprintCode indent env t.inexpr with (env,inexpr) in
    (env, join [
      typeStr, pprintNewline indent,
      "in", pprintNewline indent,
      inexpr])
end

lang RecLetsPrettyPrint = PrettyPrint + LetPrettyPrint + RecLetsAst + UnknownTypeAst
  sem isAtomic =
  | TmRecLets _ -> false

  sem pprintRecLetsCode (indent : Int) (env : PprintEnv) =
  | bindings ->
    let i = indent in
    let ii = pprintIncr i in
    let f = lam env. lam bind : RecLetBinding.
      pprintLetAssignmentCode ii env {
        ident = bind.ident, body = bind.body, tyAnnot = bind.tyAnnot}
    in
    match mapAccumL f env bindings with (env,bindingStrs) in
    let joinedBindings = strJoin (pprintNewline ii) bindingStrs in
    (env,join ["recursive", pprintNewline ii,
               joinedBindings])

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmRecLets t ->
    match pprintCode indent env t.inexpr with (env,inexpr) in
    match t.bindings with [] then
      (env, inexpr)
    else
      match pprintRecLetsCode indent env t.bindings with (env, recletStr) in
      (env, join [recletStr, pprintNewline indent,
                  "in", pprintNewline indent,
                  inexpr])
end

lang ConstPrettyPrint = PrettyPrint + ConstAst
  sem isAtomic =
  | TmConst _ -> true

  sem getConstStringCode (indent : Int) =
  -- intentionally left blank

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmConst t -> (env,getConstStringCode indent t.val)
end

lang DataPrettyPrint = PrettyPrint + DataAst + UnknownTypeAst
  sem isAtomic =
  | TmConDef _ -> false
  | TmConApp _ -> false

  sem pprintConDefCode (indent : Int) (env : PprintEnv) =
  | {ident = ident, tyIdent = tyIdent} ->
    match pprintConName env ident with (env, str) in
    match getTypeStringCode indent env tyIdent with (env, ty) in
    let ty = if eqString ty "Unknown" then "" else concat ": " ty in
    (env, join ["con ", str, ty])

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmConDef t ->
    match pprintConDefCode indent env {ident = t.ident, tyIdent = t.tyIdent}
    with (env, conStrTy) in
    match pprintCode indent env t.inexpr with (env,inexpr) in
    (env,join [conStrTy, " in", pprintNewline indent, inexpr])

  | TmConApp t ->
    match pprintConName env t.ident with (env,str) in
    match printParen (pprintIncr indent) env t.body with (env,body) in
    (env, join [str, pprintNewline (pprintIncr indent), body])
end

lang MatchPrettyPrint = PrettyPrint + MatchAst
  sem isAtomic =
  | TmMatch _ -> false

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  -- intentionally left blank

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmMatch t -> pprintTmMatchNormally indent env t

 sem pprintTmMatchBegin (indent : Int) (env: PprintEnv) =
  | t ->
    let i = indent in
    let ii = pprintIncr indent in
    match pprintCode ii env t.target with (env,target) in
    match getPatStringCode ii env t.pat with (env,pat) in
    (env,join ["match", pprintNewline ii, target, pprintNewline i,
               "with", pprintNewline ii, pat, pprintNewline i])

  sem pprintTmMatchNormally (indent : Int) (env: PprintEnv) =
  | t ->
    let i = indent in
    let ii = pprintIncr indent in
    match pprintTmMatchBegin i env t with (env,begin) in
    match pprintCode ii env t.thn with (env,thn) in
    match pprintCode ii env t.els with (env,els) in
    (env,join [begin,
               "then", pprintNewline ii, thn, pprintNewline i,
               "else", pprintNewline ii, els])

  sem pprintTmMatchIn (indent : Int) (env: PprintEnv) =
  | t ->
    let i = indent in
    let ii = pprintIncr indent in
    match pprintTmMatchBegin i env t with (env,begin) in
    match pprintCode ii env t.thn with (env,thn) in
    (env,join [begin, "in", pprintNewline i, thn])
end

lang RecordProjectionSyntaxSugarPrettyPrint = MExprIdentifierPrettyPrint +
  MatchPrettyPrint + RecordPat + NeverAst + NamedPat + VarAst
  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmMatch (t & {els = TmNever _}) -> pprintTmMatchIn indent env t
  | TmMatch (t &
    { pat = PatRecord
      { bindings = bindings
      }
    , thn = TmVar {ident = exprName}
    , els = TmNever _
    , target = expr
    })
  ->
    let binds : [(SID, Pat)] = mapBindings bindings in
    match binds with [(fieldLabel, PatNamed {ident = PName patName})]
      then
      if nameEq patName exprName
      then
        match printParen indent env expr with (env, expr) in
        (env, join [expr, ".", pprintProjString fieldLabel])
      else pprintTmMatchIn indent env t
    else pprintTmMatchIn indent env t
end

lang UtestPrettyPrint = PrettyPrint + UtestAst
  sem isAtomic =
  | TmUtest _ -> false

  sem pprintUtestCode (indent : Int) (env : PprintEnv) =
  | {test = test, expected = expected, tusing = tusing} ->
    match pprintCode indent env test with (env,testStr) in
    match pprintCode indent env expected with (env,expectedStr) in
    match
      optionMapOr (env,"") (
        lam tusing.
          match pprintCode indent env tusing with (env,tusingStr) in
          (env,join [pprintNewline indent, "using ", tusingStr])
        ) tusing
    with (env,tusingStr) in
    (env,join ["utest ", testStr, pprintNewline indent,
               "with ", expectedStr, tusingStr])

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmUtest t ->
    match pprintUtestCode indent env {
      test = t.test, expected = t.expected, tusing = t.tusing}
    with (env, utestStr) in
    match pprintCode indent env t.next with (env,next) in
    (env,join [utestStr, pprintNewline indent,
               "in", pprintNewline indent, next])
end

lang SeqPrettyPrint = PrettyPrint + SeqAst + ConstPrettyPrint + CharAst
  sem isAtomic =
  | TmSeq _ -> true

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmSeq t ->
    let extract_char = lam e.
      match e with TmConst t1 then
        match t1.val with CChar c then
          Some c.val
        else None ()
      else None ()
    in
    match optionMapM extract_char t.tms with Some str then
      (env, join ["\"", escapeString str, "\""])
    else
    match mapAccumL (lam env. lam tm. pprintCode (pprintIncr indent) env tm)
                    env t.tms
    with (env,tms) in
    let merged =
      strJoin (concat "," (pprintNewline (pprintIncr indent))) tms
    in
    (env,join ["[ ", merged, " ]"])
end

lang NeverPrettyPrint = PrettyPrint + NeverAst
  sem isAtomic =
  | TmNever _ -> true

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmNever _ -> (env,"never")
end

---------------
-- CONSTANTS --
---------------
-- All constants in boot have not been implemented. Missing ones can be added
-- as needed.

lang UnsafeCoercePrettyPrint = UnsafeCoerceAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CUnsafeCoerce _ -> "unsafeCoerce"
end

lang IntPrettyPrint = IntAst + IntPat + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CInt t -> int2string t.val
end

lang ArithIntPrettyPrint = ArithIntAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CAddi _ -> "addi"
  | CSubi _ -> "subi"
  | CMuli _ -> "muli"
  | CModi _ -> "modi"
  | CDivi _ -> "divi"
  | CNegi _ -> "negi"
end

lang ShiftIntPrettyPrint = ShiftIntAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CSlli _ -> "slli"
  | CSrli _ -> "srli"
  | CSrai _ -> "srai"
end

lang FloatPrettyPrint = FloatAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CFloat t ->
    if ltf t.val 0. then join ["(negf ", float2string (negf t.val), ")"]
    else float2string t.val
end

lang ArithFloatPrettyPrint = ArithFloatAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CAddf _ -> "addf"
  | CSubf _ -> "subf"
  | CMulf _ -> "mulf"
  | CDivf _ -> "divf"
  | CNegf _ -> "negf"
end

lang FloatIntConversionPrettyPrint = FloatIntConversionAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CFloorfi _ -> "floorfi"
  | CCeilfi _ -> "ceilfi"
  | CRoundfi _ -> "roundfi"
  | CInt2float _ -> "int2float"
end

lang BoolPrettyPrint = BoolAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CBool b -> if b.val then "true" else "false"
end

lang CmpIntPrettyPrint = CmpIntAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CEqi _ -> "eqi"
  | CNeqi _ -> "neqi"
  | CLti _ -> "lti"
  | CGti _ -> "gti"
  | CLeqi _ -> "leqi"
  | CGeqi _ -> "geqi"
end

lang CmpFloatPrettyPrint = CmpFloatAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CEqf _ -> "eqf"
  | CLtf _ -> "ltf"
  | CLeqf _ -> "leqf"
  | CGtf _ -> "gtf"
  | CGeqf _ -> "geqf"
  | CNeqf _ -> "neqf"
end

lang CharPrettyPrint = CharAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CChar c -> join ["\'", escapeChar c.val, "\'"]
end

lang CmpCharPrettyPrint = CmpCharAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CEqc _ -> "eqc"
end

lang IntCharConversionPrettyPrint = IntCharConversionAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CInt2Char _ -> "int2char"
  | CChar2Int _ -> "char2int"
end

lang FloatStringConversionPrettyPrint = FloatStringConversionAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CStringIsFloat _ -> "stringIsFloat"
  | CString2float _ -> "string2float"
  | CFloat2string _ -> "float2string"
end

lang SymbPrettyPrint = SymbAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CSymb _ -> "sym"
  | CGensym _ -> "gensym"
  | CSym2hash _ -> "sym2hash"
end

lang CmpSymbPrettyPrint = CmpSymbAst + ConstPrettyPrint
   sem getConstStringCode (indent : Int) =
   | CEqsym _ -> "eqsym"
end

lang SeqOpPrettyPrint = SeqOpAst + ConstPrettyPrint + CharAst
  sem getConstStringCode (indent : Int) =
  | CGet _ -> "get"
  | CSet _ -> "set"
  | CCons _ -> "cons"
  | CSnoc _ -> "snoc"
  | CConcat _ -> "concat"
  | CLength _ -> "length"
  | CReverse _ -> "reverse"
  | CHead _ -> "head"
  | CTail _ -> "tail"
  | CNull _ -> "null"
  | CMap _ -> "map"
  | CMapi _ -> "mapi"
  | CIter _ -> "iter"
  | CIteri _ -> "iteri"
  | CFoldl _ -> "foldl"
  | CFoldr _ -> "foldr"
  | CCreate _ -> "create"
  | CCreateList _ -> "createList"
  | CCreateRope _ -> "createRope"
  | CIsList _ -> "isList"
  | CIsRope _ -> "isRope"
  | CSplitAt _ -> "splitAt"
  | CSubsequence _ -> "subsequence"
end

lang FileOpPrettyPrint = FileOpAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CFileRead _ -> "readFile"
  | CFileWrite _ -> "writeFile"
  | CFileExists _ -> "fileExists"
  | CFileDelete _ -> "deleteFile"
end

lang IOPrettyPrint = IOAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CPrint _ -> "print"
  | CPrintError _ -> "printError"
  | CDPrint _ -> "dprint"
  | CFlushStdout _ -> "flushStdout"
  | CFlushStderr _ -> "flushStderr"
  | CReadLine _ -> "readLine"
  | CReadBytesAsString _ -> "readBytesAsString"
end

lang RandomNumberGeneratorPrettyPrint = RandomNumberGeneratorAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CRandIntU _ -> "randIntU"
  | CRandSetSeed _ -> "randSetSeed"
end

lang SysPrettyPrint = SysAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CExit _ -> "exit"
  | CError _ -> "error"
  | CArgv _ -> "argv"
  | CCommand _ -> "command"
end

lang TimePrettyPrint = TimeAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CWallTimeMs _ -> "wallTimeMs"
  | CSleepMs _ -> "sleepMs"
end

lang ConTagPrettyPrint = ConTagAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CConstructorTag _ -> "constructorTag"
end

lang RefOpPrettyPrint = RefOpAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CRef _ -> "ref"
  | CModRef _ -> "modref"
  | CDeRef _ -> "deref"
end

lang ConTagPrettyPrint = ConTagAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CConstructorTag _ -> "constructorTag"
end

lang TensorOpPrettyPrint = TensorOpAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CTensorCreateUninitInt _ -> "tensorCreateUninitInt"
  | CTensorCreateUninitFloat _ -> "tensorCreateUninitFloat"
  | CTensorCreateInt _ -> "tensorCreateCArrayInt"
  | CTensorCreateFloat _ -> "tensorCreateCArrayFloat"
  | CTensorCreate _ -> "tensorCreateDense"
  | CTensorGetExn _ -> "tensorGetExn"
  | CTensorSetExn _ -> "tensorSetExn"
  | CTensorLinearGetExn _ -> "tensorLinearGetExn"
  | CTensorLinearSetExn _ -> "tensorLinearSetExn"
  | CTensorRank _ -> "tensorRank"
  | CTensorShape _ -> "tensorShape"
  | CTensorReshapeExn _ -> "tensorReshapeExn"
  | CTensorCopy _ -> "tensorCopy"
  | CTensorTransposeExn _ -> "tensorTransposeExn"
  | CTensorSliceExn _ -> "tensorSliceExn"
  | CTensorSubExn _ -> "tensorSubExn"
  | CTensorIterSlice _ -> "tensorIterSlice"
  | CTensorEq _ -> "tensorEq"
  | CTensorToString _ -> "tensor2string"
end

lang BootParserPrettyPrint = BootParserAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CBootParserParseMExprString _ -> "bootParserParseMExprString"
  | CBootParserParseMCoreFile _ -> "bootParserParseMCoreFile"
  | CBootParserGetId _ -> "bootParserGetId"
  | CBootParserGetTerm _ -> "bootParserGetTerm"
  | CBootParserGetType _ -> "bootParserGetType"
  | CBootParserGetString _ -> "bootParserGetString"
  | CBootParserGetInt _ -> "bootParserGetInt"
  | CBootParserGetFloat _ -> "bootParserGetFloat"
  | CBootParserGetListLength _ -> "bootParserGetListLength"
  | CBootParserGetConst _ -> "bootParserGetConst"
  | CBootParserGetPat _ -> "bootParserGetPat"
  | CBootParserGetInfo _ -> "bootParserGetInfo"
end

--------------
-- PATTERNS --
--------------

lang PatNamePrettyPrint = IdentifierPrettyPrint
  sem _pprint_patname (env : PprintEnv) =
  | PName name ->
    pprintVarName env name
  | PWildcard () -> (env, "_")
end

lang NamedPatPrettyPrint = NamedPat + PatNamePrettyPrint
  sem patIsAtomic =
  | PatNamed _ -> true

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PatNamed {ident = patname} -> _pprint_patname env patname
end

let _pprint_patseq: (Int -> PprintEnv -> Pat -> (PprintEnv, String)) -> Int ->
                    PprintEnv -> [Pat] -> (PprintEnv, String) =
lam recur. lam indent. lam env. lam pats.
  use CharPat in
  let extract_char = lam e.
    match e with PatChar c then Some c.val
    else None () in
  match optionMapM extract_char pats with Some str then
    (env, join ["\"", escapeString str, "\""])
  else match mapAccumL (recur (pprintIncr indent)) env pats
  with (env, pats) in
  let merged =
    strJoin (concat "," (pprintNewline (pprintIncr indent))) pats in
  (env, join ["[ ", merged, " ]"])

lang SeqTotPatPrettyPrint = SeqTotPat + CharPat
  sem patIsAtomic =
  | PatSeqTot _ -> true

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | PatSeqTot {pats = pats} -> _pprint_patseq getPatStringCode indent env pats
end

lang SeqEdgePatPrettyPrint = SeqEdgePat + PatNamePrettyPrint
  sem patIsAtomic =
  | PatSeqEdge _ -> false

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | PatSeqEdge {prefix = pre, middle = patname, postfix = post} ->
    match _pprint_patseq getPatStringCode indent env pre with (env, pre) in
    match _pprint_patname env patname with (env, pname) in
    match _pprint_patseq getPatStringCode indent env post with (env, post) in
      (env, join [pre, " ++ ", pname, " ++ ", post])
end

lang RecordPatPrettyPrint = RecordPat + IdentifierPrettyPrint
  sem patIsAtomic =
  | PatRecord _ -> true

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PatRecord {bindings = bindings} ->
    if mapIsEmpty bindings then (env, "{}")
    else match record2tuple bindings with Some pats then
      match mapAccumL (lam env. lam e. getPatStringCode indent env e) env pats
      with (env, tuplePats) in
      let merged =
        match tuplePats with [e]
        then concat e ","
        else strJoin ", " tuplePats in
      (env, join ["(", merged, ")"])
    else match
      mapMapAccum
        (lam env. lam k. lam v.
           match getPatStringCode indent env v with (env,str) in
           (env,join [pprintLabelString k, " = ", str]))
         env bindings
    with (env,bindMap) in
    (env,join ["{", strJoin ", " (mapValues bindMap), "}"])
end

lang DataPatPrettyPrint = DataPat + IdentifierPrettyPrint
  sem patIsAtomic =
  | PatCon _ -> false

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PatCon t ->
    match pprintConName env t.ident with (env,str) in
    match getPatStringCode indent env t.subpat with (env,subpat) in
    let subpat = if patIsAtomic t.subpat then subpat
                 else join ["(", subpat, ")"]
    in (env, join [str, " ", subpat])
end

lang IntPatPrettyPrint = IntPat
  sem patIsAtomic =
  | PatInt _ -> true

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PatInt t -> (env, int2string t.val)
end

lang CharPatPrettyPrint = CharPat
  sem patIsAtomic =
  | PatChar _ -> true

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PatChar t -> (env, join ["\'", escapeChar t.val, "\'"])
end

lang BoolPatPrettyPrint = BoolPat
  sem patIsAtomic =
  | PatBool _ -> true

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PatBool b -> (env, if b.val then "true" else "false")
end

lang AndPatPrettyPrint = PrettyPrint + AndPat
  sem patIsAtomic =
  | PatAnd _ -> false

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | PatAnd {lpat = l, rpat = r} ->
    match printPatParen indent env l with (env, l2) in
    match printPatParen indent env r with (env, r2) in
    (env, join [l2, " & ", r2])
end

lang OrPatPrettyPrint = PrettyPrint + OrPat
  sem patIsAtomic =
  | PatOr _ -> false

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | PatOr {lpat = l, rpat = r} ->
    match printPatParen indent env l with (env, l2) in
    match printPatParen indent env r with (env, r2) in
    (env, join [l2, " | ", r2])
end

lang NotPatPrettyPrint = PrettyPrint + NotPat
  sem patIsAtomic =
  | PatNot _ -> false  -- OPT(vipa, 2020-09-23): this could possibly be true, just because it binds stronger than everything else

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | PatNot {subpat = p} ->
    match printPatParen indent env p with (env, p2) in
    (env, join ["!", p2])
end

-----------
-- TYPES --
-----------

lang UnknownTypePrettyPrint = UnknownTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyUnknown _ -> (env,"Unknown")
end

lang BoolTypePrettyPrint = BoolTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyBool _ -> (env,"Bool")
end

lang IntTypePrettyPrint = IntTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyInt _ -> (env,"Int")
end

lang FloatTypePrettyPrint = FloatTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyFloat _ -> (env,"Float")
end

lang CharTypePrettyPrint = CharTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyChar _ -> (env,"Char")
end

lang FunTypePrettyPrint = PrettyPrint + FunTypeAst
  sem typePrecedence =
  | TyArrow _ -> 0

  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyArrow t ->
    match printTypeParen indent 1 env t.from with (env, from) in
    match getTypeStringCode indent env t.to with (env, to) in
    (env, join [from, " -> ", to])
end

lang SeqTypePrettyPrint = SeqTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TySeq t ->
    match getTypeStringCode indent env t.ty with (env, ty) in
    (env, join ["[", ty, "]"])
end

lang TensorTypePrettyPrint = TensorTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyTensor t ->
    match getTypeStringCode indent env t.ty with (env, ty) in
    (env, join ["Tensor[", ty, "]"])
end

lang RecordTypePrettyPrint = IdentifierPrettyPrint + RecordTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | (TyRecord t) & ty ->
    if mapIsEmpty t.fields then (env,"()") else
      let orderedFields = tyRecordOrderedFields ty in
      let tuple =
        let seq = map (lam b : (SID,Type). (sidToString b.0, b.1)) orderedFields in
        if forAll (lam t : (String,Type). stringIsInt t.0) seq then
          let seq = map (lam t : (String,Type). (string2int t.0, t.1)) seq in
          let seq : [(Int,Type)] = sort (lam l : (Int,Type). lam r : (Int,Type). subi l.0 r.0) seq in
          let fst = lam x: (Int, Type). x.0 in
          let first = fst (head seq) in
          let last = fst (last seq) in
          if eqi first 0 then
            if eqi last (subi (length seq) 1) then
              Some (map (lam t : (Int,Type). t.1) seq)
            else None ()
          else None ()
        else None ()
      in
      match tuple with Some tuple then
        match mapAccumL (getTypeStringCode indent) env tuple with (env, tuple) in
        let singletonComma = match tuple with [_] then "," else "" in
        (env, join ["(", strJoin ", " tuple, singletonComma, ")"])
      else
        let f = lam env. lam field.
          match field with (sid, ty) in
          match getTypeStringCode indent env ty with (env, tyStr) in
          (env, (sid, tyStr))
        in
        match mapAccumL f env orderedFields with (env, fields) in
        let fields =
          map (lam b : (SID,String). (pprintLabelString b.0, b.1)) fields in
        let conventry = lam entry : (String,String). join [entry.0, ": ", entry.1] in
        (env,join ["{", strJoin ", " (map conventry fields), "}"])
end

lang VariantTypePrettyPrint = VariantTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyVariant t ->
    if eqi (mapLength t.constrs) 0 then (env,"<>")
    else (env, join ["Variant<", strJoin ", " (map nameGetStr (mapKeys t.constrs)), ">"])
    -- NOTE(wikman, 2022-04-04): This pretty printing above is just temporary
    -- as we do not have syntax for TyVariant. It is necessary however since we
    -- still use TyVariant in the AST and might get compilation errors for it.
end

lang ConTypePrettyPrint = IdentifierPrettyPrint + ConTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyCon t ->
    pprintTypeName env t.ident
end

lang VarTypePrettyPrint = IdentifierPrettyPrint + VarTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyVar t ->
    pprintVarName env t.ident
end

lang VarSortPrettyPrint = PrettyPrint + RecordTypeAst + VarSortAst
  sem getVarSortStringCode (indent : Int) (env : PprintEnv) (idstr : String) =
  | RecordVar r ->
    let recty = TyRecord {info = NoInfo (), fields = r.fields} in
    match getTypeStringCode indent env recty with (env, recstr) in
    (env, join [init recstr, " ... ", [last recstr]])
  | _ -> (env, idstr)
end

lang AllTypePrettyPrint = IdentifierPrettyPrint + AllTypeAst + VarSortPrettyPrint
  sem typePrecedence =
  | TyAll _ -> 0

  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyAll t ->
    match pprintVarName env t.ident with (env, idstr) in
    match getVarSortStringCode indent env idstr t.sort with (env, varstr) in
    match getTypeStringCode indent env t.ty with (env, tystr) in
    (env, join ["all ", varstr, ". ", tystr])
end

lang AppTypePrettyPrint = PrettyPrint + AppTypeAst
  sem typePrecedence =
  | TyApp _ -> 1

  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyApp t ->
    match printTypeParen indent 1 env t.lhs with (env,lhs) in
    match printTypeParen indent 2 env t.rhs with (env,rhs) in
    (env, join [lhs, " ", rhs])
end

lang AliasTypePrettyPrint = PrettyPrint + AliasTypeAst
  sem typePrecedence =
  | TyAlias t -> typePrecedence t.display

  sem getTypeStringCode (indent : Int) (env : PprintEnv) =
  | TyAlias t -> getTypeStringCode indent env t.display
end


---------------------------
-- MEXPR PPRINT FRAGMENT --
---------------------------

let mexprKeywords =
  let intrinsicStrs = map (lam e. match e with (str, _) in str) builtin in
  join [mexprBuiltInKeywords, intrinsicStrs, mexprExtendedKeywords]

lang MExprPrettyPrint =

  -- Terms
  VarPrettyPrint + AppPrettyPrint + LamPrettyPrint + RecordPrettyPrint +
  LetPrettyPrint + TypePrettyPrint + RecLetsPrettyPrint + ConstPrettyPrint +
  DataPrettyPrint + MatchPrettyPrint + UtestPrettyPrint + SeqPrettyPrint +
  NeverPrettyPrint + ExtPrettyPrint +

  -- Constants
  IntPrettyPrint + ArithIntPrettyPrint + ShiftIntPrettyPrint +
  FloatPrettyPrint + ArithFloatPrettyPrint + FloatIntConversionPrettyPrint +
  BoolPrettyPrint + CmpIntPrettyPrint + CmpFloatPrettyPrint + CharPrettyPrint +
  CmpCharPrettyPrint + IntCharConversionPrettyPrint +
  FloatStringConversionPrettyPrint + SymbPrettyPrint + CmpSymbPrettyPrint +
  SeqOpPrettyPrint + FileOpPrettyPrint + IOPrettyPrint +
  RandomNumberGeneratorPrettyPrint + SysPrettyPrint + TimePrettyPrint +
  ConTagPrettyPrint + RefOpPrettyPrint + TensorOpPrettyPrint +
  BootParserPrettyPrint + UnsafeCoercePrettyPrint +

  -- Patterns
  NamedPatPrettyPrint + SeqTotPatPrettyPrint + SeqEdgePatPrettyPrint +
  RecordPatPrettyPrint + DataPatPrettyPrint + IntPatPrettyPrint +
  CharPatPrettyPrint + BoolPatPrettyPrint + AndPatPrettyPrint +
  OrPatPrettyPrint + NotPatPrettyPrint +

  -- Types
  UnknownTypePrettyPrint + BoolTypePrettyPrint + IntTypePrettyPrint +
  FloatTypePrettyPrint + CharTypePrettyPrint + FunTypePrettyPrint +
  SeqTypePrettyPrint + RecordTypePrettyPrint + VariantTypePrettyPrint +
  ConTypePrettyPrint + VarTypePrettyPrint +
  AppTypePrettyPrint + TensorTypePrettyPrint + AllTypePrettyPrint +
  AliasTypePrettyPrint

  -- Identifiers
  + MExprIdentifierPrettyPrint

  -- Syntactic Sugar
  + RecordProjectionSyntaxSugarPrettyPrint

  sem mexprToString =
  | expr -> exprToStringKeywords mexprKeywords expr

end


-----------
-- TESTS --
-----------

mexpr
use MExprPrettyPrint in

let pchar = match_ (var_ "x") (pchar_ '\n') (true_) (false_) in
utest expr2str pchar with
"match
  x
with
  '\\n'
then
  true
else
  false" in

let cons_ = appf2_ (var_ "cons") in
let concat_ = appf2_ (var_ "concat") in

-- let foo = lam a. lam b.
--     let bar = lam x. addi b x in
--     let babar = 3 in
--     addi (bar babar) a
-- in
let func_foo =
  ulet_ "foo" (
    lam_ "a" tyunknown_ (
      lam_ "b" tyunknown_ (
        bindall_ [
          ulet_ "bar" (
            lam_ "x" tyunknown_ (
              addi_ (var_ "b") (var_ "x")
            )
          ),
          ulet_ "babar" (int_ 3),
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
    ureclets_add "factorial"
        (lam_ "n" (tyint_)
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
    ureclets_add "even"
        (lam_ "x" tyunknown_
            (if_ (eqi_ (var_ "x") (int_ 0))
                 (true_)
                 (not_ (app_ (var_ "odd")
                             (subi_ (var_ "x") (int_ 1))))))
    (ureclets_add "odd"
        (lam_ "x" tyunknown_
            (if_ (eqi_ (var_ "x") (int_ 1))
                 (true_)
                 (not_ (app_ (var_ "even")
                             (subi_ (var_ "x") (int_ 1))))))
    reclets_empty)
in


-- let recget = {i = 5, s = "hello!"} in
let func_recget =
    ulet_ "recget" (
        record_add "i" (int_ 5) (
        record_add "s" (str_ "hel\nlo!")
        urecord_empty))
in

-- let recconcs = lam rec. lam s. {rec with s = concat rec.s s} in
let func_recconcs =
    ulet_ "recconcs" (lam_ "rec" tyunknown_ (lam_ "s" (tystr_) (
        recordupdate_ (var_ "rec")
                      "s"
                      (concat_ (recordproj_ "s" (var_ "rec"))
                               (var_ "s")))))
in

-- con MyConA in
let func_mycona = ucondef_ "MyConA" in

-- con #con"myConB" : (Bool, Int) in
let func_myconb = condef_ "myConB" (tytuple_ [tybool_, tyint_]) in

-- con MyConA1 in
-- con MyConA2
let func_mycona_mycona =
  let n1 = nameSym "MyConA" in
  let n2 = nameSym "MyConA" in
  bindall_ [nucondef_ n1, nucondef_ n2]
in

-- let isconb : Bool = lam c : #con"myConB".
--     match c with #con"myConB" (true, 17) then
--         true
--     else
--         false
let func_isconb =
    ulet_ "isconb" (
        lam_ "c" (tycon_ "myConBType") (
            match_ (var_ "c")
                   (pcon_ "myConB" (ptuple_ [ptrue_, pint_ 17]))
                   (true_)
                   (false_)))
in

-- let addone : Int -> Int = lam i : Int. (lam x : Int. addi x 1) i
let func_addone =
  ulet_ "addone" (
      lam_ "i" (tyint_) (
        app_ (lam_ "x" (tyint_) (addi_ (var_ "x") (int_ 1)))
             (var_ "i")
      )
  )
in

-- let beginsWithBinaryDigit : String -> Bool = lam s : String.
--   match s with ['0' | '1'] ++ _ then true else false
let func_beginsWithBinaryDigit =
  ulet_ "beginsWithBinaryDigit" (
    lam_ "s" (tystr_) (
      match_ (var_ "s")
             (pseqedgew_
               [por_ (pchar_ '0') (pchar_ '1')]
               [])
             (true_)
             (false_)
    )
  )
in

-- let pedanticIsSome : all a. Option a -> Bool = lam o : Option a.
--   match o with !(None ()) & Some _ then true else false
let func_pedanticIsSome =
  let_ "pedanticIsSome"
    (tyall_ "a" (tyarrow_ (tyapp_ (tycon_ "Option") (tyvar_ "a")) tybool_)) (
      lam_ "s" (tyapp_ (tycon_ "Option") (tyvar_ "a")) (
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
  ulet_ "is123" (
    lam_ "l" (tyseq_ tyint_) (
      match_ (var_ "l")
             (pseqtot_ [pint_ 1, pint_ 2, pint_ 3])
             (true_)
             (false_)
    )
  )
in

-- let var = 1 in let var1 = 2 in addi var var1
let n1 = nameSym "var" in
let n2 = nameSym "var" in
let var_var =
  bindall_ [nulet_ n1 (int_ 1), nulet_ n2 (int_ 2), addi_ (nvar_ n1) (nvar_ n2)]
in

-- let #var"" = 1 in let #var"1" = 2 in addi #var"" #var"1"
let n1 = nameSym "" in
let n2 = nameSym "" in
let empty_empty =
  bindall_ [nulet_ n1 (int_ 1), nulet_ n2 (int_ 2), addi_ (nvar_ n1) (nvar_ n2)]
in

-- external addi : Int -> Int -> Int in addi
let external_addi =
  bind_ (ext_ "addi" false (tyarrows_ [tyint_, tyint_, tyint_])) (var_ "addi")
in

-- external addi !: Int -> Int -> Int in addi
let external_addi_effect =
  bind_ (ext_ "addi" true (tyarrows_ [tyint_, tyint_, tyint_])) (var_ "addi")
in

let sample_ast =
  bindall_ [
    func_foo,
    func_factorial,
    funcs_evenodd,
    func_recget,
    func_recconcs,
    func_mycona,
    func_mycona_mycona,
    func_myconb,
    func_isconb,
    func_addone,
    func_beginsWithBinaryDigit,
    func_pedanticIsSome,
    func_is123,
    var_var,
    empty_empty,
    external_addi,
    external_addi_effect
  ]
in

-- print "\n\n";
-- print (expr2str sample_ast);
-- print "\n\n";

utest length (expr2str sample_ast) with 0 using geqi in

-- Test keyword variable names
utest eqString (mexprToString (var_ "lam")) "lam"
with false in

()