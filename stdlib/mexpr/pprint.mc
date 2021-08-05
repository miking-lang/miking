
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
  strings: Map String Int

}

-- TODO(dlunde,2020-09-29) Make it possible to debug the actual symbols

let pprintEnvEmpty = { nameMap = mapEmpty nameCmp,
                       count = mapEmpty cmpString,
                       strings = mapEmpty cmpString }


-- Look up the string associated with a name in the environment
let pprintEnvLookup : Name -> PprintEnv -> Option String = lam name. lam env : PprintEnv.
  match env with { nameMap = nameMap } then
    mapLookup name nameMap
  else never

-- Check if a string is free in the environment.
let pprintEnvFree : String -> PprintEnv -> Bool = lam str. lam env : PprintEnv.
  match env with { strings = strings } then
    not (mapMem str strings)
  else never

-- Add a binding to the environment
let pprintEnvAdd : Name -> String -> Int -> PprintEnv -> PprintEnv =
  lam name. lam str. lam i. lam env : PprintEnv.
    match env with {nameMap = nameMap, count = count, strings = strings} then
      let baseStr = nameGetStr name in
      let count = mapInsert baseStr i count in
      let nameMap = mapInsert name str nameMap in
      let strings = mapInsert str 0 strings in
      {nameMap = nameMap, count = count, strings = strings}
    else never

-- Get a string for the current name. Returns both the string and a new
-- environment.
let pprintEnvGetStr : PprintEnv -> Name -> (PprintEnv, String) =
  lam env : PprintEnv. lam name.
    match pprintEnvLookup name env with Some str then (env,str)
    else
      let baseStr = nameGetStr name in
      if pprintEnvFree baseStr env then (pprintEnvAdd name baseStr 1 env, baseStr)
      else
        match env with {count = count} then
          let start =
            match mapLookup baseStr count
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

-- Variable string parser translation
let pprintVarString = lam str.
  _parserStr str "#var" (lam str. isLowerAlphaOrUnderscore (head str))

-- Constructor string parser translation
let pprintConString = lam str.
  _parserStr str "#con" (lam str. isUpperAlpha (head str))
----------------------
-- HELPER FUNCTIONS --
----------------------

-- Get an optional list of tuple expressions for a record. If the record does
-- not represent a tuple, None () is returned.
let record2tuple
  : Map SID a
  -> Option [a]
  = lam bindings.
    let keys = map sidToString (mapKeys bindings) in
    match all stringIsInt keys with false then None () else
    let intKeys = map string2int keys in
    let sortedKeys = sort subi intKeys in
    -- Check if keys are a sequence 0..(n-1)
    match sortedKeys with [] then None ()
    else match sortedKeys with [h] ++ _ then
      if and (eqi 0 h)
             (eqi (subi (length intKeys) 1) (last sortedKeys)) then
        Some (map (lam key. mapLookupOrElse
                              (lam. error "Key not found")
                              (stringToSid (int2string key)) bindings)
                   sortedKeys)
      else None ()
    else never


-----------
-- TERMS --
-----------

lang IdentifierPrettyPrint
  sem pprintConName (env : PprintEnv) =
  sem pprintVarName (env : PprintEnv) =
  sem pprintLabelString =                  -- Label string parser translation for records
end

lang MExprIdentifierPrettyPrint = IdentifierPrettyPrint
  sem pprintConName (env: PprintEnv) =
  | name ->
    match pprintEnvGetStr env name with (env,str) then
      let s = pprintConString str in
      (env, s)
    else never

  sem pprintVarName (env: PprintEnv) =
  | name ->
    match pprintEnvGetStr env name with (env,str) then
      let s = pprintVarString str in
      (env, s)
    else never

  sem pprintLabelString =
  | sid -> _parserStr (sidToString sid) "#label" (lam str. isLowerAlphaOrUnderscore (head str))
end

lang PrettyPrint = IdentifierPrettyPrint
  sem isAtomic =
  -- Intentionally left blank
  sem patIsAtomic =
  -- Intentionally left blank

  sem pprintCode (indent : Int) (env: PprintEnv) =
  -- Intentionally left blank
  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  -- Intentionally left blank

  sem getTypeStringCode (indent : Int) (env : PprintEnv) =
  -- Intentionally left blank


  sem expr2str =
  | expr ->
    match pprintCode 0 pprintEnvEmpty expr with (_,str)
    then str else never

  sem type2str =
  | ty ->
    match getTypeStringCode 0 pprintEnvEmpty ty with (_,str)
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

  -- Helper function for printing parentheses (around patterns)
  sem printPatParen (indent : Int) (env : PprintEnv) =
  | pat ->
    let i = if patIsAtomic pat then indent else addi 1 indent in
    match getPatStringCode i env pat with (env, str) then
      if patIsAtomic pat then (env, str)
      else (env, join ["(", str, ")"])
    else never

end

lang VarPrettyPrint = PrettyPrint + VarAst
  sem isAtomic =
  | TmVar _ -> true

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmVar {ident = ident} ->
    match pprintVarName env ident with (env, str)
    then (env,str) else never
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

lang LamPrettyPrint = PrettyPrint + LamAst + UnknownTypeAst
  sem isAtomic =
  | TmLam _ -> false

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmLam t ->
    match pprintVarName env t.ident with (env,str) then
      match getTypeStringCode indent env t.tyIdent with (env, ty) then
        let ty = if eqString ty "Unknown" then "" else concat ": " ty in
        match pprintCode (pprintIncr indent) env t.body with (env,body) then
          (env,
           join ["lam ", str, ty, ".", pprintNewline (pprintIncr indent),
                 body])
        else never
      else never
    else never
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
      with (env,tupleExprs) then
        let merged = match tupleExprs with [e] then
                       concat e ","
                     else strJoin ", " tupleExprs in
        (env, join ["(", merged, ")"])
      else never
    else
      let innerIndent = pprintIncr (pprintIncr indent) in
      match
        mapMapAccum
          (lam env. lam k. lam v.
             match pprintCode innerIndent env v with (env, str) then
               (env,
                join [pprintLabelString k, " =", pprintNewline innerIndent,
                      str])
             else never)
           env bindings
      with (env, bindMap) then
        let binds = mapValues bindMap in
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
                   pprintLabelString t.key, " =", pprintNewline ii, value,
                   " }"])
      else never
    else never
end

lang LetPrettyPrint = PrettyPrint + LetAst + UnknownTypeAst
  sem isAtomic =
  | TmLet _ -> false

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmLet t ->
    match pprintVarName env t.ident with (env,str) then
      match pprintCode indent env t.inexpr with (env,inexpr) then
        match getTypeStringCode indent env t.tyBody with (env, ty) then
          let ty = if eqString ty "Unknown" then "" else concat ": " ty in
          if eqString (nameGetStr t.ident) "" then
             match printParen (pprintIncr indent) env t.body with (env,body)
             then
               (env, join [body, pprintNewline indent, ";", inexpr])
             else never
           else
             match pprintCode (pprintIncr indent) env t.body with (env,body)
             then
               (env,
                join ["let ", str, ty, " =", pprintNewline (pprintIncr indent),
                      body, pprintNewline indent,
                      "in", pprintNewline indent,
                      inexpr])
             else never
          else never
      else never
    else never
end

lang ExtPrettyPrint = PrettyPrint + ExtAst + UnknownTypeAst
  sem isAtomic =
  | TmExt _ -> false

  sem getTypeStringCode (indent : Int) (env : PprintEnv) =
  -- Intentionally left blank

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmExt t ->
    match pprintVarName env t.ident with (env,str) then
      match pprintCode indent env t.inexpr with (env,inexpr) then
        match getTypeStringCode indent env t.tyIdent with (env,ty) then
          let e = if t.effect then "!" else "" in
          (env,
           join ["external ", str, e, " : ", ty, pprintNewline indent,
                 "in", pprintNewline indent,
                 inexpr])
        else never
      else never
    else never
end

lang TypePrettyPrint = PrettyPrint + TypeAst + UnknownTypeAst
  sem isAtomic =
  | TmType _ -> false

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmType t ->
    match pprintEnvGetStr env t.ident with (env,str) then
      let ident = str in -- TODO(dlunde,2020-11-24): change to pprintTypeName
      match pprintCode indent env t.inexpr with (env,inexpr) then
        match getTypeStringCode indent env t.tyIdent with (env, tyIdent) then
          match t.tyIdent with TyUnknown _ then
            (env, join ["type ", ident, pprintNewline indent,
                         "in", pprintNewline indent,
                         inexpr])
          else
            (env, join ["type ", ident, " =", pprintNewline (pprintIncr indent),
                      tyIdent, pprintNewline indent,
                      "in", pprintNewline indent,
                      inexpr])
        else never
      else never
    else never
end

lang RecLetsPrettyPrint = PrettyPrint + RecLetsAst + UnknownTypeAst
  sem isAtomic =
  | TmRecLets _ -> false

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmRecLets t ->
    let i = indent in
    let ii = pprintIncr i in
    let iii = pprintIncr ii in
    let f = lam env. lam bind : RecLetBinding.
      match pprintVarName env bind.ident with (env,str) then
        match pprintCode iii env bind.body with (env,body) then
          match getTypeStringCode indent env bind.ty with (env, ty) then
            let ty = if eqString ty "Unknown" then "" else concat ": " ty in
            (env, join ["let ", str, ty, " =", pprintNewline iii, body])
          else never
        else never
      else never
    in
    match mapAccumL f env t.bindings with (env,bindings) then
      match pprintCode indent env t.inexpr with (env,inexpr) then
        match bindings with [] then (env, inexpr) else
        let bindings = strJoin (pprintNewline ii) bindings in
        (env,join ["recursive", pprintNewline ii,
                   bindings, pprintNewline i,
                   "in", pprintNewline i,
                   inexpr])
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

lang DataPrettyPrint = PrettyPrint + DataAst + UnknownTypeAst
  sem isAtomic =
  | TmConDef _ -> false
  | TmConApp _ -> false

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmConDef t ->
    match pprintConName env t.ident with (env,str) then
      match getTypeStringCode indent env t.tyIdent with (env, ty) then
        let ty = if eqString ty "Unknown" then "" else concat ": " ty in
        match pprintCode indent env t.inexpr with (env,inexpr) then
          (env,join ["con ", str, ty, " in", pprintNewline indent, inexpr])
        else never
      else never
    else never

  | TmConApp t ->
    match pprintConName env t.ident with (env,str) then
      match printParen (pprintIncr indent) env t.body with (env,body) then
        (env, join [str, pprintNewline (pprintIncr indent), body])
      else never
    else never
end

lang MatchPrettyPrint = PrettyPrint + MatchAst
  sem isAtomic =
  | TmMatch _ -> false

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  -- intentionally left blank

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmMatch t -> pprintTmMatchNormally indent env t

  sem pprintTmMatchNormally (indent : Int) (env: PprintEnv) =
  | t ->
    let t : { target : Expr
            , pat : Pat
            , thn : Expr
            , els : Expr
            , ty : Type
            , info : Info } = t in
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

lang RecordProjectionSyntaxSugarPrettyPrint = MatchPrettyPrint + RecordPat + NeverAst + NamedPat + VarAst
  sem pprintCode (indent : Int) (env: PprintEnv) =
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
        match printParen indent env expr with (env, expr) then
          (env, join [expr, ".", pprintLabelString fieldLabel])
        else never
      else pprintTmMatchNormally indent env t
    else pprintTmMatchNormally indent env t
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
    match optionMapM extract_char t.tms with Some str then
      (env, join ["\"", escapeString str, "\""])
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
  | TmNever _ -> (env,"never")
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
  | CChar {val = '\n'} -> "\\n"
  | CChar {val = '\t'} -> "\\t"
  | CChar {val = '\\'} -> "\\\\"
  | CChar {val = '\''} -> "\\'"
  | CChar {val = '\"'} -> "\\\""
  | CChar c -> ['\'', c.val, '\'']
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
  | CCreateFingerTree _ -> "createFingerTree"
  | CCreateList _ -> "createList"
  | CCreateRope _ -> "createRope"
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
  | CDPrint _ -> "dprint"
  | CFlushStdout _ -> "flushStdout"
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

lang RefOpPrettyPrint = RefOpAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CRef _ -> "ref"
  | CModRef _ -> "modref"
  | CDeRef _ -> "deref"
end

lang MapPrettyPrint = MapAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CMapEmpty _ -> "mapEmpty"
  | CMapInsert _ -> "mapInsert"
  | CMapRemove _ -> "mapRemove"
  | CMapFindWithExn _ -> "mapFind"
  | CMapFindOrElse _ -> "mapFindOrElse"
  | CMapFindApplyOrElse _ -> "mapFindApplyOrElse"
  | CMapBindings _ -> "mapBindings"
  | CMapSize _ -> "mapSize"
  | CMapMem _ -> "mapMem"
  | CMapAny _ -> "mapAny"
  | CMapMap _ -> "mapMap"
  | CMapMapWithKey _ -> "mapMapWithKey"
  | CMapFoldWithKey _ -> "mapFoldWithKey"
  | CMapEq _ -> "mapEq"
  | CMapCmp _ -> "mapCmp"
  | CMapGetCmpFun _ -> "mapGetCmpFun"
end

lang TensorOpPrettyPrint = TensorOpAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CTensorCreateInt _ -> "tensorCreateCArrayInt"
  | CTensorCreateFloat _ -> "tensorCreateCArrayFloat"
  | CTensorCreate _ -> "tensorCreateDense"
  | CTensorGetExn _ -> "tensorGetExn"
  | CTensorSetExn _ -> "tensorSetExn"
  | CTensorRank _ -> "tensorRank"
  | CTensorShape _ -> "tensorShape"
  | CTensorReshapeExn _ -> "tensorReshapeExn"
  | CTensorBlitExn _ -> "tensorBlitExn"
  | CTensorCopy _ -> "tensorCopy"
  | CTensorTransposeExn _ -> "tensorTransposeExn"
  | CTensorSliceExn _ -> "tensorSliceExn"
  | CTensorSubExn _ -> "tensorSubExn"
  | CTensorIterSlice _ -> "tensorIterSlice"
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
    match pprintVarName env name with (env, str)
    then (env,str) else never
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
    (env, join ["\"", str, "\""])
  else match mapAccumL (recur (pprintIncr indent)) env pats
  with (env, pats) then
    let merged =
      strJoin (concat "," (pprintNewline (pprintIncr indent))) pats in
    (env, join ["[ ", merged, " ]"])
  else never

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
    match _pprint_patseq getPatStringCode indent env pre with (env, pre) then
    match _pprint_patname env patname with (env, pname) then
    match _pprint_patseq getPatStringCode indent env post with (env, post) then
      (env, join [pre, " ++ ", pname, " ++ ", post])
    else never else never else never
end

lang RecordPatPrettyPrint = RecordPat + IdentifierPrettyPrint
  sem patIsAtomic =
  | PatRecord _ -> true

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PatRecord {bindings = bindings} ->
    if mapIsEmpty bindings then (env, "{}")
    else match record2tuple bindings with Some pats then
      match mapAccumL (lam env. lam e. getPatStringCode indent env e) env pats
      with (env, tuplePats) then
        let merged =
          match tuplePats with [e]
          then concat e ","
          else strJoin ", " tuplePats in
        (env, join ["(", merged, ")"])
      else never
    else match
      mapMapAccum
        (lam env. lam k. lam v.
           match getPatStringCode indent env v with (env,str) then
             (env,join [pprintLabelString k, " = ", str])
           else never)
         env bindings
    with (env,bindMap) then
      (env,join ["{", strJoin ", " (mapValues bindMap), "}"])
    else never
end

lang DataPatPrettyPrint = DataPat + IdentifierPrettyPrint
  sem patIsAtomic =
  | PatCon _ -> false

  sem getPatStringCode (indent : Int) (env: PprintEnv) =
  | PatCon t ->
    match pprintConName env t.ident with (env,str) then
      match getPatStringCode indent env t.subpat with (env,subpat) then
        let subpat = if patIsAtomic t.subpat then subpat
                     else join ["(", subpat, ")"]
        in (env, join [str, " ", subpat])
      else never
    else never
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
    match printPatParen indent env l with (env, l2) then
    match printPatParen indent env r with (env, r2) then
    (env, join [l2, " & ", r2])
    else never else never
end

lang OrPatPrettyPrint = PrettyPrint + OrPat
  sem patIsAtomic =
  | PatOr _ -> false

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | PatOr {lpat = l, rpat = r} ->
    match printPatParen indent env l with (env, l2) then
    match printPatParen indent env r with (env, r2) then
    (env, join [l2, " | ", r2])
    else never else never
end

lang NotPatPrettyPrint = PrettyPrint + NotPat
  sem patIsAtomic =
  | PatNot _ -> false  -- OPT(vipa, 2020-09-23): this could possibly be true, just because it binds stronger than everything else

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | PatNot {subpat = p} ->
    match printPatParen indent env p with (env, p2) then
    (env, join ["!", p2])
    else never
end

-----------
-- TYPES --
-----------
-- TODO(dlunde,2020-11-24): Type printing is using a lot of unnecessary
-- parentheses.

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

lang FunTypePrettyPrint = FunTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyArrow t ->
    match getTypeStringCode indent env t.from with (env, from) then
      match getTypeStringCode indent env t.to with (env, to) then
        (env, join ["(", from, ") -> (", to, ")"])
      else never
    else never
end

lang SeqTypePrettyPrint = SeqTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TySeq t ->
    match getTypeStringCode indent env t.ty with (env, ty) then
      (env, join ["[", ty, "]"])
    else never
end

lang TensorTypePrettyPrint = TensorTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyTensor t ->
    match getTypeStringCode indent env t.ty with (env, ty) then
      (env, join ["Tensor[", ty, "]"])
    else never
end

lang RecordTypePrettyPrint = RecordTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyRecord t ->
    if mapIsEmpty t.fields then (env,"()") else
      let tuple =
        let seq = map (lam b : (a,b). (sidToString b.0, b.1)) (mapBindings t.fields) in
        if all (lam t : (a,b). stringIsInt t.0) seq then
          let seq = map (lam t : (a,b). (string2int t.0, t.1)) seq in
          let seq : [(a,b)] = sort (lam l : (a,b). lam r : (a,b). subi l.0 r.0) seq in
          let fst = lam x: (a, b). x.0 in
          let first = fst (head seq) in
          let last = fst (last seq) in
          if eqi first 0 then
            if eqi last (subi (length seq) 1) then
              Some (map (lam t : (a,b). t.1) seq)
            else None ()
          else None ()
        else None ()
      in
      match tuple with Some tuple then
        match mapAccumL (getTypeStringCode indent) env tuple with (env, tuple)
        then (env, join ["(", strJoin ", " tuple, ")"])
        else never
      else
        let f = lam env. lam. lam v. getTypeStringCode indent env v in
        match mapMapAccum f env t.fields with (env, fields) then
          let fields =
            map (lam b : (a,b). (sidToString b.0, b.1)) (mapBindings fields) in
          let conventry = lam entry : (a,b). join [entry.0, ": ", entry.1] in
          (env,join ["{", strJoin ", " (map conventry fields), "}"])
        else never
end

lang VariantTypePrettyPrint = VariantTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyVariant t ->
    if eqi (mapLength t.constrs) 0 then (env,"<>")
    else error "Printing of non-empty variant types not yet supported"
end

lang VarTypePrettyPrint = VarTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyVar t ->
    match pprintEnvGetStr env t.ident with (env,str)
    then (env, str) else never -- TODO(vipa, 2020-09-23): format properly with #type
end

lang AppTypePrettyPrint = AppTypeAst
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyApp t ->
    match getTypeStringCode indent env t.lhs with (env,lhs) then
      match getTypeStringCode indent env t.rhs with (env,rhs) then
        (env,join ["(", lhs, ") (", rhs, ")"])
      else never
    else never
end


---------------------------
-- MEXPR PPRINT FRAGMENT --
---------------------------

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
  RefOpPrettyPrint + MapPrettyPrint + TensorOpPrettyPrint +
  BootParserPrettyPrint +

  -- Patterns
  NamedPatPrettyPrint + SeqTotPatPrettyPrint + SeqEdgePatPrettyPrint +
  RecordPatPrettyPrint + DataPatPrettyPrint + IntPatPrettyPrint +
  CharPatPrettyPrint + BoolPatPrettyPrint + AndPatPrettyPrint +
  OrPatPrettyPrint + NotPatPrettyPrint +

  -- Types
  UnknownTypePrettyPrint + BoolTypePrettyPrint + IntTypePrettyPrint +
  FloatTypePrettyPrint + CharTypePrettyPrint + FunTypePrettyPrint +
  SeqTypePrettyPrint + RecordTypePrettyPrint + VariantTypePrettyPrint +
  VarTypePrettyPrint + AppTypePrettyPrint + TensorTypePrettyPrint

  -- Identifiers
  + MExprIdentifierPrettyPrint

  -- Syntactic Sugar
  + RecordProjectionSyntaxSugarPrettyPrint

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
        lam_ "c" (tyvar_ "myConBType") (
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

-- let pedanticIsSome : Option a -> Bool = lam o : Option a.
--   match o with !(None ()) & Some _ then true else false
let func_pedanticIsSome =
  ulet_ "pedanticIsSome" (
    lam_ "s" (tyapp_ (tyvar_ "Option") (tyvar_ "a")) (
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

()
