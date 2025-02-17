-- Instruments performance profiling into a given AST. The profiling is
-- instrumented on every let-expression and recursive binding defined on the
-- top-level, whose body is a lambda term.
--
-- At the end of the AST, code is instrumented for storing the profiling
-- results in a file 'mexpr.prof'. This file will contain one line for every
-- top-level function that was called at least once during the execution of the
-- program. The contents of a line are the following space-separated values:
-- 1. The name of the file and the position within the file where the function
--    is defined.
-- 2. The name of the function.
-- 3. The number of calls made to the function, including self-recursive calls.
-- 4. The exclusive time spent within the function - this excludes the time
--    spent in its calls to other top-level functions.
-- 5. The inclusive time of the function.
--
-- Known limitations:
-- * The file to which the profiling results are stored is currently hard-coded
--   as 'mexpr.prof'.
-- * Only functions defined on the top-level are profiled.
-- * Prevents the OCaml compiler from doing tail-call optimizations.
-- * A partially applied function, such as x in `let x = head`, is not profiled
--   because its body is not a lambda term.

include "mexpr/ast.mc"
include "mexpr/boot-parser.mc"
include "mexpr/eval.mc"
include "mexpr/symbolize.mc"

include "sys.mc"

type ProfileEnv = Map Name (Int, Info)

let profilingResultFileName = "mexpr.prof"

let _profilerInitStr : Map Name (Int, Info) -> String = lam env.
  let envStrs : Map Name (String, Int) =
    mapMapWithKey
      (lam k. lam v : (Int, Info).
        let idx = v.0 in
        let info = v.1 in
        let str =
          match info with Info t then
            join [t.filename, "[", int2string t.row1, ":", int2string t.col1,
                  "-", int2string t.row2, ":", int2string t.col2, "] ",
                  nameGetStr k]
          else join ["? ", nameGetStr k] in
        (str, v.0))
      env in
  let orderedFunctionStrs : [String] =
    map
      (lam x : (String, Int). x.0)
      (sort
        (lam l : (String, Int). lam r : (String, Int). subi l.1 r.1)
        (mapValues envStrs)) in
  let functionProfileData =
    join
      [ "let functionProfileData = [\n"
      , strJoin ",\n"
          (map
            (lam functionStr.
              join ["  ref {emptyProfileData with id = \"", functionStr, "\"}"])
            orderedFunctionStrs)
      , "] in"] in
  join [
"type StackEntry = {
  onTopSince : Float,
  pushedAt : Float,
  functionIndex : Int
} in

type ProfileData = {
  id : String,
  exclusiveTime : Float,
  inclusiveTime : Float,
  calls : Int
} in

let emptyProfileData = {id = \"\", exclusiveTime = 0.0, inclusiveTime = 0.0,
                        calls = 0} in

let callStack : Ref [StackEntry] =
  ref (createList 0 (lam. {onTopSince = 0.0, pushedAt = 0.0,
                           functionIndex = 0})) in
",
functionProfileData,
"
let addExclusiveTime : Float -> StackEntry -> () =
  lam t. lam entry.
  let dataRef = get functionProfileData entry.functionIndex in
  let data : ProfileData = deref dataRef in
  let addedTime = subf t entry.onTopSince in
  modref dataRef {data with exclusiveTime = addf data.exclusiveTime addedTime}
in

let addInclusiveTime : Float -> StackEntry -> () =
  lam t. lam entry.
  let dataRef = get functionProfileData entry.functionIndex in
  let data : ProfileData = deref dataRef in
  let addedTime = subf t entry.pushedAt in
  modref dataRef {data with inclusiveTime = addf data.inclusiveTime addedTime}
in

let incrementCallCount : Int -> () = lam index.
  let dataRef = get functionProfileData index in
  let data : ProfileData = deref dataRef in
  modref dataRef {data with calls = addi data.calls 1}
in

let pushCallStack : Int -> () = lam index.
  let stack = deref callStack in
  let t = wallTimeMs () in
  let pushEntry = lam.
    incrementCallCount index;
    let entry = {onTopSince = t, pushedAt = t, functionIndex = index} in
    cons entry stack
  in
  let stack =
    if null stack then pushEntry ()
    else
      let prevTopEntry = head stack in
      addExclusiveTime t prevTopEntry;
      pushEntry ()
  in
  modref callStack stack
in

let popCallStack : () -> () = lam.
  let stack = deref callStack in
  if null stack then error \"Attempted to pop empty call stack\"
  else
    let t = wallTimeMs () in
    let prevTopEntry = head stack in
    addExclusiveTime t prevTopEntry;
    addInclusiveTime t prevTopEntry;
    let tl = tail stack in
    let stack =
      if null tl then tl
      else
        let newHead : StackEntry = head tl in
        cons {newHead with onTopSince = t} (tail tl)
    in
    modref callStack stack
in

()
"]

let _profilerReportStr = join ["
let int2string = lam n.
  recursive
  let int2string_rechelper = lam n.
    if lti n 10
    then [int2char (addi n (char2int '0'))]
    else
      let d = [int2char (addi (modi n 10) (char2int '0'))] in
      concat (int2string_rechelper (divi n 10)) d
  in
  if lti n 0
  then cons '-' (int2string_rechelper (negi n))
  else int2string_rechelper n
in
recursive let filter = lam p. lam seq.
  if null seq then []
  else if p (head seq) then cons (head seq) (filter p (tail seq))
  else filter p (tail seq)
in
let join = foldl concat [] in
let data =
  filter
    (lam entryRef : Ref ProfileData.
      let entry : ProfileData = deref entryRef in
      gti entry.calls 0)
    functionProfileData in
writeFile
  \"", profilingResultFileName, "\"
  (join
    (map
      (lam dataRef : Ref ProfileData.
        let data : ProfileData = deref dataRef in
        let exclusiveTime = divf data.exclusiveTime 1000.0 in
        let inclusiveTime = divf data.inclusiveTime 1000.0 in
        join [data.id, \" \", int2string data.calls, \" \",
              float2string exclusiveTime, \" \", float2string inclusiveTime,
              \"\\n\"])
      data))
"]

let _profilerReportCodeRef = ref (None ())
let getProfilerReportCode = lam.
  match deref _profilerReportCodeRef with Some t then t
  else
    use BootParser in
    let code = parseMExprStringKeywordsExn ["functionProfileData"] _profilerReportStr in
    modref _profilerReportCodeRef (Some code);
    code

lang MExprProfileInstrument = MExprAst + BootParser
  sem collectToplevelFunctions (env : ProfileEnv) =
  | TmLet t ->
    let env =
      match t.body with TmLam _ then
        let idx = mapSize env in
        mapInsert t.ident (idx, t.info) env
      else env in
    collectToplevelFunctions env t.inexpr
  | TmRecLets t ->
    let collectBinding : ProfileEnv -> RecLetBinding -> ProfileEnv =
      lam env. lam binding.
      match binding.body with TmLam _ then
        let idx = mapSize env in
        mapInsert binding.ident (idx, binding.info) env
      else env
    in
    let env = foldl collectBinding env t.bindings in
    collectToplevelFunctions env t.inexpr
  | t -> sfold_Expr_Expr collectToplevelFunctions env t

  sem instrumentProfilingCalls (functionIndex : Int) =
  | TmLam t ->
    TmLam {t with body = instrumentProfilingCalls functionIndex t.body}
  | t ->
    bindall_ [
      ulet_ "" (app_ (var_ "pushCallStack") (int_ functionIndex)),
      ulet_ "tmp" t,
      ulet_ "" (app_ (var_ "popCallStack") unit_),
      var_ "tmp"]

  sem instrumentProfilingH (env : ProfileEnv) =
  | TmLet t ->
    match mapLookup t.ident env with Some (idx, _) then
      TmLet {{t with body = instrumentProfilingCalls idx t.body}
                with inexpr = instrumentProfilingH env t.inexpr}
    else TmLet {t with inexpr = instrumentProfilingH env t.inexpr}
  | TmRecLets t ->
    let instrumentBinding : RecLetBinding -> RecLetBinding =
      lam binding.
      match mapLookup binding.ident env with Some (idx, _) then
        {binding with body = instrumentProfilingCalls idx binding.body}
      else binding
    in
    TmRecLets {{t with bindings = map instrumentBinding t.bindings}
                  with inexpr = instrumentProfilingH env t.inexpr}
  | TmType t -> TmType {t with inexpr = instrumentProfilingH env t.inexpr}
  | TmConDef t -> TmConDef {t with inexpr = instrumentProfilingH env t.inexpr}
  | TmUtest t -> TmUtest {t with next = instrumentProfilingH env t.next}
  | TmExt t -> TmExt {t with inexpr = instrumentProfilingH env t.inexpr}
  | t -> t

  sem instrumentProfiling =
  | t ->
    let emptyEnv = mapEmpty nameCmp in
    let env = collectToplevelFunctions emptyEnv t in
    bindall_ [
      parseMExprStringKeywordsExn [] (_profilerInitStr env),
      ulet_ "" (instrumentProfilingH env t),
      getProfilerReportCode ()]
end

lang TestLang = MExprProfileInstrument + MExprSym + MExprEval
end

mexpr

use TestLang in

let t = bindall_ [
  ureclets_ [
    ("fact", ulam_ "n" (
      if_ (eqi_ (var_ "n") (int_ 0))
        (int_ 1)
        (muli_ (var_ "n") (app_ (var_ "fact") (subi_ (var_ "n") (int_ 1)))))),
    ("nonsense", ulam_ "n" (
      if_ (leqi_ (var_ "n") (int_ 0))
        (true_)
        (app_ (var_ "nonsense") (subi_ (var_ "n") (int_ 1)))))],
  ulet_ "f" (ulam_ "x" (app_ (var_ "fact") (addi_ (var_ "x") (int_ 3)))),
  app_ (var_ "f") (int_ 4)
] in
let t = instrumentProfiling t in
eval (evalCtxEmpty ()) (symbolize t);
utest fileExists profilingResultFileName with true in
(if fileExists profilingResultFileName then
  let lines =
    filter
      (lam line. gti (length line) 0)
      (strSplit "\n" (readFile profilingResultFileName)) in
  utest length lines with 2 in
  let lineTerms =
    map
      (lam line. strSplit " " line)
      lines in
  let fst = get lineTerms 0 in
  let snd = get lineTerms 1 in

  -- Function names
  utest get fst 1 with "fact" in
  utest get snd 1 with "f" in

  -- #calls
  utest string2int (get fst 2) with 8 in
  utest string2int (get snd 2) with 1 in

  -- Exclusive time spent in function
  utest string2float (get fst 3) with 0.0 using gtf in
  utest string2float (get snd 3) with 0.0 using gtf in

  -- Remove profiling file
  sysDeleteFile profilingResultFileName;
  ()
else ());

()
