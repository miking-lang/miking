-- input:
-- Map Name (Set (Name, Set Int))
-- Expr -> set of  (hole, set of contexts)

-- probably also prefix tree for producing switch statements

-- CallCtxEnv for id:s

include "ast.mc"

include "common.mc"
include "set.mc"
include "mexpr/symbolize.mc"
include "mexpr/boot-parser.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/utesttrans.mc"

type InstrumentationEnv = {
  -- Maps a name of a of measuring points to the set of holes and contexts that
  -- it depends on.
  dep : Map Name (Set (Name, Set Int)),

  -- Maps a name of a measuring point to its unique identifier.
  id : Map Name Int
}

let _instrumentationHeaderStr =
"
let log = ref [] in
let record = lam id. lam startTime. lam endTime.
  modref log (cons (id,startTime,endTime) (deref log))
in
()
"

let _instrumentationHeader =
  use BootParser in
  parseMExprString [] _instrumentationHeaderStr

let _instrumentationLogName =
  match findName "log" _instrumentationHeader with Some n then n
  else error "impossible"

let _instrumentationRecordName =
  match findName "record" _instrumentationHeader with Some n then n
  else error "impossible"

lang Instrumentation = LetAst
  sem instrument (env : InstrumentationEnv) =
  | TmLet ({ident = ident} & t) ->
    match mapLookup ident env.dep with Some holes then
      let id = mapFindExn ident env.id in
      let startName = nameSym "s" in
      let endName = nameSym "e" in
      bindall_
      [ nulet_ startName (wallTimeMs_ uunit_)
      , TmLet {t with inexpr = uunit_}
      , nulet_ endName (wallTimeMs_ uunit_)
      , nulet_ (nameSym "") (
          appf3_ (nvar_ _instrumentationRecordName) (int_ id)
             (nvar_ startName) (nvar_ endName))
      , instrument env t.inexpr
      ]
    else smap_Expr_Expr (instrument env) (TmLet t)
  | t -> smap_Expr_Expr (instrument env) t

end

lang TestLang = Instrumentation + HoleAst + BootParser + MExprSym +
                MExprPrettyPrint

mexpr

use TestLang in

let debug = true in

let debugPrintLn =
  if debug then printLn else ()
in

let parse = lam str.
  let ast = parseMExprString holeKeywords str in
  let ast = makeKeywords [] ast in
  symbolize ast
in

let str2name = lam str. lam expr.
  match findName str expr with Some name then name
  else error (concat "name not found: " str)
in

let createEnv = lam expr. lam env : [(String,[(String,[Int])])].
  let set1 : [(Name, Set (Name,Set Int))] =
    map (lam e : (String, [(String,[Int])]).
      (str2name e.0 expr,
       setOfSeq (map (lam e: (String, [Int]). (str2name e.0 expr, setOfSeq e.1)) e.1))
    ) env
  in
  let dep = mapFromSeq nameCmp set1 in
  let id = match mapMapAccum (
      lam acc. lam k. lam.
        (addi acc 1, acc)) 0 dep
    with (_, m) in m
  in
  { dep = dep, id = id }
in

let test = lam debug. lam expr. lam env.
  debugPrintLn "\n-------- ORIGINAL PROGRAM --------";
  debugPrintLn (expr2str expr);
  let res = instrument env expr in
  debugPrintLn "\n-------- INSTRUMENTED PROGRAM --------";
  debugPrintLn (expr2str res);
  debugPrintLn "";
  ()
in

let t = parse
"
let foo = lam x.
  let h = hole (Boolean {default = true}) in
  let a = sleepMs h in
  let b = sleepMs h in
  (a,b)
in
let bar = lam x. lam y.
  let h1 = hole (Boolean {default = true}) in
  let c = if h1 then 1 else 2 in
  c
in
foo ()
" in

utest test debug t (createEnv t
[ ("a",[("h",[1])])
, ("b",[("h",[1])])
, ("c",[("h1",[1])])
] ) with () in

()
