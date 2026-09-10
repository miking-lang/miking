-- Selecting pure runtime intrinsics to append to a generated module.
--
-- Runtime intrinsics are named with a leading `$`. The name allocator in
-- `ident.mc` maps every non-alphanumeric character to `_`, so it can never
-- produce a `$` -- which means a runtime name can never collide with a
-- compiled MExpr binding, with no reserved-word list to keep in sync.
--
-- `runtime/mexpr.mjs` is hand-written JavaScript holding the intrinsics that
-- cannot be inlined as JS operators. This module reads it, splits it on its
-- `//!intrinsic` markers, and emits only the definitions a program actually
-- uses -- appended after `main`, so the program reads first and the runtime
-- stays out of the way.

include "bool.mc"
include "basic-types.mc"
include "option.mc"
include "ecmascript/ast.mc"
include "map.mc"
include "seq.mc"
include "set.mc"
include "stdlib.mc"
include "string.mc"

lang ESRuntime = ESAst

  -- The runtime helpers a program actually refers to.
  -- Runtime helpers are the globals whose name begins
  -- with `$`; host globals such as `Math` do not.
  sem esRuntimeUsed : ESProg -> [String]
  sem esRuntimeUsed =
  | ESProg t ->
    setToSeq (setOfSeq cmpString (join (map esGlobalsStmt t.stmts)))

  sem esGlobalsExpr : ESExpr -> [String]
  sem esGlobalsExpr =
  | ESEGlobal t -> match t.name with "$" ++ _ then [t.name] else []
  | ESEArrow t ->
    switch t.body
    case ESFBExpr b then esGlobalsExpr b.expr
    case ESFBBlock b then join (map esGlobalsStmt b.stmts)
    end
  | e -> join (map esGlobalsExpr (esExprChildren e))

  sem esGlobalsStmt : ESStmt -> [String]
  sem esGlobalsStmt =
  | ESSConst t -> esGlobalsExpr t.init
  | ESSLet t -> optionMapOr [] esGlobalsExpr t.init
  | ESSAssign t -> concat (esGlobalsExpr t.target) (esGlobalsExpr t.value)
  | ESSExpr t -> esGlobalsExpr t.expr
  | ESSReturn t -> optionMapOr [] esGlobalsExpr t.expr
  | ESSThrow t -> esGlobalsExpr t.expr
  | ESSIf t ->
    join [ esGlobalsExpr t.cond
         , join (map esGlobalsStmt t.thn), join (map esGlobalsStmt t.els) ]
  | ESSBlock t -> join (map esGlobalsStmt t.stmts)
  | ESSWhile t ->
    concat (esGlobalsExpr t.cond) (join (map esGlobalsStmt t.body))
  | ESSFunDecl t -> join (map esGlobalsStmt t.body)
  | ESSExportDefault t -> esGlobalsStmt t.stmt
  | ESSClass _ | ESSContinue _ -> []

end

let esRuntimeFile : String = concat stdlibLoc "/ecmascript/runtime/mexpr.mjs"

type ESRuntimeSection = {
  -- Other intrinsics this one calls, pulled in automatically.
  deps : [String],
  code : String
}

-- Splits the runtime module into its marked sections. Anything outside a
-- `//!intrinsic ... //!end` pair -- the file header, the export list -- is
-- ignored, which is what lets the file stay a valid ES module on its own.
let esRuntimeSections : () -> Map String ESRuntimeSection = lam.
  let lines = strSplit "\n" (readFile esRuntimeFile) in
  recursive let go = lam lines. lam open. lam acc.
    match lines with [l] ++ rest then
      let t = strTrim l in
      match open with Some (name, deps, buf) then
        if strStartsWith "//!end" t then
          go rest (None ()) (mapInsert name { deps = deps, code = strJoin "\n" buf } acc)
        else go rest (Some (name, deps, snoc buf l)) acc
      else if strStartsWith "//!intrinsic" t then
        match filter (lam w. not (null w)) (strSplit " " t) with [_, name] ++ deps then
          go rest (Some (name, deps, [])) acc
        else error (concat "malformed //!intrinsic marker: " t)
      else go rest open acc
    else
      match open with Some (name, _, _) then
        error (concat "unterminated //!intrinsic section: " name)
      else acc
  in go lines (None ()) (mapEmpty cmpString)

-- Renders the definitions for `used` plus everything they depend on.
--
-- Emitted in sorted order, which keeps output stable across runs; the
-- definitions are `function` declarations, so order does not affect semantics.
let esRuntimeEmit : [String] -> String = lam used.
  if null used then "" else
  let sections = esRuntimeSections () in
  recursive let close = lam pending. lam seen.
    match pending with [n] ++ rest then
      if setMem n seen then close rest seen
      else match mapLookup n sections with Some s then
        close (concat s.deps rest) (setInsert n seen)
      else error (concat "unknown runtime intrinsic: " n)
    else seen
  in
  let names = setToSeq (close used (setEmpty cmpString)) in
  join
  [ "\n// ---------------------------------------------------------------\n"
  , "// MExpr runtime intrinsics.\n"
  , "// ---------------------------------------------------------------\n\n"
  , strJoin "\n\n" (map (lam n. (mapFindExn n sections).code) names)
  , "\n" ]

mexpr

use ESRuntime in

let sections = esRuntimeSections () in

utest mapMem "$slli" sections with true in
utest mapMem "$srli" sections with true in
utest mapMem "$srai" sections with true in
utest mapMem "$roundfi" sections with true in
utest mapMem "$fromBig" sections with true in

-- The export list at the bottom of the file is outside every marker.
utest mapMem "export" sections with false in

-- Dependencies are recorded from the marker line.
utest (mapFindExn "$slli" sections).deps with ["$fromBig"] in
utest (mapFindExn "$roundfi" sections).deps with [] in

let a = nameSym "a" in

-- Reports exactly the runtime helpers the program refers to. Reading this off
-- the finished program is what keeps a helper used only inside a binding that
-- was later deleted from being emitted; `mcore.mc` tests that interaction.
let prog = ESProg { imports = [], stmts =
  [ ESSConst { id = a, init = ESECall
      { callee = ESEGlobal { name = "$unused" }, args = [] } }
  , ESSExpr { expr = ESECall
      { callee = ESEGlobal { name = "$kept" }, args = [ESEInt { value = 1 }] } } ] } in
utest esRuntimeUsed prog with ["$kept", "$unused"] in

-- Host globals are not runtime helpers.
utest esRuntimeUsed (ESProg { imports = [], stmts =
  [ ESSExpr { expr = ESECall
      { callee = esMember (ESEGlobal { name = "Math" }) "floor"
      , args = [ESEInt { value = 1 }] } } ] }) with [] in

-- Nothing requested means nothing emitted.
utest esRuntimeEmit [] with "" in

-- A dependency is pulled in even when it was not asked for.
let contains = lam needle. lam s. gti (length (strSplit needle s)) 1 in
let out = esRuntimeEmit ["$slli"] in
utest contains "function $slli(" out with true in
utest contains "function $fromBig(" out with true in
utest contains "function $roundfi(" out with false in

()
