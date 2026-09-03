-- Compares the new native parser (src/stdlib/parser/parser.mc) against
-- the boot (OCaml) parser on a single mcore file, and checks that every
-- node's info field is self-consistent: reparsing the exact source span
-- an info field points at, using the matching parse function for that
-- node's kind, must produce a result that is the same (up to info)
-- as the original node.
--
-- Usage: mi eval misc/parser-compare.mc -- <path/to/file.mc>
--
-- Exit code 0: the native parser agrees with boot (or boot itself could
--   not parse the file, which is reported but not treated as a native
--   parser failure) and every info field passed the self-consistency
--   check.
-- Exit code 1: the native parser failed to parse the file, its AST
--   disagrees with boot's, or an info field failed the self-consistency
--   check.

include "common.mc"
include "string.mc"
include "result.mc"
include "stdlib::parser/parser.mc"

let emptyEqEnv = {varEnv = biEmpty, conEnv = biEmpty}

-- The lexer counts a tab as `tabSpace` (2) columns wide when skipping
-- whitespace between tokens (see lexer.mc's `eatWSAC`), but as a single
-- (raw) column when it occurs inside a string or char literal (`matchChar`
-- does no tab-specific handling there). So `col` is not a simple raw
-- character index on lines with tabs, and the mapping depends on
-- whether a given tab is inside a string or char literal. This walks a
-- line, tracking literal state with a simple (unescaped-quote) toggle,
-- to find the raw index of the given (tab-aware) column.
let colToIndex : String -> Int -> Int = lam line. lam targetCol.
  recursive let go = lam idx. lam col. lam inStr. lam inChar.
    if or (geqi col targetCol) (geqi idx (length line)) then idx
    else
      let c = get line idx in
      let inStr = if and (eqChar c '"') (not inChar) then not inStr else inStr in
      let inChar = if and (eqChar c '\'') (not inStr) then not inChar else inChar in
      let step = if and (eqChar c '\t') (not (or inStr inChar)) then tabSpace else 1 in
      go (addi idx 1) (addi col step) inStr inChar
  in go 0 0 false false

-- Extracts the exact source substring an info field points at. Returns
-- `None ()` for `NoInfo` or an out-of-range span (which is itself an
-- info-consistency bug, reported separately by the caller).
let sliceBySpan : String -> Info -> Option String = lam src. lam info.
  match info with Info r then
    let lines = strSplit "\n" src in
    let nLines = length lines in
    if or (lti r.row1 1) (gti r.row2 nLines) then None () else
    if eqi r.row1 r.row2 then
      let line = get lines (subi r.row1 1) in
      let i1 = colToIndex line r.col1 in
      let i2 = colToIndex line r.col2 in
      if leqi i1 i2 then Some (subsequence line i1 (subi i2 i1)) else None ()
    else
      let firstLine = get lines (subi r.row1 1) in
      let lastLine = get lines (subi r.row2 1) in
      let i1 = colToIndex firstLine r.col1 in
      let i2 = colToIndex lastLine r.col2 in
      if leqi i1 (length firstLine) then
        let firstPart = subsequence firstLine i1 (subi (length firstLine) i1) in
        let lastPart = subsequence lastLine 0 i2 in
        let midLines = subsequence lines r.row1 (subi (subi r.row2 1) r.row1) in
        Some (strJoin "\n" (join [[firstPart], midLines, [lastPart]]))
      else None ()
  else None ()

mexpr

use TestParser in
use BootParserMLang in

let lex = lam s. nextToken {pos = initPos "reparse", str = s} in

let eqPatTop : Pat -> Pat -> Bool = lam p1. lam p2.
  match eqPat emptyEqEnv emptyEqEnv biEmpty p1 p2 with Some _ then true else false
in

let eqInfoStruct : Info -> Info -> Bool = lam a. lam b. eqi (infoCmp a b) 0 in

-- Reparses the source span an info field points at with `parseFn`, and
-- reports an issue (appended to `acc`) unless the result is present and
-- equal (via `eqFn`, ignoring info) to `orig`. Skipped when `info`
-- matches `parentInfo`: some nodes deliberately reuse their parent's
-- span verbatim because they have no source position of their own (e.g.
-- each character of a string literal, or the `Char` in the `[Char]` that
-- `String` desugars to) and so aren't independently reparseable.
let checkNode : all a. String -> [String] -> String -> Info -> Info -> a
              -> (NextTokenResult -> ParseResult () (a, NextTokenResult))
              -> (a -> a -> Bool) -> [String] =
  lam src. lam acc. lam kind. lam parentInfo. lam info. lam orig. lam parseFn. lam eqFn.
    match info with NoInfo _ then acc else
    if eqInfoStruct info parentInfo then acc else
    -- A zero-width span never corresponds to real source text (every
    -- token spans at least one character); it marks a synthetic
    -- placeholder node instead, e.g. the implicit `()` used when a
    -- program has no `mexpr` section at all.
    match info with Info r then
      if and (eqi r.row1 r.row2) (eqi r.col1 r.col2) then acc else
      switch sliceBySpan src info
      case None _ then
        snoc acc (join [info2str info, ": ", kind, " info span is out of range"])
      case Some s then
        switch result.consume (parseFn (lex s))
        case (_, Right (reparsed, _)) then
          if eqFn orig reparsed then acc
          else snoc acc (join [info2str info, ": ", kind, " reparse produced a different result for: ", s])
        case (_, Left _) then
          snoc acc (join [info2str info, ": ", kind, " reparse failed on: ", s])
        end
      end
    else acc
in

recursive
  let checkInfoDecl : Info -> String -> [String] -> Decl -> [String] = lam parentInfo. lam src. lam acc. lam d.
    let info = infoDecl d in
    let acc = checkNode src acc "decl" parentInfo info d parseDecl eqDecl in
    let acc = sfold_Decl_Decl (checkInfoDecl info src) acc d in
    let acc = sfold_Decl_Expr (checkInfoExpr info src) acc d in
    let acc = sfold_Decl_Type (checkInfoType info src) acc d in
    let acc = sfold_Decl_Pat (checkInfoPat info src) acc d in
    acc
  let checkInfoExpr : Info -> String -> [String] -> Expr -> [String] = lam parentInfo. lam src. lam acc. lam e.
    let info = infoTm e in
    let acc = checkNode src acc "expr" parentInfo info e parseExpr eqExpr in
    let acc = sfold_Expr_Expr (checkInfoExpr info src) acc e in
    let acc = sfold_Expr_Type (checkInfoType info src) acc e in
    let acc = sfold_Expr_Pat (checkInfoPat info src) acc e in
    acc
  let checkInfoType : Info -> String -> [String] -> Type -> [String] = lam parentInfo. lam src. lam acc. lam t.
    let info = infoTy t in
    -- `TyUnknown` is never produced by explicit syntax: it's always a
    -- placeholder for an omitted annotation, borrowing a nearby token's
    -- span purely for error-reporting purposes. That span isn't meant to
    -- be independently reparseable as "the type that was written here".
    let acc = match t with TyUnknown _ then acc
      else checkNode src acc "type" parentInfo info t parseType eqType in
    sfold_Type_Type (checkInfoType info src) acc t
  let checkInfoPat : Info -> String -> [String] -> Pat -> [String] = lam parentInfo. lam src. lam acc. lam p.
    let info = infoPat p in
    let acc = checkNode src acc "pat" parentInfo info p parsePat eqPatTop in
    let acc = sfold_Pat_Pat (checkInfoPat info src) acc p in
    let acc = sfold_Pat_Expr (checkInfoExpr info src) acc p in
    let acc = sfold_Pat_Type (checkInfoType info src) acc p in
    acc
in

if lti (length argv) 2 then
  printLn "Usage: mi eval misc/parser-compare.mc -- <path/to/file.mc>";
  exit 1
else

let path = get argv 1 in
let src = readFile path in

let parseNative = result.map (lam a. a.0) (parseProgram (lex src)) in

match result.consume parseNative with (_, Left errs) then
  printLn (join [path, ": NATIVE PARSER FAILED"]);
  iter (lam e. match e src with (info, msg) in printLn (infoErrorString info msg)) errs;
  exit 1
else match result.consume parseNative with (_, Right prog) in

let astOk =
  switch result.consume (parseMLangString src)
  case (_, Left _) then
    printLn (join [path, ": (boot could not parse this file; skipping AST comparison)"]);
    true
  case (_, Right bootProg) then
    if eqProgram prog bootProg then true
    else (printLn (join [path, ": NATIVE/BOOT AST MISMATCH"]); false)
  end
in

let issues =
  let acc = foldl (checkInfoDecl (NoInfo ()) src) [] prog.decls in
  checkInfoExpr (NoInfo ()) src acc prog.expr
in

(if null issues then ()
 else
   printLn (join [path, ": INFO SELF-CONSISTENCY ISSUES (", int2string (length issues), ")"]);
   iter printLn issues);

if and astOk (null issues) then
  printLn (join [path, ": OK"]);
  exit 0
else
  exit 1
