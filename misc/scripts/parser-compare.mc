-- Compares the new native parser (src/stdlib/parser/parser.mc) against
-- the boot (OCaml) parser on a single mcore file, and checks that every
-- node's info field is self-consistent: reparsing the exact source span
-- an info field points at, using the matching parse function for that
-- node's kind, must produce a result that is the same (up to info)
-- as the original node. There are exceptions due to syntax sugar.
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
include "stdlib::mexpr/boot-parser.mc"
include "stdlib::mlang/boot-parser.mc"
include "stdlib::mexpr/cmp.mc"
include "stdlib::mlang/cmp.mc"

lang ParserCompare = MLangParser + MLangCmp end

-- The lexer's `col` is not a raw character index into the line: it
-- advances differently depending on what is being consumed.
--
--  * Between tokens (`eatWSAC`) a tab counts as `tabSpace` (2) columns
--    and a carriage return as zero.
--  * Inside a string or char literal (`matchChar`) every raw character
--    counts as one column, tabs included, and a backslash escape is a
--    two-character, two-column pair whose second character must not be
--    inspected -- otherwise the escaped quote in `"q\"r"` reads as the
--    end of the literal and every tab after it is mismeasured.
--  * Inside a comment (`LineCommentParser` / `MultilineCommentParser`)
--    every raw character counts as one column, tabs included. Block
--    comments nest.
--
-- This mirrors that arithmetic to recover the raw index of a column.
let colToIndex : String -> Int -> Int = lam line. lam targetCol.
  let len = length line in
  -- Reading past the end yields a character that starts nothing.
  let at = lam i. if lti i len then get line i else ' ' in
  let isPair = lam i. lam a. lam b.
    and (eqChar (at i) a) (eqChar (at (addi i 1)) b) in
  recursive
    let normal = lam idx. lam col.
      if or (geqi col targetCol) (geqi idx len) then idx else
      if isPair idx '-' '-' then lineComment (addi idx 2) (addi col 2) else
      if isPair idx '/' '-' then blockComment (addi idx 2) (addi col 2) 1 else
      let c = at idx in
      if eqChar c '"' then literal (addi idx 1) (addi col 1) '"' else
      if eqChar c '\'' then literal (addi idx 1) (addi col 1) '\'' else
      let step = switch c
        case '\t' then tabSpace
        case '\r' then 0
        case _ then 1
        end in
      normal (addi idx 1) (addi col step)
    let literal = lam idx. lam col. lam close.
      if or (geqi col targetCol) (geqi idx len) then idx else
      let c = at idx in
      if eqChar c '\\' then literal (addi idx 2) (addi col 2) close else
      if eqChar c close then normal (addi idx 1) (addi col 1) else
      literal (addi idx 1) (addi col 1) close
    let lineComment = lam idx. lam col.
      if or (geqi col targetCol) (geqi idx len) then idx else
      lineComment (addi idx 1) (addi col 1)
    let blockComment = lam idx. lam col. lam depth.
      if or (geqi col targetCol) (geqi idx len) then idx else
      if isPair idx '/' '-' then
        blockComment (addi idx 2) (addi col 2) (addi depth 1)
      else if isPair idx '-' '/' then
        if eqi depth 1 then normal (addi idx 2) (addi col 2)
        else blockComment (addi idx 2) (addi col 2) (subi depth 1)
      else blockComment (addi idx 1) (addi col 1) depth
  in
  -- An escape pair straddling the end of the line can overshoot.
  mini (normal 0 0) len

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

-- What the info self-consistency walk accumulates: the problems found, plus
-- how many nodes were actually checked and how many were skipped, for any of
-- the reasons listed at `checkNode` and `checkInfoType`.
type CheckAcc = {issues : [String], checked : Int, skipped : Int}

mexpr

use ParserCompare in
use BootParserMLang in

let lex = lam s. nextToken {pos = initPos "reparse", str = s} in

let eqDeclTop : Decl -> Decl -> Bool = lam a. lam b. eqi (cmpDecl a b) 0 in
let eqExprTop : Expr -> Expr -> Bool = lam a. lam b. eqi (cmpExpr a b) 0 in
let eqTypeTop : Type -> Type -> Bool = lam a. lam b. eqi (cmpType a b) 0 in
let eqPatTop : Pat -> Pat -> Bool = lam a. lam b. eqi (cmpPat a b) 0 in

-- Boot's AST records only the *number* of type parameters of a `syn`
-- declaration (`Data (fi, ident, List.length params, ...)` in
-- `parser.mly`); the names survive solely because `set_con_params`
-- copies them onto every constructor. A `syn` without constructors
-- therefore loses them altogether, and `mlang/boot-parser.mc` invents
-- `p` for each one. Erase the names on both sides so the comparison
-- doesn't flag a difference the boot AST is unable to represent.
recursive let eraseEmptySynParams : Decl -> Decl = lam d.
  let d = smap_Decl_Decl eraseEmptySynParams d in
  match d with DeclSyn r then
    if null r.defs then
      DeclSyn {r with params = make (length r.params) (nameNoSym "p")}
    else d
  else d
in
let eraseEmptySynParamsProgram : MLangProgram -> MLangProgram = lam p.
  {p with decls = map eraseEmptySynParams p.decls}
in

let eqInfoStruct : Info -> Info -> Bool = lam a. lam b. eqi (infoCmp a b) 0 in

-- Reparses the source span an info field points at with `parseFn`, and
-- reports an issue (appended to `acc`) unless the result is present and
-- equal (via `eqFn`, ignoring info) to `orig`.
--
-- Every expression, pattern and declaration is required to carry an info
-- field, so that a diagnostic about it has somewhere to point; one without
-- an info field is itself an issue, reported against its parent's span so it
-- can be found. Types are exempt, and handled in `checkInfoType` below.
--
-- Two kinds of span are not checked here, because reading them back out of
-- the source and expecting the same node is not meaningful:
--  * one that repeats the parent's span, which is how a node introduced by
--    desugaring is written where nothing more specific was available; and
--  * a zero-width one, which no token can occupy.
--
-- The remaining nodes that desugaring introduces do have a span of their own,
-- pointing at the nearest thing that was written, and are listed one by one
-- in `isDesugared` below.
let issue : CheckAcc -> String -> CheckAcc = lam acc. lam msg.
  {acc with issues = snoc acc.issues msg} in

let checkNode : all a. String -> CheckAcc -> String -> Info -> Info -> a
              -> (NextTokenResult -> ParseRes () (a, NextTokenResult))
              -> (a -> a -> Bool) -> CheckAcc =
  lam src. lam acc. lam kind. lam parentInfo. lam info. lam orig. lam parseFn. lam eqFn.
    match info with NoInfo _ then
      issue acc (join [info2str parentInfo, ": contains a ", kind, " node with no info field"])
    else
    if eqInfoStruct info parentInfo then {acc with skipped = addi acc.skipped 1} else
    match info with Info r then
    if and (eqi r.row1 r.row2) (eqi r.col1 r.col2) then
      {acc with skipped = addi acc.skipped 1}
    else
    let acc = {acc with checked = addi acc.checked 1} in
    switch sliceBySpan src info
    case None _ then
      issue acc (join [info2str info, ": ", kind, " info span is out of range"])
    case Some s then
      switch result.consume (parseFn (lex s))
      case (_, Right (reparsed, _)) then
        if eqFn orig reparsed then acc
        else issue acc (join [info2str info, ": ", kind, " reparse produced a different result for: ", s])
      case (_, Left _) then
        issue acc (join [info2str info, ": ", kind, " reparse failed on: ", s])
      end
    end
    else never
in

-- Nodes that the parser introduces while desugaring, and which point at the
-- nearest thing that *was* written rather than at text that parses back to
-- them. Each is listed with the construct that produces it.
--
-- This list exists only because the tree has no other way to say "this node
-- was generated"; it goes away with this whole script once the boot parser
-- does. The positions of these nodes are pinned by the utests in
-- `src/stdlib/parser/parser.mc` instead.
-- The name the parser gives the binders it introduces.
let isGenerated : Name -> Bool = lam n. eqString (nameGetStr n) "X" in

let isDesugaredExpr : Expr -> Bool = lam e.
  switch e
  -- the implicit `never` ending a `switch`, and the one a projection or a
  -- `match ... in` falls through to
  case TmNever _ then true
  -- a link of the chain a `switch` becomes, pointing at its own `case`
  case TmMatch {target = TmVar {ident = ident}} then isGenerated ident
  -- a reference to a binder the parser introduced
  case TmVar {ident = ident} then isGenerated ident
  -- one character of a string literal, which points at the whole literal
  case TmConst {val = CChar _} then true
  case _ then false
  end in

let isDesugaredPat : Pat -> Bool = lam p.
  switch p
  -- the `true` that `if` matches on, pointing at the condition it tests
  case PatBool _ then true
  -- one character of a string pattern, which points at the whole literal
  case PatChar _ then true
  -- the binder a projection introduces, and the record pattern around it
  case PatNamed {ident = PName ident} then isGenerated ident
  case PatRecord {bindings = bindings} then
    match mapValues bindings with [PatNamed {ident = PName ident}]
    then isGenerated ident else false
  case _ then false
  end in

let isDesugaredType : Type -> Bool = lam t.
  switch t
  -- the constructor set of a `Con{!A B}` restriction, which is not a type
  case TyData _ then true
  -- the variant that `type F a` with no `=` stands for
  case TyVariant {constrs = constrs} then mapIsEmpty constrs
  -- the unit payload of a `syn` constructor declared without one
  case TyRecord {fields = fields} then mapIsEmpty fields
  case _ then false
  end in

recursive
  let checkInfoDecl : Info -> String -> CheckAcc -> Decl -> CheckAcc = lam parentInfo. lam src. lam acc. lam d.
    let info = infoDecl d in
    let acc = checkNode src acc "decl" parentInfo info d parseDecl eqDeclTop in
    let acc = sfold_Decl_Decl (checkInfoDecl info src) acc d in
    let acc = sfold_Decl_Expr (checkInfoExpr info src) acc d in
    let acc = sfold_Decl_Type (checkInfoType info src) acc d in
    let acc = sfold_Decl_Pat (checkInfoPat info src) acc d in
    acc
  let checkInfoExpr : Info -> String -> CheckAcc -> Expr -> CheckAcc = lam parentInfo. lam src. lam acc. lam e.
    let info = infoTm e in
    let acc = if isDesugaredExpr e then {acc with skipped = addi acc.skipped 1}
      else checkNode src acc "expr" parentInfo info e parseExpr eqExprTop in
    let acc = sfold_Expr_Expr (checkInfoExpr info src) acc e in
    let acc = sfold_Expr_Type (checkInfoType info src) acc e in
    let acc = sfold_Expr_Pat (checkInfoPat info src) acc e in
    acc
  let checkInfoType : Info -> String -> CheckAcc -> Type -> CheckAcc = lam parentInfo. lam src. lam acc. lam t.
    let info = infoTy t in
    -- Unlike the other three, a type node need not carry a span at all: most
    -- of them are placeholders that the type checker fills in later rather
    -- than syntax that was written. Two kinds are therefore skipped instead
    -- of being required to reparse:
    --  * `TyUnknown`, which stands for an annotation that was omitted; where
    --    it does carry a span, that span belongs to whatever it annotates and
    --    is not meant to reparse as "the type written here"; and
    --  * any type with no span, such as the `Char` in the `[Char]` that the
    --    `String` keyword stands for.
    let acc =
      match t with TyUnknown _ then {acc with skipped = addi acc.skipped 1} else
      match info with NoInfo _ then {acc with skipped = addi acc.skipped 1} else
      if isDesugaredType t then {acc with skipped = addi acc.skipped 1} else
      checkNode src acc "type" parentInfo info t parseType eqTypeTop in
    sfold_Type_Type (checkInfoType info src) acc t
  let checkInfoPat : Info -> String -> CheckAcc -> Pat -> CheckAcc = lam parentInfo. lam src. lam acc. lam p.
    let info = infoPat p in
    let acc = if isDesugaredPat p then {acc with skipped = addi acc.skipped 1}
      else checkNode src acc "pat" parentInfo info p parsePat eqPatTop in
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
    if eqi (cmpProgram (eraseEmptySynParamsProgram prog)
                       (eraseEmptySynParamsProgram bootProg)) 0
    then true
    else (printLn (join [path, ": NATIVE/BOOT AST MISMATCH"]); false)
  end
in

let acc =
  let empty = {issues = [], checked = 0, skipped = 0} in
  let acc = foldl (checkInfoDecl (NoInfo ()) src) empty prog.decls in
  checkInfoExpr (NoInfo ()) src acc prog.expr
in
let issues = acc.issues in

(if null issues then ()
 else
   printLn (join [path, ": INFO SELF-CONSISTENCY ISSUES (", int2string (length issues), ")"]);
   iter printLn issues);

if and astOk (null issues) then
  printLn (join [path, ": OK (", int2string acc.checked, " checked, ", int2string acc.skipped, " skipped)"]);
  exit 0
else
  exit 1
