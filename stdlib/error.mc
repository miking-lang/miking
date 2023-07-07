/-

This module provides functions for highlighting sections of a file,
primarily intended for error reporting in a compiler.

The underlying workhorse is `formatHighlights`, which takes the source
of a file and a sequence of ranges to highlight (`Highlight`s,
essentially `Info`s with some extra information).

There is also a high-level interface for reporting errors and
immediately exiting. This centers around the `ErrorSection` type:

```
type ErrorSection = {msg : String, multi : String, info : Info, infos : [Info]}
let err : ErrorSection = {msg = "", multi = "", info = NoInfo (), infos = []}
```

An `ErrorSection` represents a single contiguous range in a file,
possibly with multiple sub-ranges to highlight, and with an optional
related message. Typically you would construct this through record
updates on `err`, since most fields are optional:

- `infos`: The ranges to highlight. Default to [`info`] if absent.
- `info`: The complete section to display. Defaults to `foldl
  mergeInfo (NoInfo ()) infos` if absent.
- `msg`: The message to display above the highlighted section, if any.
- `multi`: Used instead of `msg` if present and `infos` contains at
  least two elements (useful for pluralizing messages).

There are three functions for displaying an error and immediately
exiting:
- `errorGeneral` takes a sequence of `ErrorSection`s and a record with
  two fields (both are optional):
  - `single`: The message to display if only one `ErrorSection` is
    given.
  - `multi`: The message to display if more than one `ErrorSection` is
    given. Defaults to `single` if absent.
- `errorSingle` is a helper for when you have only one section; it
  takes a sequence of `Info`s and the error message as a `String`.
- `errorMulti` correspondingly handles the simplest case with multiple
  sections; it takes a sequence of `(Info, String)`, treating each as
  a section, as well as the error message as a `String`.

-/

include "seq.mc"
include "char.mc"
include "map.mc"
include "mexpr/info.mc"
include "common.mc"

type Highlight
-- A section of the code inside the area to be highlighted, but that
-- is itself irrelevant. Optional, sections between other highlighted
-- sections are irrelevant by default.
con Irrelevant : Info -> Highlight
-- A section that is inside the highlighted area and is relevant,
-- i.e., it should be highlighted in some way.
con Relevant : Info -> Highlight
-- Text to be added in the highlighted section, even though it is not
-- present in the original input. If `ensureSurroundedBySpaces` is
-- true then the added content will additionally be surrounded by a
-- space on either side, from the original input if possible,
-- otherwise added.
con Added : {content : String, ensureSurroundedBySpaces : Bool} -> Highlight

-- Highlighting can be configured using the functions in this config.
type HighlightConfig =
  { beforeSection : String -> String  -- Called for the part before the section *on the same line* as the beginning
  , afterSection : String -> String   -- Called for the part after the section *on the same line* as the end
  , irrelevant : String -> String
  , relevant : String -> String
  , added : String -> String
  }

type InnerHighlight
con IBefore : () -> InnerHighlight
con IAfter : () -> InnerHighlight
con IRelevant : () -> InnerHighlight
con IIrrelevant : () -> InnerHighlight
con IAdded : {ensureSurroundedBySpaces : Bool} -> InnerHighlight

type HPos = { row : Int, col : Int }
type HInput = { pos : HPos, rest : String }

let _advanceRow
  : HPos -> HPos
  = lam pos. {{ pos with row = addi pos.row 1 } with col = 0}
let _advanceCol
  : HPos -> HPos
  = lam pos. { pos with col = addi pos.col 1 }
let _hposLessThan
  : HPos -> HPos -> Bool
  = lam a. lam b. or (lti a.row b.row) (and (eqi a.row b.row) (lti a.col b.col))
let _advanceInput
  : HInput -> Option (Char, HInput)
  = lam input.
    switch input.rest
    case "\n" ++ rest then Some ('\n', {pos = _advanceRow input.pos, rest = rest})
    case [c] ++ rest then Some (c, {pos = _advanceCol input.pos, rest = rest})
    case [] then None ()
    end
let _splitInput
  : HPos -> HInput -> (String, HInput)
  = lam target. lam input.
    recursive let work = lam acc. lam input: HInput.
      if _hposLessThan input.pos target then
        match _advanceInput input with Some (c, input) then
          work (snoc acc c) input
        else (acc, input)
      else (acc, input)
    in work "" input

let _getRange
  : Highlight
  -> Option (HPos, HPos)
  = lam h.
    switch h
    case Irrelevant (Info x) then Some ({row = x.row1, col = x.col1}, {row = x.row2, col = x.col2})
    case Relevant (Info x) then Some ({row = x.row1, col = x.col1}, {row = x.row2, col = x.col2})
    case Added _ then None ()
    case _ then
      printLn "WARNING: (implementation error) missing info field in _getRange";
      None ()
    end

-- Take a sequence of sections to be highlighted (positioned through
-- `Info` values) belonging to a single file, in order, then produce a
-- highlighted version of that section of the input file.
let formatHighlights
  : HighlightConfig
  -> String  -- File content
  -> [Highlight]
  -> String  -- Highlighted section after processing
  = lam config. lam content. lam highlights.
    let contentTooShort = lam. error "The file isn't long enough, some of the highlight is outside" in
    let input: HInput = { rest = content, pos = { row = 1, col = 0} } in
    let startPos: HPos =
      match findMap _getRange highlights with Some (startPos, _)
      then startPos
      else error "This highlight list doesn't have any info fields in it" in
    let endPos: HPos =
      match findMap _getRange (reverse highlights) with Some (_, endPos)
      then endPos
      else error "This highlight list doesn't have any info fields in it" in

    -- NOTE(vipa, 2022-03-04): Identify the sections and their content
    match _splitInput { startPos with col = 0 } input with (_, input) in
    match _splitInput startPos input with (before, input) in
    let sections = [(before, IBefore ())] in
    recursive let work = lam sections. lam input. lam highlights.
      match highlights with [h] ++ highlights then
        match _getRange h with Some (startPos, endPos) then
          match _splitInput startPos input with (irr, input) in
          match _splitInput endPos input with (sec, input) in
          let label =
            switch h
            case Relevant _ then IRelevant ()
            case Irrelevant _ then IIrrelevant ()
            case _ then error "impossible"
            end in
          work (concat sections [(irr, IIrrelevant ()), (sec, label)]) input highlights
        else match h with Added x then
          work (snoc sections (x.content, IAdded {ensureSurroundedBySpaces = x.ensureSurroundedBySpaces})) input highlights
        else
          work (snoc sections ("<NoInfo>", IAdded {ensureSurroundedBySpaces = true})) input highlights
      else (sections, input)
    in
    match work sections input highlights with (sections, input) in
    match _splitInput (_advanceRow endPos) input with (after, _) in
    let after = match after with after ++ "\n" then after else after in
    let sections = snoc sections (after, IAfter ()) in

    let sections = filter (lam x. match x with ([_] ++ _, _) then true else false) sections in

    -- NOTE(vipa, 2022-03-04): Format and concatenate the
    -- sections. This isn't just a concatMap because we need to fix
    -- padding for `Added` sections.
    recursive let work = lam acc. lam needsPreSpace. lam sections.
      match sections with [(content, label)] ++ sections then
        let needsPadding = match label with (IAdded {ensureSurroundedBySpaces = true}) then true else false in
        let needsPostSpace =
          match sections with [([c] ++ _, _)] ++ _
          then if isWhitespace c then false else true
          else false in
        let pre = if and needsPadding needsPreSpace then config.irrelevant " " else "" in
        let post = if and needsPadding needsPostSpace then config.irrelevant " " else "" in
        let f = switch label
          case IBefore _ then config.beforeSection
          case IAfter _ then config.afterSection
          case IRelevant _ then config.relevant
          case IIrrelevant _ then config.irrelevant
          case IAdded _ then config.added
          end in
        let nextNeedsPreSpace =
          match concat content post with _ ++ [c] in
          if isWhitespace c then false else true in
        work (join [acc, pre, f content, post]) nextNeedsPreSpace sections
      else acc
    in
    work "" false sections

let terminalHighlightAddedConfig: HighlightConfig =
  { beforeSection = lam str. concat "[0m" str
  , afterSection = lam str. concat "[0m" str
  , irrelevant = lam str. concat "[0m" str
  , relevant = lam str. concat (concat "[37m" str) "[0m"
  , added = lam str. concat (concat "[31m" str) "[0m"
  }

let terminalHighlightErrorConfig: HighlightConfig =
  { beforeSection = lam str. concat "[0m" str
  , afterSection = lam str. concat "[0m" str
  , irrelevant = lam str. concat "[0m" str
  , relevant = lam str. concat (concat "[31m" str) "[0m"
  , added = lam str. concat (concat "[31m" str) "[0m"
  }

type ErrorSection = {msg : String, multi : String, info : Info, infos : [Info]}
let errorDefault : ErrorSection = {msg = "", multi = "", info = NoInfo (), infos = []}
let infoToSection : Info -> ErrorSection = lam info. {errorDefault with info = info}

let _cachedContent : Ref (Map String String) = ref (mapEmpty cmpString)
let _readContent : String -> Option String = lam filename.
  match mapLookup filename (deref _cachedContent) with c & Some content then c else
  -- TODO(vipa, 2022-05-17): This is technically a race condition, the
  -- file could be removed in-between the check and the read, but
  -- there's no better way to handle it atm.
  if fileExists filename then
    let content = readFile filename in
    modref _cachedContent (mapInsert filename content (deref _cachedContent));
    Some content
  else None ()

let _emptyOrNewlineTerm : String -> String = lam str.
  switch str
  case "" then str
  case _ ++ "\n" then str
  case str then snoc str '\n'
  end

let _highlightSection
  : ErrorSection -> (Info, String)
  = lam section.
    let info = match section.info with NoInfo ()
      then foldl mergeInfo (NoInfo ()) section.infos
      else section.info in
    let infos = match section.infos with []
      then [section.info]
      else section.infos in
    let infos = map (lam x. Relevant x) infos in
    let infos =
      match section.info with Info x then
        let first = infoVal x.filename x.row1 x.col1 x.row1 x.col1 in
        let last = infoVal x.filename x.row2 x.col2 x.row2 x.col2 in
        snoc (cons (Irrelevant first) infos) (Irrelevant last)
      else infos in
    let msg = match section.infos with ![] & ![_]
      then match section.multi with !"" then section.multi else section.msg
      else section.msg in
    let msg = _emptyOrNewlineTerm msg in
    let msg =
      match info with Info {filename = filename} then
        match _readContent filename with Some content
        then concat msg (formatHighlights terminalHighlightErrorConfig content infos)
        else join [msg, "<Couldn't read '", filename, "', no highlight available>"]
      else msg in
    (info, _emptyOrNewlineTerm msg)

let errorMsg
  : [ErrorSection] -> {single: String, multi: String} -> (Info, String)
  = lam sections. lam msg.
    switch map _highlightSection sections
    case [(info, inner)] then (info, concat (_emptyOrNewlineTerm msg.single) inner)
    case sections then
      let msg = match msg.multi with !"" then msg.multi else msg.single in
      match unzip sections with (infos, inners) in
      let info = foldl mergeInfo (NoInfo ()) infos in
      let msg = strJoin "\n" (cons (_emptyOrNewlineTerm msg) inners) in
      (info, msg)
    end

let _partitionInfosByFile : [Info] -> [[Info]] = lam infos.
  recursive let work = lam acc. lam info.
    match info with Info x then
      mapInsertWith concat x.filename [info] acc
    else acc
  in mapValues (foldl work (mapEmpty cmpString) infos)

let _die : all a. (Info, String) -> a = lam msg.
  printError (join ["\n", infoErrorString msg.0 msg.1, "\n"]);
  flushStderr ();
  exit 1
let _warn : (Info, String) -> () = lam msg.
  printError (join ["\n", infoWarningString msg.0 msg.1, "\n"]);
  flushStderr ()

let _general = lam f. lam sections. lam msg. f (errorMsg sections msg)
let errorGeneral : all a. [ErrorSection] -> {single: String, multi: String} -> a
  = lam x. _general _die x

let _single = lam f. lam infos. lam msg.
  let mkSection = lam infos. {errorDefault with infos = infos} in
  f (errorMsg (map mkSection (_partitionInfosByFile infos)) {single = msg, multi = ""})
let errorSingle : all a. [Info] -> String -> a
  = lam x. _single _die x
let warnSingle : all a. [Info] -> String -> ()
  = lam x. _single _warn x

let _multi = lam f. lam sections. lam msg.
  f (errorMsg (map (lam sec. {errorDefault with info = sec.0, msg = sec.1}) sections) {single = msg, multi = ""})
let errorMulti : all a. [(Info, String)] -> String -> a
  = lam x. _multi _die x
let warnMulti : all a. [(Info, String)] -> String -> ()
  = lam x. _multi _warn x

mexpr

let content = join
  [ "let a = 1 in\n"
  , "let x = match a with\n"
  , "  | 1 -> match x with\n"
  , "    | \"blub\" -> 1\n"
  , "  | 2 -> 2\n"
  ] in

let config =
  { beforeSection = lam str. join ["<bef>", str, "</bef>"]
  , afterSection = lam str. join ["<aft>", str, "</aft>"]
  , irrelevant = lam str. join ["<irr>", str, "</irr>"]
  , relevant = lam str. join ["<rel>", str, "</rel>"]
  , added = lam str. join ["<new>", str, "</new>"]
  } in

let highlights =
  [ Relevant (infoVal "test" 2 8 2 13)
  , Relevant (infoVal "test" 2 16 2 20)
  , Irrelevant (infoVal "test" 3 8 3 9)
  , Added {content = "(", ensureSurroundedBySpaces = true}
  , Relevant (infoVal "test" 3 9 3 14)
  ] in

utest formatHighlights config content highlights
with
  let content: String = join
    [ "<bef>let x = </bef><rel>match</rel><irr> a </irr><rel>with</rel><irr>\n"
    , "  | 1 -></irr><irr> </irr><new>(</new><irr> </irr><rel>match</rel><aft> x with</aft>"
    ]
  in content in

()
