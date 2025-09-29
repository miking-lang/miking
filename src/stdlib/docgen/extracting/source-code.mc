-- # Source code
--
-- We need a way to represent source code so that each node has its own slice of code,
-- while avoiding duplicating text in memory or introducing a heavyweight recursive structure.
-- We rely on the fact that child nodes appear in order among a node’s `children`.
-- Therefore, we represent the source as an array of optional `SourceCodeWord`.
-- Each `None` marks **the next child**, letting us assemble the full text later
-- by interleaving parent words with the children’s rendered code.
-- This yields efficient, recursive reconstruction without a recursive data type.

include "./source-code-word.mc"

-- A linear buffer of words where `None` denotes a child-boundary placeholder.
type SourceCode = [Option SourceCodeWord]

-- Packs a flat word buffer into a `SourceCode` by wrapping each word in `Some`.
let wordBufferToSourceCode : [SourceCodeWord] -> SourceCode = lam code.
    map (lam c. Some c) code

-- Trims leading/trailing words:
--   left  = content before the first `None` from the right (prefix section)
--   right = content after the last  `Some` from the left (suffix section)
let sourceCodeTrim : SourceCode -> { left: SourceCode, right: SourceCode } = lam code.
    { left = (splitOnR optionIsNone code).left, right = reverse (splitOnR optionIsSome (reverse code)).left }

-- Cast a string to a SourceCode by tokenizing the string until eof.
recursive let strToSourceCode : String -> SourceCode = use TokenReader in lam s.
    match s with "" then [] else
    match next s pos0 with { token = token, stream = stream } in
    let word = Some (sourceCodeWordFormat token) in
    cons word (strToSourceCode stream)
end
