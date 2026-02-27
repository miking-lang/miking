-- Core source-code representation and lexical classification for tooling.
-- This module defines visual word categories, wraps lexer tokens with
-- display metadata, and provides utilities to convert between strings,
-- tokens, and classified source code. It is a central component used by
-- the colorizer and other source-level tooling.

include "../parsing/token-readers.mc"
include "./logger.mc"

-- Visual categories used by the colorizer.
-- These kinds are purely for display / syntax highlighting,
-- not for semantic analysis.
lang SourceCodeWordKinds

    syn SourceCodeWordKind =
    | CodeKeyword {}
    | CodeName {}
    | CodeDefault {}
    | CodeType {}
    | CodeNumber {}
    
end

-- Represents a single token from the source code with its display category.
type SourceCodeWord = use SourceCodeWordKinds in use TokenReader in  {
    word: Token,
    kind: SourceCodeWordKind
}

-- Builds a single SourceCodeWord
let buildCodeWord :
    use SourceCodeWordKinds in
    use TokenReader in
    Token -> SourceCodeWordKind -> SourceCodeWord =

    use SourceCodeWordKinds in
    lam word. lam kind. {
        word = word,
        kind = kind    
    }

-- Classifies a token without context:
-- 1. Literal keyword -> CodeKeyword
-- 2. Integer literal -> CodeNumber
-- 3. Starts with capital letter -> CodeType
-- 4. Starts with letter or underscore -> CodeName
-- 5. Otherwise -> CodeDefault
-- These rules match Miking syntax (e.g., types start with a capital letter).
let sourceCodeWordFormat : use TokenReader in Token -> SourceCodeWord =
    use TokenReader in use SourceCodeWordKinds in lam token.
    let build = buildCodeWord token in
    switch token
    case TokenWord { content = content } then
         
        let kind = match content with "" then
            warn "Encountered empty token content during source code formatting.";
            CodeDefault {}
        else match content with "mexpr" | "utest" | "with" | "recursive" | "match" | "end" |
             "switch" | "in" | "include" | "case" | "if" | "else" | "type" | "con" |
             "lang" | "syn" | "use" | "let" | "lam" | "sem" | "then" then CodeKeyword {}
        else if stringIsInt content then  CodeNumber {}
        else if isUpperAlpha (head content) then CodeType {}
        else if isAlphaOrUnderscore (head content) then CodeName {}
        else CodeDefault {}
        in
        build kind
    case _ then build (CodeDefault {})
    end

-- A linear buffer of words
type SourceCode = [SourceCodeWord]

-- Cast a tokens array to a SourceCode.
let tokensToSourceCode : use TokenReader in [Token] -> SourceCode =
    map sourceCodeWordFormat

-- Cast a string to a SourceCode by tokenizing the string until eof.
recursive let strToSourceCode : String -> SourceCode = use TokenReader in lam s.
    match s with "" then [] else
    match next s pos0 with { token = token, stream = stream } in
    let word = sourceCodeWordFormat token in
    cons word (strToSourceCode stream)
end

let sourceCodeIsEmpty : SourceCode -> Bool = null

let sourceCodeEmpty : () -> SourceCode = lam . []

-- Cast a SourceCode to the original string.
let sourceCodeToStr : SourceCode -> String =
    lam code.
    use TokenReader in
    foldr concat "" (map (lam w. lit w.word) code)
