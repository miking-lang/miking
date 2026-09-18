-- In the Miking syntax, `include` statements must remain at the beginning of a
-- file. To implement a Miking lexer/parser, it is therefore possible to start
-- by parsing a header containing all the includes.
-- This file provides a function that takes a file name and returns a data
-- structure representing the file and its includes.

include "../parsing/token-readers.mc"
include "../parsing/pos.mc"
include "../global/ext-utils.mc"
include "sys.mc"
include "basic-types.mc"

-- Represents a parsed file header, including its includes, header tokens, and full text.
type ParsingFile = use TokenReader in {
    includes: [String],
    headerTokens: [{ token: Token, pos: Pos }],
    -- fileText contains the source text starting from the first non-header token
    fileText: String
}

let parsingFileEmpty = { includes = [], fileText = "", headerTokens = [] }

-- This file provides a function that parses the header of a Miking file
-- (includes, comments, separators) and stops at the first non-header token.
-- Header tokens are limited to includes, comments, and separators.
-- Parsing stops at the first non-header token.
let parsingOpenFile : String -> Option ParsingFile = use TokenReader in lam file.

    recursive let work : String -> Pos -> ParsingFile -> ParsingFile = lam s. lam pos. lam acc.
        match next s pos with { stream = stream, token = token, pos = pos } in
        let go = lam acc. work stream pos { acc with headerTokens = cons { token = token, pos = pos } acc.headerTokens } in

        switch token
        case TokenComment {} | TokenMultiLineComment {} | TokenSeparator {} then go acc
        case TokenInclude { content = content} then go { acc with includes = cons content acc.includes }
        case _ then { includes = reverse acc.includes, headerTokens = reverse acc.headerTokens, fileText = s }
        end
    in

    match docgenFileReadOpen file with Some rc then
        let s = docgenFileReadString rc in
        docgenFileReadClose rc;
        Some (work s pos0 { includes = [], headerTokens = [], fileText = "" })
    else
        None {}
