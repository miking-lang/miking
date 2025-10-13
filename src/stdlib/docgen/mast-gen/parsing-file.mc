-- Defines a simple type representing an opened file.

include "../parsing/lexing/token-readers.mc"

-- Represents a parsed file header, including its `include`s, header tokens, and full text.
type ParsingFile = use TokenReader in { includes: [String], headerTokens: [{ token: Token, pos: Pos }], fileText: String }

let parsingFileEmpty = { includes = [], fileText = "", headerTokens = [] }
