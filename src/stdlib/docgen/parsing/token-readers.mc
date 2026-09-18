-- All token readers implement a common interface: `TokenReaderInterface`.
-- The module ends by composing all token readers into one combined `TokenReader`.

include "../global/util.mc"
include "../global/logger.mc"
include "./include-set.mc"
include "./pos.mc"
    
include "hashmap.mc"
include "seq.mc"
include "bool.mc"
include "char.mc"

-- Interface definition for a generic TokenReader
lang TokenReaderInterface
    
    type NextResult = { token : Token, stream : String, pos: Pos }
    
    -- Abstract token type to be implemented by concrete readers
    syn Token =

    -- Generate the new position in the stream from the litteral of the given token
    sem actualisePos: Pos -> Token -> Pos
    sem actualisePos =
    | pos -> lam token.
        recursive let work : String -> Pos -> Pos = lam s. lam pos.
            switch s 
            case "" then pos
            case ['\n'] ++ s then work s { pos0 with y = addi pos.y 1 }
            case [_] ++ s then work s { pos with x = addi pos.x 1 }
            end
        in work (lit token) pos

    
    -- Returns the original literal text of the token
    sem lit : Token -> String

    -- Is used by the parser to get a representation of the token.
    sem content : Token -> String
    sem content =
    | t -> lit t
    
    -- Produces the next token from the input stream
    sem next : String -> Pos -> NextResult

    -- Utility function to build a NextResult
    sem buildResult : Token -> Pos -> String -> NextResult
    sem buildResult token pos = | stream ->  { token = token, pos = actualisePos pos token, stream = stream }
    
    -- Converts the token to a human-readable string
    sem tokenToString : Token -> String
     
end
    
-- Reader for multi lignes comments ( /* ... */ style )
lang MultiLineCommentTokenReader = TokenReaderInterface
    syn Token +=
      | TokenMultiLineComment { content: String, lit: String }

    sem lit +=
        | TokenMultiLineComment { lit = lit } -> lit

    sem content +=
        | TokenMultiLineComment { content = content } -> content

    sem tokenToString +=
        | TokenMultiLineComment {} -> "MultiLineComment"
    
    sem next +=
        | "/-" ++ str -> lam pos.
            recursive
            let extract =
            lam str. lam stack.
                switch (str, stack)
                case ("-/" ++ xs, 0) then ("", xs)
                case ("-/" ++ xs, stack) then
                    let extracted = extract xs (subi stack 1) in
                    (concat "-/" extracted.0, extracted.1)
                case ("/-" ++ xs, stack) then
                    let extracted = extract xs (addi stack 1) in
                    (concat "/-" extracted.0, extracted.1)
                case ([x] ++ xs, stack) then
                    let extracted = extract xs stack in
                    (cons x extracted.0, extracted.1)
                case _ then ("", "")
                end
            in
            let extracted = extract str 0 in
            buildResult (TokenMultiLineComment {
                    content = extracted.0,
                    lit = concat (concat "/-" extracted.0) "-/"
            }) pos extracted.1
end

    
-- Reader for single-line comments ( -- ... )
lang CommentTokenReader = TokenReaderInterface
    syn Token +=
      | TokenComment { content: String, lit: String }

    sem lit +=
        | TokenComment { lit = lit } -> lit        

    sem content +=
        | TokenComment { content = content } -> content

    sem tokenToString +=
        | TokenComment {} -> "Comment"
    
    sem next +=
        | "--" ++ str -> lam pos.
            recursive
            let extract =
            lam str.
                match str with "\n" ++ xs then
                    ("\n", xs)
                else match str with [x] ++ xs then
                    let extracted = extract xs in
                    (cons x extracted.0, extracted.1)
                else
                    ("", "")
            in
            let extracted = extract str in
            buildResult (TokenComment { content = extracted.0, lit = concat "--" extracted.0 }) pos extracted.1
end

-- Reader for string literals ( "..." )
lang StrTokenReader = TokenReaderInterface
    syn Token +=
      | TokenStr { content: String, between: String }

    sem lit +=
        | TokenStr { content = content } -> content

    sem tokenToString +=
        | TokenStr {} -> "Str"
    
    sem next /- : String -> NextResult -/ +=
        | "\"" ++ str -> lam pos.
            recursive
            let extract =
                lam str. 
                    switch str
                    case ['\\', x] ++ xs then
                        let extracted = extract xs in
                        (concat ['\\', x] extracted.0, extracted.1)
                    case ['\"'] ++ xs then
                        ("", xs)
                    case [x] ++ xs then
                        let extracted = extract xs in
                        (cons x extracted.0, extracted.1)
                    case _ then ("", "")
                    end
                in
            let extracted =  extract str in
            buildResult (TokenStr { content = join ["\"", extracted.0, "\""], between = extracted.0 }) pos extracted.1
end

-- Define set of separator characters / operators as a hashmap for fast lookup
let separatorMap =
    let traits = hashmapStrTraits in
    let insert = lam x. hashmapInsert traits x in
    let mem = lam x. hashmapMem traits x in
    foldl
        (lam m. lam k. hmInsert k () m)
        (hashmapEmpty ())
        ["=", "++", "+", "|", "{", "}", "[", "]", ":", ";", ".", ",", "(", ")", "->", " ", "\n", "\t", "\\", "&"]

-- Predicate to check if a string is a separator
let isSep = lam s. hmMem s separatorMap

-- Reader for words (non-separator sequences)
lang WordTokenReader = TokenReaderInterface
    syn Token +=
      | TokenWord { content: String }

    sem lit +=
        | TokenWord { content = content } -> content

    sem tokenToString +=
        | TokenWord {} -> "Word"
    
    sem next +=
         | str -> lam pos.
            match str with [x] then
                let token = TokenWord { content = [x] } in
                { token = token, stream = "", pos = actualisePos pos token }
            else if and (not (eqChar '\\' (head str))) (isSep [head str]) then
                let token = TokenWord { content = [head str] } in
                { token = token, stream = tail str, pos = actualisePos pos token }
            else let arr = [head str, head (tail str)] in if isSep arr then
                let token = TokenWord { content = arr } in
                { token = token, stream = tail (tail str), pos = actualisePos pos token }
            else
                recursive
                let extract =
                lam str. lam previous. lam first.
                    switch str 
                    case (("--" ++ x) | ("++" ++ x))
                        then ("", str)
                    case [x] ++ xs then
                        if and (not (and first (eqChar '\\' x))) (isSep [x]) then
                            ("", str)
                        else
                            let extracted = extract xs x false in
                            (cons x extracted.0, extracted.1)
                    case _ then ("", "")
                    end
                in
                let extracted =  extract str '-' true in
                buildResult (TokenWord { content = extracted.0 }) pos extracted.1
end

-- Reader for separators (spaces, newlines, tabs, etc.)
lang SeparatorTokenReader = TokenReaderInterface
    syn Token +=
      | TokenSeparator { content: String }

    sem lit +=
        | TokenSeparator { content = content } -> content

    sem tokenToString +=
        | TokenSeparator {} -> "Separator"
    
    sem next +=
        | [(' ' | '\t' | '\n' ) & c] ++ str -> lam pos.
            recursive
            let extract =
            lam str.
                match str with [(' ' | '\t' | '\n' ) & x] ++ xs then
                   let extracted = extract xs in
                   (cons x extracted.0, extracted.1)
                else ("", str)
            in
            let extracted =  extract str in
            buildResult (TokenSeparator { content = cons c extracted.0 }) pos extracted.1
end
    
-- Reader for End-of-File
lang EofTokenReader = TokenReaderInterface
    syn Token +=
      | TokenEof {}

    sem tokenToString +=
        | TokenEof {} -> "Eof"
    
    sem lit +=
        | TokenEof {} -> ""
    
    sem next +=
        | ""  -> lam pos.
            {
                token =TokenEof {},
                stream = "",
                pos = pos
            }
end
    
-- This lexer only support fundamental words.
lang SimpleWordTokenReader = StrTokenReader + CommentTokenReader + MultiLineCommentTokenReader + WordTokenReader + SeparatorTokenReader + EofTokenReader end

-- Contains skip utility function allowing to jump all the comments and separator until the next important token
lang CommAndSepSkiper = SimpleWordTokenReader
    
    sem skip : String -> String -> { skiped: [Token], stream: String, newToken: Token }
    sem skip =
    | str -> lam first.
        let pos = pos0 in
        let firstSkiped = match first with "" then [] else [TokenSeparator { content = first }] in
        switch next str pos 
            case { token = (TokenSeparator {} | TokenComment {} | TokenMultiLineComment {}) & token, stream = stream } then
                let res = skip stream "" in
                let skiped = concat firstSkiped (cons token res.skiped) in
                { res with skiped = skiped }
            case { token = token, stream = stream } then { stream = stream, skiped = firstSkiped, newToken = token }
            end
end
    
-- Reader for include directives ( include "file" )
lang IncludeTokenReader = CommAndSepSkiper
    syn Token +=
        | TokenInclude { content: String, lit: String, skiped: [Token] }

    sem lit +=
        | TokenInclude { content = content, lit = lit } -> lit

    sem tokenToString +=
        | TokenInclude {} -> "Include"

    sem includeNext =
        | str -> lam pos. lam firstSep.
            match skip str firstSep with { newToken = TokenStr { content = str }, stream = stream, skiped = skiped } then
                let token = TokenInclude { content = subsequence str 1 (subi (length str) 2), lit = join ["include", join (map lit skiped), str], skiped = skiped } in
                buildResult token pos stream
            else
                parsingWarn "Expected a string literal after `include` directive during lexing.";
                buildResult (TokenWord { content = concat "include" firstSep }) pos str

    sem next +=
        | "include " ++ str -> lam pos. includeNext str pos " "
        | "include\n" ++ str -> lam pos. includeNext str pos "\n"
        | "include\t" ++ str -> lam pos. includeNext str pos "\t"
        | "include\"" ++ str -> lam pos. includeNext (cons '\"' str) pos ""
        | "include--" ++ str -> lam pos. includeNext (cons '\"' str) pos ""
        | "include/-" ++ str -> lam pos. includeNext (cons '\"' str) pos ""            
end

-- This token is not readable but is at the root of a DocTree, the content is the name of the file and the includeSet a set will all the files.
lang ProgramTokenReader = TokenReaderInterface
    syn Token +=
        | TokenProgram { content: String }

    sem lit +=
        | TokenProgram {} -> ""

    sem tokenToString +=
        | TokenProgram {} -> "Program"
end

-- Reader combining recursive, include, and program tokens
lang TokenReader = IncludeTokenReader + ProgramTokenReader end

