include "./token-readers.mc"
include "basic-types.mc"
include "docgen/parsing/pos.mc"
include "docgen/global/util.mc"

-- Takes in arguemant the raw code of the file
-- and output it's documentation if there is one.
-- The documentation of the program is all the comments
-- before the first token which is not a comment.
let parseProgramDoc : String -> Option String =

    use TokenReader in
    recursive let work =
        lam acc. lam noDoc. lam s.
        match next s pos0 with { token = token, stream = rest } in

        switch token
        case TokenMultiLineComment { content = content }
           | TokenComment { content = content } then
             let newAcc = concat (reverse content) acc in
             work newAcc false rest
        case TokenWord {} then None {}
        case _ then
            if noDoc then None {}
            else Some (reverse acc)
        end
    in
    work "" true

-- Takes in arguemant the raw code before
-- an object and output it's documentation if there is one.
let parseDoc : use TokenReader in [Token] -> Option String =
    lam s.
    use TokenReader in 
    recursive let work =
        lam stream. lam acc. lam allowNewLine.
        
        match stream with [token] ++ rest then
            let reset = lam allow. work rest [] allow in
            let keep = lam allow. work rest (cons token acc) allow in
            let skip = lam allow. work rest acc allow in

            switch token 
            case TokenMultiLineComment {} then keep true
            case TokenComment {} then keep false
            case TokenSeparator { content = content } then
                switch strCount content '\n'
                case 0 then skip false
                case 1 then
                    if allowNewLine then skip false
                    else reset false
                case _ then reset false
                end
            case _ then reset false
            end
        else if null acc then None {}
        else
            let doc = foldr (lam token. lam acc. concat (content token) acc ) [] (reverse acc) in
            Some (strStripEndingNewlines doc)
    in
    work s [] false
