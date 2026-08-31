include "mexpr/pprint.mc"
include "./token-readers.mc"
include "docgen/global/util.mc"
include "seq.mc"
include "basic-types.mc"
include "bool.mc"
include "docgen/global/logger.mc"
include "string.mc"
include "mexpr/ast.mc"
include "mexpr/info.mc"
include "./pos.mc"

recursive let lex : use TokenReader in String -> Pos -> [(Token, Pos)] =
    lam s. lam pos.
    use TokenReader in
    match next s pos with { token = token, stream = s, pos = newPos } in
    match token with TokenEof {} & token then [(token, pos)] else cons (token, pos) (lex s newPos)
end

-- Compute the source code span of a given object
-- from its start position and the start position of the next object.
let computeObjectSpanning : use TokenReader in String -> Pos -> Pos -> Pos -> { code: String, rest: String, newPos: Pos } =
    use TokenReader in
    lam stream. lam currentPos. lam p1. lam p2.

    -- Assume we want to extract the source code of obj1,
    -- and that obj2 is the next object in the source.

    let getDxDy =
        lam p1. lam p2.
        -- If p2 and p1 are on the same line, we only need to shift x accordingly.
        -- Otherwise, x should be p2.x since the first line is entirely consumed.
        (subi p2.x (if eqi p2.y p1.y then p1.x else 0), subi p2.y p1.y)
    in

    -- Compute how far we need to advance from p1 to reach p2 in the stream.
    match getDxDy p1 p2 with (dx, dy) in
    -- Walk the stream to extract everything between obj1 and obj2.
    match strWalkTo stream dx dy with (code, _) in

    let tokens = lex code currentPos in

    -- Compute the actual end of obj1 by trimming comments and separators.
    match splitOnR (
        lam token.
        match token.0 with
        TokenWord { content = !("recursive" | "end") & content } -- "recursive" and "end" are edge cases
        then true else false
    ) (reverse tokens) with (trimmed, tokens) in

    -- The end of obj1 is where the first trimmed token starts.
    -- We use `last` because `trimmed` is reversed.
    let lastTrimmed = last trimmed in
    let newPos = lastTrimmed.1 in

    -- We now compute the actual remaining stream starting from the real end of obj1.
    match getDxDy currentPos newPos with (dx, dy) in

    match strWalkTo stream dx dy with (code, rest) in

    { code = code, rest = rest, newPos = newPos }

let isValidBlockOpener : String -> Bool =
    lam s.
    match s with "lang" | "external" | "syn" | "sem" | "let" | "type" | "con" | "utest" | "mexpr" then true else false

type GotoFirstWordRes = { doc: String, doc: [use TokenReader in Token], pos: Pos, rest: String, isLang: Bool }
recursive let gotoFirstWord : use TokenReader in String -> [Token] -> Pos -> Option GotoFirstWordRes =
    lam rest. lam acc. lam pos.
    use TokenReader in
    switch next rest pos
    case { token = TokenEof {} } then None {}
    case { token = TokenWord { content = !("recursive" | "end") & content } } then
        (if (not (isValidBlockOpener content)) then
            parsingWarn (join ["Wrong block opener detected: ", content, "."])
        else ());

        Some { doc = reverse acc, pos = pos, rest = rest, isLang = eqString "lang" content }
    case { token = TokenWord {}, pos = pos, stream = rest } then
        let rest = if null rest then rest else tail rest in -- We consume the separator before the let.
        gotoFirstWord rest acc pos
    case { token = token, pos = pos, stream = rest } then gotoFirstWord rest (cons token acc) pos
    end
end

recursive let getParentType : use MExprAst in Type -> String =
    lam t.
    use MExprPrettyPrint in
    switch t
    case TyApp { lhs = lhs } then getParentType lhs
    case TyAll { ty = ty } then getParentType ty
    case TyArrow { to = next } then getParentType next
    case _ then type2str t
    end
end

-- Info(row1_1, col1_1), Info(row1_2, col1_2) -> Info(row1_1, col1_1, row1_2, col1_2)
let concatInfos : Info -> Info -> Info =
    lam i1. lam i2.
    match (i1, i2)
        with (Info { filename = filename, row1 = row1, col1 = col1 }, Info { row1 = row2, col1 = col2 })
        then Info { filename = filename, row1 = row1, col1 = col1, row2 = row2, col2 = col2 }
        else NoInfo ()

recursive let strGetLastPos : String -> Pos -> Pos =
    lam s. lam pos.
    switch s
    case "" then pos
    case ['\n'] ++ s then strGetLastPos s { pos0 with y = addi pos.y 1 }
    case [_] ++ s then strGetLastPos s { pos with x = addi pos.x 1 }
    end
end

let belongToTheLang : String -> String -> Bool =
    lam langName.
    strStartsWith (concat langName "_")

let extractItemName : String -> String -> Option String =
    lam langName. lam itemName.
    if belongToTheLang langName itemName then
        Some (subsequence itemName (addi 1 (length langName)) (length itemName))
    else None {}


recursive let getNextWord : String -> Option { stream: String, word: String } =
    lam stream.
    use TokenReader in
    match next stream pos0 with { token = token, stream = stream } in
    switch token
    case TokenWord { content = word } then Some { word = word, stream = stream }
    case TokenEof {} then None {}
    case _ then getNextWord stream
    end
end

recursive let skipString: String -> String -> Option String =
    lam s. lam stream.
    use TokenReader in

    match next stream pos0 with { token = token, stream = stream } in
    match token with TokenWord { content = content } then
        if eqString content s then Some stream
        else None {}
    else skipString s stream
end

let strExtractType = use TokenReader in lam typedef.
    recursive let strExtractType = lam typedef.
     switch typedef
        case [] | ["in"] then ""
        case [x, "in"] | [x] then x
        case [current] ++ rest then
            let res = strExtractType rest in
            match (current, res)
            with (_, "," ++ _)
               | ("{", "}" ++ _)
               | ("[", _)
               | (_, "]" ++ _)
               | ("(", _)
               | (_, ")" ++ _)
               | (_, ":" ++ _) then
                concat current res
            else join [current, " ", res]
        end
    in
    strExtractType (reverse typedef)

let extractName : String -> Option String =
    lam stream.
    use TokenReader in
    recursive let work =
        lam stream. lam return.
        match next stream pos0 with { stream = stream, token = token } in
        switch token
        case TokenEof {} then None {}
        case TokenWord { content = content } then
            if return then Some content
            else work stream true
        case _ then work stream return
        end
    in
    work stream false

recursive let correctSpanning : String -> Pos -> Pos -> Pos =
    lam s. lam p1. lam p2.
    use TokenReader in
    if gePos p1 p2 then p2 else
    match next s p1 with { pos = newPos, token = token, stream = s } in
    switch token
    case TokenEof {} then p2
    case TokenWord { content = "lang" } then p1 -- Edge case, because the miking ast prunes the empty language we took the decision to handle this here
    case _ then correctSpanning s newPos p2
    end
end
