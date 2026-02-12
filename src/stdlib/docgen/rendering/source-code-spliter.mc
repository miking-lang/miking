include "../parsing/token-readers.mc"
include "./rendering-data.mc"

-- The result of a split operation.
-- - `left`: Code before the split (e.g., `let x =`)
-- - `right`: Code after the split (e.g., `3`)
type SourceCodeSplit = { left: SourceCode, right: SourceCode }

let sourceCodeSplit : SourceCode -> SourceCodeSplit = 
    lam arr.
    use TokenReader in

    let finish = lam left. lam right.
        { left = left, right = right }
    in

    match arr with [{ word = TokenWord {} } & x1] ++ rest then

        let splitAndReturn = lam split: String.
            match splitOnL (lam w. match w with { word = word } in eqString (lit word) split) rest with
                (left, right) in
            finish (cons x1 left) right
        in

        switch content x1.word
        case "let" | "type" | "sem" | "syn" then splitAndReturn "="
        case "con" then splitAndReturn ":"
        case "utest" | "mexpr" then finish [x1] rest
        case "lang" then
            match splitOnL (lam w. match w with { word = TokenWord {} } then true else false) rest with
                (left, right) in
            finish (cons x1 left) right

        case _ then finish [] arr
        end
    else
        finish [] arr
