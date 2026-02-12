include "./token-readers.mc"
include "./utils.mc"
include "../global/objects.mc"

-- Extracts variant names from a stream of syntax tree nodes starting with '|'.
-- Returns a list of the variants.
let synVariantParse : use TokenReader in use Objects in [Token] -> [SynVariant] = lam stream.
    use TokenReader in
    use Objects in
    recursive let work : [Token] -> Option [String] -> String -> [String] -> [SynVariant] =
    
        lam stream. lam typeAcc. lam nextDoc. lam commentBuffer.

        let strExtractType = lam acc.
            let t = strExtractType acc in
            match strSplitOnce t ' ' with Some (name, vtype) then
                { name = name, vtype = vtype, doc = nextDoc }
            else
                { name = t, vtype = "", doc = nextDoc }
        in

        let joinComments : () -> String = lam. strJoin "\n" (reverse commentBuffer) in

        switch (stream, typeAcc)
        case ([TokenWord { content = "|" }] ++ stream, None {}) then work stream (Some []) (joinComments ()) []
        case ([TokenWord { content = "|" }] ++ stream, Some typeAcc) then
            let t = strExtractType typeAcc in
            let nextDoc = joinComments () in
            let tail = work stream (Some []) nextDoc [] in
            cons t tail
        case ([TokenWord { content = word } ] ++ stream, Some typeAcc) then work stream (Some (cons word typeAcc)) nextDoc commentBuffer
        case ([TokenWord {} ] ++ stream, None {}) then work stream (None {}) nextDoc commentBuffer
        case ([TokenComment { content = comment } | TokenMultiLineComment { content = comment} ] ++ stream, _) then work stream typeAcc nextDoc (cons (strTrim comment) commentBuffer)
        case ([_] ++ stream, _) then work stream typeAcc nextDoc commentBuffer
        case ([], Some typeAcc) then [strExtractType typeAcc]
        case ([], None {}) then []
        end
    in
    work stream (None {}) "" []

