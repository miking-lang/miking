-- # Sem-Map
--
-- This module implements the `sem-map`.
--
-- The problem we address is that when a language `B` inherits from another
-- language `A`, the compiler may merge their semantics, producing recursive
-- blocks that do not directly match the source code. For example:
--
-- lang A
-- sem x = | 1 -> recursive let y = 2 in 4
-- end
--
-- lang B = A
-- sem x = | 2 -> recursive let z = let a = 2 in 1 in 2
-- end
--
-- When processing `B`, the compiler generates a recursive block with `sem x`
-- containing both `1` and `2`, because `B` stems from `A`.
--
-- The issue: in the recursive stream, the `x` stream of `B` now contains two
-- different recursive blocks, which can desynchronize the logic.
--
-- To handle this, we define `getSemMap`, which counts how many times the word
-- `recursive` appears in each `sem` of the language. In the recursive stream,
-- we then keep only the *n* last recursive counts, where *n* is the number of
-- `recursive`s seen in the source code for that `sem`.
--
-- Example:  
-- If we obtain `[1, 2]` in the recursive stream, and the `sem-map` says `1`,
-- we keep only `[2]`.  
-- Since added semantics always appear after the real ones, we can safely
-- truncate the front of the array.

include "mexpr/ast.mc"
include "./token-readers.mc"
include "../../global/util.mc"

-- Maps a semantic name to the number of `recursive` keywords it contains.
type SemMap = HashMap String Int

-- Builds a `SemMap` by counting `recursive` keywords per `sem` in the input code.
let getSemMap : String -> SemMap = use TokenReader in lam s.
    recursive let nthWord : String -> Int -> String = lam stream. lam n.
        match next stream pos0 with { stream = stream, token = token } in
        switch token
        case TokenEof {} then parsingWarn "EOF detected during nthTokenWord."; ""
        case TokenWord { content = content } then
             if eqi 0 n then content
             else nthWord stream (subi n 1)
        case _ then nthWord stream n
        end
    in

    recursive let work : String -> SemMap -> Int -> Int -> String -> SemMap  = lam s. lam acc. lam count. lam switchCount. lam currentSem.
        match next s pos0 with { token = token, stream = stream } in
        let finish : () -> SemMap = lam.
            if eqi -1 count then acc else
                let count: Int = match hmLookup currentSem acc with Some n then addi n count else count in
                hmInsert currentSem count acc
        in
        switch token
        case TokenEof {} then parsingWarn "EOF reached in getSemStream"; acc
        case TokenWord { content = "switch" } then work stream acc count (addi switchCount 1) currentSem
        case TokenWord { content = "end" } then
             if eqi switchCount 0 then
                finish ()
             else
                work stream acc count (subi switchCount 1) currentSem
        case TokenWord { content = "sem" } then work stream (finish ()) 0 switchCount (nthWord stream 0)
        case TokenWord { content = "recursive" } then work stream acc (addi 1 count) switchCount currentSem
        case _ then work stream acc count switchCount currentSem
        end
    in
    work s (hashmapEmpty ()) -1 0 ""

