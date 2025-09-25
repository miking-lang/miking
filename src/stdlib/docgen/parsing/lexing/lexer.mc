-- # Lexer
-- This module defines the `lex` function, which tokenizes a Miking source string.
-- It produces a `TokenStream`, which is a list of `(Token, Pos)` pairs.
-- The lexer uses the `next` function from `token-readers.mc` to scan the input
-- and record the position of each token.
--
-- The main challenge of our lexer is that we must preprocess recursive blocks
-- and replace their closers with a specific token. The syntax of recursive blocks
-- is highly ambiguous, which causes problems for our parser, whose goal is not
-- to fully parse the program but only to annotate it.
--
-- For example, the following code is ambiguous, since we cannot know in advance
-- whether the first `in` closes the recursive block or the `let y`, without a
-- full parse:
--
-- let z =
--     recursive
--     let a = 3
--     let x = let y = 3 in 2
--     in
--     2
--
-- To address this, we use the compiler’s AST to establish a recursive stream.
-- The idea is that we traverse the compiler’s AST and count how many `in`s are
-- expected in each recursive block. With this information, it becomes
-- straightforward to disambiguate recursive blocks by determining which `in`
-- closes them.
--
-- The recursive stream provides a sequence of integers representing how many
-- `in`s each recursive block contains, in raw-code order. Each time we see a
-- `recursive` in the code, we fetch a count from the stream. Each time we see
-- an `in`, we decrement the counter. When an `in` appears with the counter at 0,
-- we know it closes the block and must replace it with a special token.
--
-- There are 3 main challenges:
--
-- 1. **Language assembly**  
--    When a language is assembled, semantic patterns from parent languages are
--    merged. This may introduce recursive blocks in the AST that are absent
--    from the source code, desynchronizing the recursive stream and the lexer.
--    To handle this, we use a sem-stream: whenever the lexer encounters
--    `lang`, it traverses the entire language definition and counts the number
--    of recursives introduced by its semantics. The recursive stream then
--    adapts accordingly. See `type-stream.mc` for more information.
--
-- 2. **Multiple constructs introducing `in`**  
--    Many constructs in Miking introduce an `in`:  
--      - obvious ones: nested `let`, `type`, etc.  
--      - `match .. in` also introduces one.  
--    To handle this, we increase the current counter when we see such constructs.
--    This ensures that when the corresponding `in` appears, it will be
--    decremented automatically.  
--    We must also intercept `then`, which may act as an `in` counter decreaser
--    if the match was a `match .. then` instead of `match .. in`. To handle this
--    correctly, we also increase the counter when we see constructs that produce
--    a `then`, like `case` or `if`.  
--    Furthermore, `use` introduces an `in`, so we apply the same logic there.  
--    Finally, some constructs desynchronize raw code and AST, such as `;` and
--    `switch`, which introduce hidden `let`/`in` in the MAST. Each time one is
--    seen, we decrement the counter to keep it consistent.
--
-- 3. **`end` vs recursive closers**  
--    Nested recursive blocks end with `in`, but top recursive blocks end with
--    `end`. We must account for this. Fortunately, syntax rules help: if an
--    `end` appears while inside a recursive block with an active counter, it
--    can only close a `switch` or the top recursive. To decide, we maintain a
--    `switch` count stack. If the stack is empty, the `end` closes the recursive;
--    otherwise, it closes a `switch`.  
--    We can be confident that `end` will not prematurely close a recursive block
--    because the counter ensures that `in` closers are still correctly tracked.  
--    Top-level constructs like `let` or `type` that are not closed with `in`
--    are not a problem, since we never enter a recursive block at the top level.
--
-- For more details on the recursive stream internals, see `recursive-stream.mc`.

include "mexpr/ast.mc"
include "mexpr/pprint.mc"

include "./token-readers.mc"
include "./sem-map.mc"
include "./recursive-stream.mc"

include "../../mast-gen/mast.mc"

-- Holds the MAST and the recursive data stream used during lexing.
type LexingCtx = { ast: MAst, recursiveDataStream: RecursiveDataStream }

-- Creates a new lexing context from a MAST.
let lexingCtxNew: MAst -> LexingCtx = lam ast.
    { ast = ast, recursiveDataStream = createRecursiveDataStream ast.expr }

-- A list of tokens paired with their position in the source file.
type TokenStream = use TokenReader in [(Token, Pos)]

-- Result of lexing: the token stream and the updated context.
type LexOutput = { stream: TokenStream, ctx: LexingCtx }

-- Lexical analysis: converts a raw source string into a stream of (token, position) pairs.
let lex : use TokenReader in LexingCtx -> String -> LexOutput = use TokenReader in lam ctx. lam stream.
    recursive let nthWord : String -> Int -> String = lam stream. lam n.
        match next stream pos0 with { stream = stream, token = token } in
        switch token
        case TokenEof {} then parsingWarn "EOF detected during lexing."; ""
        case TokenWord { content = content } then
             if eqi 0 n then content
             else nthWord stream (subi n 1)
        case _ then nthWord stream n
        end
    in

    recursive let lex : LexingCtx -> [Int] -> String -> Pos -> TokenStream -> Int -> LexOutput =
        lam ctx. lam stack. lam stream. lam pos. lam acc. lam switchCount.
        switch next stream pos
        case { token = TokenEof {} & token } then { stream = reverse (cons (token, pos) acc), ctx = ctx }
        
        case { token = token, stream = stream, pos = newPos } then
             let enderCandidate = TokenRecursiveEnder { ender = lit token } in
             let default = (stack, token, ctx, switchCount) in
             let switchRes = switch token
                 case TokenWord { content = "recursive" } then
                     match recursiveDataStreamNext ctx.recursiveDataStream with
                     { inCount = inCount, stream = newStream } in
                         (cons inCount stack, token, { ctx with recursiveDataStream = newStream }, switchCount)
                 case TokenWord { content = "lang" } then
                     let semStream = getSemMap stream in
                     match nthWord stream 0 with langName in
                     let stream = recursiveDataStreamLang ctx.recursiveDataStream langName semStream in
                     (stack, token, { ctx with recursiveDataStream = stream }, switchCount)
                 case TokenWord { content = "sem" } then
                     match nthWord stream 0 with semName in
                     let stream = recursiveDataStreamSem ctx.recursiveDataStream semName in
                     (stack, token, { ctx with recursiveDataStream = stream }, switchCount)
                 case TokenWord { content = "match" | "case" | "if" | "use" } then
                      let stack = match stack with [h] ++ t then cons (addi 1 h) t else stack in
                      (stack, token, ctx, switchCount)
                 case TokenWord { content = ("in" | "then" | ";" | "switch") & content } then 
                     match stack with [c] ++ stack then
                         let switchCount = addi switchCount (match content with "switch" then 1 else 0) in
                         if eqi 0 c then (stack, enderCandidate, ctx, switchCount)
                         else (cons (subi c 1) stack, token, ctx, switchCount)
                     else default
                 case TokenWord { content = "end" } then
                     switch stack
                     case [_] ++ rest then
                         if eqi switchCount 0 then (rest, enderCandidate, ctx, switchCount)
                         else (stack, token, ctx, subi switchCount 1)
                     case _ then default -- We are closing a lang
                     end
                 case _ then default
                 end
             in
             match switchRes with (stack, token, ctx, switchCount) in
             lex ctx stack stream newPos (cons (token, pos) acc) switchCount
        end
    in
    lex ctx [] stream { x = 0, y = 0 } [] 0
