-- # Recursive Stream
--
-- This module implements the recursive-stream.
-- The idea is simple: we take as input a compiler expression representing a
-- Miking program, and use it as a stack. For example, if we encounter a
-- `match`, we push its 3 expressions onto the stack in the correct order so
-- that traversal is performed properly.
--
-- The main goal is to compute the number of `in` tokens present in each
-- recursive block. To do this, we traverse down the stack until reaching the
-- next `TmRecLets`. Once found, we traverse all its bindings and count the
-- expected number of `in` tokens.
--
-- Nested recursive blocks require special care. When we encounter a recursive
-- block inside another, we pause the current counting and compute the number
-- of `in`s for the nested block separately. The result is cached and stored
-- in an array that can be reused when fetching the next `in` count. This
-- avoids double counting.
--
-- Example:
--
-- recursive
--     let x =
--         recursive
--             let y = let z = 2 in 3
--         in
--         4
-- end
--
-- The inner block counts only one `in` (for `z`). The parent block also counts
-- one `in` (closing the child recursive), but does not include the inner `z`.
--
-- This approach also handles merged semantics correctly. When the parser
-- replaces `lang` with a recursive block (each binding is a `sem`), we must
-- adapt. For example:
--
-- lang A
-- sem x = | 1 -> ...
-- sem y = | _ -> ...
-- sem x = | 2 -> ...
-- end
--
-- The compiler’s AST may contain only a single `sem` for `x`. During lexing,
-- however, we see `sem y` in between. The solution: whenever we encounter a
-- `lang`, we locate it in the AST and build a cache array for each semantic.
-- These are stored in a hashmap linking semantic names to their caches. When
-- the lexer encounters a `sem`, it retrieves the corresponding cache and
-- switches appropriately.
--
-- Finally, the sem-stream is used when generating the lang map. We keep only
-- the last *n* recursive blocks (where *n* is the expected number). The older
-- blocks are discarded, as they were introduced during assembly.

include "mexpr/ast.mc"
include "../../global/util.mc"
include "./sem-map.mc"

lang RDSInterface = MExprAst

    -- Maps semantic names to recursive block counts.
    type RDSMap = HashMap String [Int]

    -- Represents the recursive data stream used to track expected `in` tokens.
    type RDS = {
         stack: [Expr],
         cache: [Int],
         langMap: RDSMap,
         currentSem: String,
         langName: String
    }

    -- Removes a prefix before the first '_' in a string.
    sem removePrefix: String -> String
    sem removePrefix =
    | name -> reverse (splitOnR (eqChar '_') (reverse name)).left 
    
    -- Creates a new recursive data stream from an expression.
    sem createRDS: Expr -> RDS
    sem createRDS =
    | expr -> { stack = [expr], cache = [], currentSem = "", langName = "", langMap = hashmapEmpty () }

    -- Result type for computing the next recursive block count, private usage, use rdsNext instead.
    type DataStreamComputeNextRes = {
         stream: RDS, -- New stream
         acc: [Int],                  -- The row cache
         map: RDSMap, -- A map binding each rec branchs to its cache
         inCount: Int                 -- The actual number of ins.
    }

    -- Computes the next result, is essentially called by rdsComputeNext.
    sem rdsWork: Option SemMap -> Bool -> [Int] -> [Expr] -> Int -> { acc: [Int], inCount: Int, stack: [Expr], map: RDSMap }
    sem rdsWork semMap first acc =
    | [] -> lam inCount. { inCount = inCount, acc = acc, stack = [], map = hashmapEmpty () }

    -- Result type for fetching the next recursive count. 
    type RDSNextRes = { inCount: Int, stream: RDS }

    -- Computes the next recursive block count from the data stream.
    sem rdsComputeNext: RDS -> Option SemMap -> DataStreamComputeNextRes
    sem rdsComputeNext =
    | stream -> lam semMap.
        match rdsWork semMap true [] stream.stack 0 with { map = map, acc = acc, inCount = inCount, stack = stack } in
        { inCount = inCount, stream = { stream with stack = stack }, map = map, acc = acc }


    -- Returns the next recursive count from the stream, will take from the cache if not empty.
    sem rdsNext: RDS -> RDSNextRes
    sem rdsNext =
    | stream ->
        match stream.cache with [inCount] ++ cache then
            { inCount = inCount, stream = { stream with cache = cache } } 
        else 
            match rdsComputeNext stream (None {}) with { acc = acc, inCount = inCount, stream = stream } in
            { inCount = inCount, stream = { stream with cache = acc } }


    -- Called when encountering a `lang` keyword. The argument `langName` must be
    -- the identifier following `lang`.
    --
    -- The function first calls `rdsComputeNext` to access the
    -- bindings map (other returned data can be ignored).
    --
    -- Because the Miking compiler prunes all `lang` definitions that contain no
    -- `sem`, we face three cases:
    -- 1. The `lang` contains no `sem` *and* it is the last recursive of the file.
    --    The stream will return an empty map.
    -- 2. The `lang` contains no `sem`, but another recursive follows. We detect
    --    this by checking whether one of the binding names starts with
    --    `v$langName_`, which is the prefix of all sem identifiers.
    -- 3. Default case: the stream is updated with a map binding each `sem` to its
    --    recursive blocks. The `langName` field is set so we know we are inside a
    --    `lang`, and `currentSem` is reset to `""`. This also allows us to tell if
    --    the next `sem` is the first one.
    --
    -- In the first two cases, the function simply returns the unchanged stream.
    sem rdsLang: RDS -> String -> SemMap -> RDS
    sem rdsLang =
    | oldStream -> lam langName. lam semMap.
        match rdsComputeNext oldStream (Some semMap) with { map = map, stream = stream } in
        match hmKeys map with [h] ++ _ then
            if strStartsWith (join ["v", langName, "_"]) h then
               (match stream.cache with [] then () else parsingWarn "The cache should be empty at this point");
               { stream with langMap = map, langName = langName, currentSem = "" }
            else oldStream
        else oldStream

    -- Called when encountering a `sem` keyword. The argument `semName` must be
    -- the identifier following `sem`.
    --
    -- We want to switch the cache and update the `langMap` if needed. Two cases:
    -- 1. If `currentSem` is `""`, this is the first `sem`. We simply fetch its
    --    cache from the map.
    -- 2. Otherwise, we update the `langMap` by storing the cache of the previous
    --    `sem` under its name, then switch to the cache of the new `sem`. If we
    --    later encounter the same `sem` again, it will reuse the updated cache.
    sem rdsSem: RDS -> String -> RDS
    sem rdsSem =
    | stream -> lam semName.
        let semName = join ["v", stream.langName, "_", semName] in
    
        let stream = if eqString "" stream.currentSem then stream else
           { stream with langMap = hmInsert stream.currentSem stream.cache stream.langMap }
        in
        
        match hmLookup semName stream.langMap with Some cache then
            { stream with cache = cache, currentSem = semName }
        else
            parsingWarn (join ["semName ", semName, " is not in the langMap of the lang ", stream.langName, "."]);
            stream
end


lang RDSFullIgnore = RDSInterface

    sem rdsWork semMap first acc =
    | [TmVar {} | TmConst {} | TmNever {} | TmPlaceholder {} ] ++ rest -> lam inCount.
        rdsWork semMap first acc rest inCount 
        
end

lang RDSSimpleIgnore = RDSInterface

    sem rdsWork semMap first acc =
    | [TmLam { body = e } | TmConApp { body = e } | TmDecl { decl = DeclExt {}, inexpr = e}] ++ rest -> lam inCount.
        rdsWork semMap first acc (cons e rest) inCount 
        
end

lang RDSDoubleIgnore = RDSInterface

    sem rdsWork semMap first acc =
    | [TmApp { lhs = e2, rhs = e1 } | TmRecordUpdate { rec = e1, value = e2 }] ++ rest -> lam inCount.
        rdsWork semMap first acc (concat [e1, e2] rest) inCount 
        
end

lang RDSTripleIgnore = RDSInterface

    sem rdsWork semMap first acc =
    | [TmMatch { target = e1, thn = e2, els = e3 }] ++ rest -> lam inCount.
        rdsWork semMap first acc (concat [e1, e2, e3] rest) inCount 
        
end

lang RDSRecord = RDSInterface

    sem rdsWork semMap first acc =
    | [TmRecord { bindings = map }] ++ rest -> lam inCount.
        rdsWork semMap first acc (concat (mapValues map) rest) inCount 
        
end

lang RDSSeq = RDSInterface

    sem rdsWork semMap first acc =
    | [TmSeq { tms = arr }] ++ rest -> lam inCount.
        rdsWork semMap first acc (concat arr rest) inCount 
        
end
    
lang RDSSimpleConsider = RDSInterface

    sem rdsWork semMap first acc =
    | [TmDecl { decl = DeclType {} | DeclConDef {}, inexpr = e}] ++ rest -> lam inCount.
        rdsWork semMap first acc (cons e rest) (addi 1 inCount) 
        
end

lang RDSDoubleConsider = RDSInterface

    sem rdsWork semMap first acc =
    | [TmDecl { decl = DeclLet { body = e1 }, inexpr = e2}] ++ rest -> lam inCount.
        rdsWork semMap first acc (concat [e1, e2] rest) (addi 1 inCount)

end


lang RDSTripleConsider = RDSInterface

    sem rdsWork semMap first acc =
    | [TmDecl { decl = DeclUtest { test = e1, expected = e2, tusing = None {}, tonfail = None {} }, inexpr = e3}] ++ rest -> lam inCount.
        rdsWork semMap first acc (concat [e1, e2, e3] rest) (addi 1 inCount)

end

lang RDSQuadrupleConsider = RDSInterface

    sem rdsWork semMap first acc =
    | [TmDecl { decl = DeclUtest { test = e1, expected = e2, tusing = Some e3, tonfail = None {} }
                     | DeclUtest { test = e1, expected = e2, tusing = None {}, tonfail = Some e3 }, inexpr = e4}] ++ rest -> lam inCount.
        rdsWork semMap first acc (concat [e1, e2, e3, e4] rest) (addi 1 inCount)

end

lang RDSQuintupleConsider = RDSInterface

    sem rdsWork semMap first acc =
    | [TmDecl { decl = DeclUtest { test = e1, expected = e2, tusing = Some e3, tonfail = Some e4 }, inexpr = e5 }] ++ rest -> lam inCount.
        rdsWork semMap first acc (concat [e1, e2, e3, e4, e5] rest) (addi 1 inCount)

end


lang RDSRec = RDSInterface
    sem rdsWork semMap first acc =
    | [TmDecl { decl = DeclRecLets { bindings = bindings }, inexpr = inexpr }] ++ rest -> lam inCount.
        type Arg = { recLetCount: Int, acc: [Int], map: RDSMap } in
        let foldRes = foldl (lam arg: Arg. lam node.
            let name = removePrefix node.ident.0 in
            match rdsWork semMap false [] [node.body] 0 with { inCount = inCount, acc = subAcc } in
            let subAcc = match (first, semMap) with (true, Some semMap) then
                match hmLookup name semMap with Some count then
                    if lti (length subAcc) count then
                       parsingWarn (join ["The number of recursive in the sem (", int2string (length subAcc), ") is lower than the counter in the semMap (", int2string count, ")."]);
                       subAcc
                    else
                        subsequence subAcc 0 count
                else subAcc
            else subAcc
            in
            let map: RDSMap = hmInsert node.ident.0 (reverse subAcc) arg.map in
            { recLetCount = addi inCount arg.recLetCount, acc = concat subAcc arg.acc, map = map }
        ) { recLetCount = 0, acc = [], map = hashmapEmpty () } bindings in
        if first then
           { acc = reverse foldRes.acc, inCount = foldRes.recLetCount, stack = cons inexpr rest, map = foldRes.map }
        else
           let acc = join [foldRes.acc, [foldRes.recLetCount], acc] in
           rdsWork semMap false acc (cons inexpr rest) inCount
end

lang RecursiveDataStream = RDSFullIgnore + RDSSimpleIgnore + RDSDoubleIgnore + RDSTripleIgnore + RDSSeq + RDSRecord + RDSSimpleConsider + RDSDoubleConsider + RDSTripleConsider + RDSQuadrupleConsider + RDSQuintupleConsider + RDSRec end



