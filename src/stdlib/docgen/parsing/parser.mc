-- # Parser: Building a DocTree from a Source File 
--
-- This module defines a parser that reads a file and produces a `DocTree`,
-- a hierarchical structure of tokens annotated with formatting state.  
-- See doc-tree.mc for more information.
--
-- ## General Idea
-- The parser segments the code using a markup system: some keywords open new
-- nodes in the tree, and other keywords close them.  
-- 
-- Example:
-- ```miking
-- let x = addi 3 8 in
-- ```
-- Here, `let` opens a new node (a "let block"). Later, when the parser
-- encounters `in`, it recognizes it as a breaker for this block and closes it.
--
-- The detection of opening words is handled here in the parser, while the
-- decision of which breakers apply in the current context is delegated to
-- breaker-choosers.mc. This separation allows us to handle nested structures,
-- language extensions, and special keywords without duplicating logic.
--
-- ## Breaker Types
-- When a breaker is encountered, three cases are possible:
--
-- 1. **Local break**  
--    Only the current block is closed.  
--    Example:  
--    ```miking
--    lang A
--    end
--    ```  
--    The keyword `end` closes only the `lang` block.
--
-- 2. **Global break**  
--    The breaker closes the current block **and one or more parent blocks**.  
--    Example:  
--    ```miking
--    lang A
--        sem x = ...
--    end
--    ```  
--    Here, `end` breaks both the `sem` and the `lang` block.
--    In this context, we also have to decides to which block `lang` belongs.
--
-- 3. **Hard break**  
--    A new keyword forces a reinterpretation of the tree.  
--    Example:  
--    ```miking
--    let x = 1
--    let y = 2
--    lang A
--    end
--    ```  
--    Initially, the second `let` is assumed to be nested (`let ... in`).
--    But encountering `lang` later reveals that `let y = 2` was actually
--    a **top-level let**, so the parser restructures the tree to reflect this.
--    To handle this case a little bit tricky, we use back tracking with an accumlator.
--
-- ## Includes
-- Includes are handled through the IncludeSet API from the mast-gen module.
-- The parser first processes the include header of the file and recursively
-- parses all included files. Each include is represented in the DocTree by
-- an `DocTreeIncludeNode`, which may either contain the included file’s tree or be
-- marked as already visited to prevent infinite loops.
--
-- ## Result
-- The final output is a `DocTree` for the entire project. This tree preserves
-- block structure and include relationships


include "./lexing/lexer.mc"

include "./doc-tree.mc"

include "../global/util.mc"
include "../options/docgen-options.mc"

include "seq.mc"
include "hashmap.mc"
include "fileutils.mc"
include "hashmap.mc"
include "sys.mc"


-- # The parse function
-- - Takes in input a path to a miking program
-- - And the MAST of this program
-- - Returns the corresponding `DocTree`.
-- - Assume that the entry is a valid Miking program.
let parse : Logger -> String -> MAst -> DocTree = use TokenReader in use BreakerChooser in lam log. lam basePath. lam ast.
    -- Keywords that start new blocks (head snippets)
    -- Using HashSet to improve performances
    let headSnippets =
        foldl
        (lam m. lam k. hmInsert k () m)
            (hashmapEmpty ())
        ["let", "lang", "type", "syn", "sem", "con", "mexpr", "use", "utest", "recursive"] in

    -- Extra breakers (manually added).
    -- We would like to ignore `switch` keyword, but we cant becauses it ends with then end keyword. It may break a lang block in some situations.
    let breakerAdder = [("switch", ["end"]), ("match", ["then", "in"]), ("if", ["then"])] in

    -- Snippet type = partial parse result
    type Snippet = {
        pos: Pos,
        tree: [DocTree],
        stream: TokenStream,
        breaker: String,
        toAdd: [DocTree],
        absorbed: Bool
    } in

    type ParseRes = {
        includeSet: IncludeSet (),
        lexingCtx: LexingCtx,
        tree: [DocTree]
    } in
    
    let parseRes2tree : ParseRes -> String -> DocTree = lam parseRes. lam progName.
        DocTreeNode {
            sons = parseRes.tree,
            pos = { x = 1, y = 1 },
            token = TokenProgram {
                content = progName,
                includeSet = parseRes.includeSet
            },
            state = StateProgram {}
        }
    in
    
    -- Access top of breaker stack
    let topState = lam breakers. let h = (head breakers).0 in h.state in
    let topBreakers = lam breakers. let h = (head breakers).0 in h.breakers in
    let baseBreaker = [({ breakers = [""], state = StateProgram {} }, false)] in
    
    recursive
    -- This function is parsing the text of the file without any includes
    let parseStream: TokenStream -> Pos -> [(Breaker, Bool)] -> [DocTree] -> Snippet =
        lam oldStream. lam oldPos. lam breakers. lam treeAcc.

            -- Main recursion:
            -- stream = input string
            -- breakers = stack of current block contexts
            -- treeAcc = accumulated tree so far
            --
            -- Builds a snippet when a head snippet token is encountered
            let buildSnippet : (Token -> TokenStream -> Pos -> [(Breaker, Bool)] -> [DocTree] -> Snippet) = lam token. lam stream. lam pos. lam breakers. lam treeAcc.
                let lword = content token in
                let oldState = topState breakers in
                let breakers = cons ((choose (oldState, lword, pos)), false) breakers in
                let newState = topState breakers in
    
                -- Parse the snippet content
                let isTop = eqi 2 (length breakers) in
                let snippet = parseStream stream pos breakers [] in
                let reStructureTest = reStructureTree (newState, snippet.breaker) in
                let continueTest = or isTop (continue (newState, snippet.breaker)) in
                let newState = switchVersion (newState, snippet.breaker) in
    
                -- Handle continue case (normal exit)
                if continueTest then
                    match (match snippet.stream with [(last, lastPos)] ++ stream then (last, lastPos, stream) else (TokenEof {}, pos, [])) with (last, lastPos, lastStream) in
    
                    match (if and (not snippet.absorbed) (absorbIt (newState, content last)) then
                        let leaf = DocTreeLeaf { token = last, state = newState, pos = lastPos } in
                        { stream = lastStream, newPos = lastPos, sons = concat snippet.tree [leaf] }
                    else
                        { stream = snippet.stream, newPos = snippet.pos, sons = snippet.tree }) with
                    { stream = stream, sons = sons, newPos = newPos } in

                    let docNode = DocTreeNode { sons = sons, pos = pos, token = token, state = newState } in
                    let tree = reverse (cons docNode snippet.toAdd) in
                    parseStream stream newPos (tail breakers) (concat tree treeAcc)
                else
                    -- Handle hard break
                    let docNode = DocTreeNode {
                        pos = pos,
                        sons = snippet.tree, token = token,
                        state = newState
                    } in
                    let concatToAdd = cons docNode snippet.toAdd in
                    {
                        snippet with
                        toAdd = if reStructureTest then concatToAdd else [],
                        tree = if reStructureTest then reverse treeAcc else reverse (concat (reverse concatToAdd) treeAcc)
                    }
            in

            switch oldStream 
            case [(TokenEof {}, pos)] then
                { tree = reverse treeAcc, pos = pos, stream = oldStream, breaker = "", toAdd = [], absorbed = true }
            case [(token, pos)] ++ stream then

            let lword = content token in
            let state = topState breakers in
        
            if any (eqString lword) (topBreakers breakers) then
                if (head breakers).1 then
                    let acc = (cons (DocTreeLeaf { token = token, state = state, pos = pos }) treeAcc) in
                    parseStream stream pos (tail breakers) acc
                else
                    let absorb = absorbIt (state, lword) in
                    {
                        tree = reverse (if absorb then
                                            cons (DocTreeLeaf { token = token, state = state, pos = pos }) treeAcc
                                        else treeAcc),
                        stream = if absorb then stream else oldStream,
                        absorbed = absorb,
                        pos = if absorb then pos else oldPos,
                        breaker = lword, toAdd = []
                    }
            else match find (lam w. eqString w.0 lword) breakerAdder with Some b then
                -- Extra breakers (example: switch/end)
                parseStream
                    stream
                    pos
                    (cons ( { breakers = b.1, state = state }, true ) breakers)
                    (cons (DocTreeLeaf { token = token, state = state, pos = pos }) treeAcc)
            else if hmMem lword headSnippets then
                -- If head snippet -> build new snippet block
                buildSnippet token stream pos breakers treeAcc
            else
                -- Default case: accumulate leaf
                parseStream stream pos breakers (cons (DocTreeLeaf { token = token, state = state, pos = pos }) treeAcc)
            end
    -- Here we parse the include header of the file, jump in all the includes before processing the actual code.
    let parse: IncludeSet () -> String -> LexingCtx -> ParseRes = lam includeSet. lam loc. lam lexingCtx.
        match includeSetGetValue ast.includeSet loc with Some { includes = includes, headerTokens = headerTokens, fileText = fileText } then
        
        let headerDocTree = foldl (lam arg: ParseRes. lam token.
            match arg with { lexingCtx = lexingCtx, includeSet = includeSet, tree = tree } in
            match token with { token = token, pos = pos } in

            let go : ParseRes -> DocTree -> ParseRes = lam arg. lam doctree. { arg with tree = cons doctree arg.tree } in
            match token with TokenInclude { content = content } then
                match includeSetInsert includeSet loc content () with
                { includeSet = includeSet, inserted = inserted, path = path, isStdlib = isStdlib } in
                let insertResult = if inserted then
                    match parse includeSet path lexingCtx with
                    { includeSet = includeSet, lexingCtx = lexingCtx } & parseRes in
                    ({ arg with includeSet = includeSet, lexingCtx = lexingCtx }, Some (parseRes2tree parseRes path))
                else
                    (arg, None {}) in
                match insertResult with (arg, tree) in
                go arg (DocTreeIncludeNode { token = token, tree = tree, state = StateProgram {}, path = path, isStdlib = isStdlib, pos = pos })
            else
                go arg (DocTreeLeaf { token = token, state = StateProgram {}, pos = pos })
            ) { includeSet = includeSet, lexingCtx = lexingCtx, tree = [] } headerTokens
        in
        match headerDocTree with { includeSet = includeSet, tree = headerTree, lexingCtx = lexingCtx } in
        log (concat "Beginning of parsing stage on " loc);
        match lex lexingCtx fileText with { stream = stream, ctx = lexingCtx } in

        let snippet = parseStream stream { x = 1, y = 1 } baseBreaker headerTree in
        { includeSet = includeSet, lexingCtx = lexingCtx, tree = snippet.tree }

        else
            iter printLn (hmKeys ast.includeSet.set);
            error (join ["Found an invalid path during parsing: ", loc, "."])
    in
    
    let lexingCtx = lexingCtxNew ast in

    match goHere pwd basePath with { path = basePos } in

    let includeSet = includeSetNew (dirname basePos) in

    match includeSetInsert includeSet "." basePath () with { includeSet = includeSet } in    

    match parse includeSet basePath lexingCtx with { includeSet = includeSet, tree = tree } & parseRes in
    log (join ["Parsing is over, computed prefix: ", includeSetPrefix includeSet, "."]);
    parseRes2tree parseRes basePath
