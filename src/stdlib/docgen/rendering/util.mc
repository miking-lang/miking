-- # util.mc
--
-- This module defines primitives used by the renderer to handle objects
-- during the documentation generation process.

include "./rendering-types.mc"
include "../extracting/objects.mc"
include "../global/util.mc"

-- ## removeDoubleNames
--
-- During rendering, we generate one page and one documentation block per child.
-- But what if two children have the same name and the same kind?
-- Since they share the same name, namespace and kind, they will end up with the same URL.
-- However, two documentation blocks will still be generated, both pointing
-- toward the last child’s page.
--
-- This function catches all duplicate names among children with same namespace
-- and keeps only the last one. Moreover, if two children
-- with the same namespace are next to each other, we merge their documentation.
-- Otherwise, in this scenario:
--
-- -- Takes x and returns x + 1
-- sem semX: Int -> Int
-- sem semX = | x -> addi x 1
--
-- Since only the last sem remains, the previous documentation would be lost.
let removeDoubleNames : [RenderingData] -> [RenderingData] = lam children.
    type MergeFoldArg = { doc: String, prev: String, children: [RenderingData] } in
    -- Merging the documentations of consecutive same elements.
    let merged = foldl
    (
        lam arg. lam child.
        match arg with { doc = doc, prev = prev, children = children } in
        let namespace = objNamespace child.obj in
        if eqString namespace prev then
           let doc = concat doc (objDoc child.obj) in
           let child = { child with obj = objWithDoc child.obj doc } in
           { arg with doc = doc, children = cons child children }
        else
           { arg with doc = objDoc child.obj, children = cons child children, prev = namespace }
        
    ) { doc = "", prev = "", children = [] } children in

    type SanitizeFoldArg = { saw: HashMap String (), children: [RenderingData] } in
    -- Removing double names
    let sanitized =  foldl
    (
        lam arg. lam child.
        match arg with { saw = saw, children = children } in
        let namespace = objNamespace child.obj in
        match hmLookup namespace saw with Some _ then arg
        else { children = cons child children, saw = hmInsert namespace () saw }
    ) { children = [], saw = hashmapEmpty () } merged.children in
    sanitized.children
        



-- ## injectTests
--
-- Post-processes a list of `RenderingData` nodes to attach unit tests to their parent
-- documentation blocks.
-- - Iterates through children (`children`).
-- - Buffers any `RenderingData` elements that correspond to test code.
-- - When a new non-test block (`current`) is encountered, merges the buffered tests
--   into that block by:
--   * Concatenating the test code (`tests`) into the `tests` field
--   * Concatenating their raw rows (`row`) into the `rowTests` field
-- - Clears the buffer after attaching tests.
--
-- Returns: the transformed list of `RenderingData`, where test blocks are folded into
-- the corresponding parent documentation block.
let injectTests : [RenderingData] -> [RenderingData] = use ObjectKinds in lam children.
    type Arg = { current: Option RenderingData, acc: [RenderingData], tests: [RenderingData] } in

    -- - Takes the accumulated list, the current block, and buffered tests.
    -- - Extracts the "lastRow" of the last test, trimming trailing comments and empty lines.
    -- - Builds the final `tests` and `rowTests` strings by concatenating buffered test code.
    -- - Produces a new `RenderingData` with its tests attached, then pushes it into the accumulator.
    let pushChildInAcc: [RenderingData] -> RenderingData -> [RenderingData] -> [RenderingData] = lam acc. lam current. lam tests.
        let testsStr: (String, String) =
            match tests with [last] ++ tests then
                let lastRow = last.row in
                recursive let trimRow = lam row.
                  match row with [h] ++ t then
                        let l = strTrim h in
                        if strStartsWith "--" l then
                           trimRow t
                        else if eqString l "" then
                           trimRow t
                        else strJoin "\n" (reverse row)
                  else []
                in
                let lastRow = trimRow (reverse (strSplit "\n" lastRow)) in
                
                let row: String = join (map (lam t. t.row) (reverse tests)) in                            
                let tests: String = join (map (lam t. join [t.left, t.right, t.trimmed]) (reverse tests)) in
                (join [tests, last.left, last.right], concat row lastRow)
            else ("", "")
        in
        let current: RenderingData = { current with tests = testsStr.0, rowTests = testsStr.1 } in
        join [tests, [current], acc]
    in
                    
    let foldRes: Arg = foldl (lam arg. lam child.
        match arg with { current = current, acc = acc, tests = tests } in
        let isUtest = match objKind child.obj with ObjUtest {} then true else false in
        switch current
        case Some current then
             if isUtest then { arg with tests = cons child tests }
             else { arg with current = Some child, tests = [], acc = pushChildInAcc acc current tests }
        case None {} then
             if isUtest then { arg with acc = cons child acc }
             else { arg with current =  Some child }
        end
    ) { current = None {}, acc = [], tests = [] } children
    in
    
    let children = switch foldRes.current
        case Some current then pushChildInAcc foldRes.acc current foldRes.tests
        case None {} then foldRes.acc
        end
    in
    
    reverse children

-- ## RenderingDataSet
--
-- Groups `RenderingData` nodes into categories by their kind.
-- This structure is useful for organizing sections in the documentation.
type RenderingDataSet = {
    sUse: [Object],
    sLet: [RenderingData],
    sLang: [RenderingData],
    sSem: [RenderingData],
    sSyn: [RenderingData],
    sCon: [RenderingData],
    sMexpr: [RenderingData],
    sInclude: [Object],
    sLibInclude: [Object],
    sType: [RenderingData],
    sUtest: [RenderingData]
}

-- Constructs a `RenderingDataSet` from:
-- - A list of rendered children (`children`).
-- - Recursive block data (`recDatas`), extracted earlier.
let buildSet: [RenderingData] -> [[RenderingData]] -> RenderingDataSet = use ObjectKinds in lam children. lam recDatas.
    recursive
    let buildSet = lam set. lam children. lam recDatas.
        switch children
        case [child] ++ children then
            let switchRes = switch child.obj.kind
            case ObjUse {} then ({ set with sUse = cons child.obj set.sUse }, recDatas)
            case ObjLet {} then ({ set with sLet = cons child set.sLet }, recDatas)
            case ObjLang {} then ({ set with sLang = cons child set.sLang }, recDatas)
            case ObjSem {} then ({ set with sSem = cons child set.sSem }, recDatas)
            case ObjSyn {} then ({ set with sSyn = cons child set.sSyn }, recDatas)
            case ObjCon {} then ({ set with sCon = cons child set.sCon }, recDatas)
            case ObjMexpr {} then ({ set with sMexpr = cons child set.sMexpr }, recDatas)
            case ObjType {} then ({ set with sType = cons child set.sType }, recDatas)
            case ObjUtest {} then ({ set with sUtest = cons child set.sUtest }, recDatas)
            case ObjInclude {} then
                (if objIsStdlib child.obj then { set with sLibInclude = cons child.obj set.sLibInclude } else { set with sInclude = cons child.obj set.sInclude }, recDatas)
            case ObjRecursiveBloc {} then
                match recDatas with [children] ++ recDatas then
                    ({ set with sLet = concat children set.sLet }, recDatas)
                else
                   renderingWarn "Running out of recursive datas.";
                   (set, recDatas)
            end in
            match switchRes with (set, recDatas) in
            buildSet set children recDatas
        case [] then set
        end
    in buildSet { sUse = [], sLet = [], sLang = [],  sSem = [], sSyn = [], sCon = [], sMexpr = [], sInclude = [], sLibInclude = [], sType = [], sUtest = [] } (reverse children) (reverse recDatas)
