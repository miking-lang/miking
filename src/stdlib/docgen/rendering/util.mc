-- This module defines primitives used by the renderer to handle objects
-- during the documentation generation process.

include "./rendering-data.mc"
include "./renderers/objects-renderer.mc"
include "../global/objects.mc"
include "../global/util.mc"

-- During rendering, we generate one page and one documentation block per child.
-- But what if two children have the same name and the same form?
-- Since they share the same name, namespace and form, they will end up with the same URL.
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
let removeDoubleNames : RenderingOptions -> [RenderingData] -> [RenderingData] = lam opt. lam children.
    use ObjectsRenderer in

    type MergeFoldArg = { doc: String, prev: String, children: [RenderingData] } in
    -- Merging the documentations of consecutive same elements.
    let merged = foldl
    (
        lam arg. lam child.
        match arg with { doc = doc, prev = prev, children = children } in
        let obj = child.obj in
        let url = objGetMyLink obj opt in
        if not (objHasName obj) then
           { arg with doc = "", children = cons child children, prev = "" }
        else if eqString url prev then
           let doc = if eqString (objDefaultDoc ()) doc then "" else doc in
           let newDoc = objTryGetDoc child.obj in
           let doc = concat doc newDoc in
           let child = { child with obj = objWithDoc child.obj doc } in
           { arg with doc = doc, children = cons child children }
        else
           { arg with doc = objDoc child.obj, children = cons child children, prev = url }
        
    ) { doc = "", prev = "", children = [] } children in

    type SanitizeFoldArg = { saw: HashMap String (), children: [RenderingData] } in
    -- Removing double names
    let sanitized =  foldl
    (
        lam arg. lam child.
        match arg with { saw = saw, children = children } in
        let url = objGetMyLink child.obj opt in
        
        if objHasName child.obj then
           match hmLookup url saw with Some _ then arg
           else { children = cons child children, saw = hmInsert url () saw }
        else { arg with children = cons child children }
    ) { children = [], saw = hashmapEmpty () } merged.children in
    sanitized.children
        

-- Groups `RenderingData` nodes into categories by their form.
-- This structure is useful for organizing sections in the documentation.
type RenderingDataSet = use Objects in {
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
let buildSet: [RenderingData] -> RenderingDataSet =
    use Objects in
    lam children.
    recursive
    let buildSet = lam set. lam children.
        switch children
        case [child] ++ children then
            let switchRes = switch child.obj
            case ObjLet {} then { set with sLet = cons child set.sLet }
            case ObjLang {} then { set with sLang = cons child set.sLang }
            case ObjSem {} then { set with sSem = cons child set.sSem }
            case ObjSyn {} then { set with sSyn = cons child set.sSyn }
            case ObjCon {} then { set with sCon = cons child set.sCon }
            case ObjMexpr {} then { set with sMexpr = cons child set.sMexpr }
            case ObjType {} then { set with sType = cons child set.sType }
            case ObjUtest {} then { set with sUtest = cons child set.sUtest }
            case ObjInclude {} then
                let set = if objIsStdlib child.obj then
                    { set with sLibInclude = cons child.obj set.sLibInclude }
                  else
                    { set with sInclude = cons child.obj set.sInclude }
                in
                set
            end in
            match switchRes with set in
            buildSet set children
        case [] then set
        end
    in buildSet { sLet = [], sLang = [],  sSem = [], sSyn = [], sCon = [], sMexpr = [], sInclude = [], sLibInclude = [], sType = [], sUtest = [] } (reverse children)
