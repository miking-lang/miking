-- # Type Labeling Module
--
-- This module annotates objects in an `ObjectTree` with type information.
-- It uses the type stream system to assign types of lets and sems
-- The execution is using TypeStream defined in types-stream.mc to fetch types of each objects.    
--
-- We want to annotate each `let` and `sem`, for that we traverse our objects and there are concretely 5 cases:
--  - Let: We make a request to the type stream for the next `let` with the correct name. We ignore anything that has been skipped as it will only be anonymous names added by switch cases or `;`.
--  - Lang: When we encounter a `Lang`, we must prepare to encounter `sem`s. There are three main difficulties:
--      * The `sem`s are transformed into regular `let`s, but they are given the prefix `Langname_` before their name, which must be considered when fetching from the TypeStream.
--      * Miking merges all `sem`s with the same name into a single `let`, which contains a large `match`. Each pattern, however, appears in the original declaration order of the `sem`s.
--        Note that it is very common for a `sem` to be declared multiple times, especially when its type needs to be specified.
--      * And the biggest difficulty: `sem`s do not appear in the order of their declaration, although `sem`s with the same name do. Since we do not have access to the complete list of semantic names, although it would be possible, it would require granting the labeler lookahead rights, which we want to avoid. Therefore, we must ensure we properly handle skipped `sem`s.
--   When we encounter a `Lang`, we create a new `LangContext` initially containing the language name and a hashmap linking the `sem`s to a local context and their type.
--  - Sem: To handle the three problems addressed above, here is how we proceed. Each time we see a `sem`:
--      * We interpolate its name with the language name from the `LangContext`.
--      * If the `sem` is not present in the `semMap`, we fetch from the TypeStream, then pop the body of the `sem` from the TypeStream and create a new stream containing only the body of the `sem`. We will henceforth call these streams `temporary streams`. We then continue parsing recursively on this temporary stream without modifying the main stream which had the `sem` body popped from it.
--      After the recursive call, we add a new entry to the `LangContext`'s `semMap`, linking the `sem` name to its type (found using the first `next` call on the main type stream) and to the new temporary context resulting from the recursive call. This context may contain the definitions of other `sem`s declared with the same name but with different patterns.
--      * If the `sem` is in the `semMap`, we just continue labeling in the existing context. The `sem` type is also found in the hashmap, as all `sem`s with the same name have the same type.
--      * To handle the disorder in the appearance of `let`s, it is enough to add all skipped items that start with the prefix of the current language to the `semMap`, so that when we encounter them, they will find their stream in the `semMap`, and we then fall back to the previous case.

include "./types-stream.mc"
include "../extracting/objects.mc"
include "../global/util.mc"

let label : Logger -> ObjectTree -> MAst -> ObjectTree =
    use ObjectKinds in use TypeStream in use RemoveMetaVar in lam log. lam tree. lam ast.

    type SkippedContext = { ctx: TypeStreamContext, t: Type } in
    type LangContext = { langName: String, semMap: HashMap String SkippedContext } in
    type LabelRecRes = { ctx : TypeStreamContext, tree : ObjectTree, langContext : Option LangContext } in

    recursive let labelRec : TypeStreamContext -> String -> Option LangContext -> ObjectTree -> LabelRecRes =
        lam ctx. lam fileName. lam langContext. lam tree.
    
        type FoldRes = { ctx : TypeStreamContext, sons: [ObjectTree], langContext : Option LangContext } in
        let foldSons: [ObjectTree] -> Option LangContext -> TypeStreamContext -> FoldRes =
            lam sons. lam langContext. lam ctx.
                let fRes = foldl (
                    lam a: FoldRes. lam s: ObjectTree.
                    match labelRec a.ctx fileName a.langContext s with { ctx = ctx, tree = tree, langContext = langContext } in
                    { ctx = ctx, sons = cons tree a.sons, langContext = langContext }
                ) { ctx = ctx, langContext = langContext, sons = [] } sons in
                { fRes with sons = reverse fRes.sons } in
    
        let default = { tree = tree, ctx = ctx, langContext = langContext } in
        let buildRes = lam obj. lam ctx. lam langContext. lam sons. lam ty.
            let ty = match ty with Some t then Some (removeMetaVarType t) else None {} in
            {
                    tree = ObjectNode {
                            sons = sons,
                            obj = objSetType obj ty
                            },
                    ctx = ctx,
                    langContext = langContext
                }
        in
    
        match tree with ObjectNode { obj = { kind = kind, name = name, namespace = namespace } & obj, sons = sons } then
            let warn = lam name. labelingWarn (join ["Found a typeless token in ", fileName, " with name ", name, "."]) in
            switch kind
            case ObjLet {} then
                match typeStreamNext name ctx with { t = t, ctx = ctx } in
                (match t with None {} then warn name else ());
                match foldSons sons (None {}) ctx with { ctx = ctx, sons = sons} in
               buildRes obj ctx langContext sons t
            case ObjSem {} then
                match langContext with Some { langName = langName, semMap = semMap } then
                    let prefix = join ["v", langName, "_"] in
                    let name = concat prefix name in
                    match hmLookup name semMap with Some { t = t, ctx = tmpCtx } then
                        match foldSons sons (None {}) tmpCtx with { ctx = tmpCtx, sons = sons} in
                        let semMap = hmInsert name { ctx = tmpCtx, t = t } semMap in
                        buildRes obj ctx (Some { langName = langName, semMap = semMap }) sons (Some t)        
                    else
                        let updateLangContext = lam semMap. lam skipped.
                            let semMap =  foldl (lam semMap. lam skip.
                                hmInsert skip.name { t = skip.t, ctx = typeStreamFromExpr skip.body } semMap)
                                semMap (filter (lam s. strStartsWith prefix s.name) skipped) in
                            Some { semMap = semMap, langName = langName }
                        in

                        switch typeStreamNext name ctx    
                        case { t = Some t, ctx = ctx, skipped = skipped } then
                            match typeStreamPop ctx with { ctx = ctx, ast = ast } in
                            let tmpCtx = typeStreamFromExpr ast in
                            match foldSons sons (None {}) tmpCtx with { ctx = tmpCtx, sons = sons} in
                            let semMap = hmInsert name { t = t, ctx = tmpCtx } semMap in
                            buildRes obj ctx (updateLangContext semMap skipped) sons (Some t)    
                        case { t = None {}, ctx = ctx, skipped = skipped } then
                            warn name;
                            buildRes obj ctx (updateLangContext semMap skipped) sons (None {})
                        end                    
                else
                    labelingWarn "Lang context in None, should never happend while labeling a Sem"; default
            case ObjLang {} then
                let langContext = Some { langName = name, semMap = hashmapEmpty () } in
                match foldSons sons langContext ctx  with { ctx = ctx, sons = sons } in
                buildRes obj ctx (None {}) sons (None {})
            case ObjInclude { pathInFile = pathInFile } then
                switch sons
                case [program] then    
                    log (concat "Labeling in" namespace);
                    match labelRec ctx pathInFile (None {}) program with { ctx = ctx, tree = tree } in
                    log (concat namespace " is labeled");
                    buildRes obj ctx langContext [tree] (None {})
                case [] then default
                case _ then labelingWarn "Include objects should all have 0 or 1 son."; default
                end
            case _ then
                match foldSons sons (None {}) ctx with { ctx = ctx, sons = sons} in
                buildRes obj ctx langContext sons (None {})            
            end
        else default
    in
    let obj = objTreeObj tree in
    let filePath = objAbsolutePath obj in
    log (concat "Labeling on " filePath);
    let ctx = buildTypeStream ast in
    log "Labeling types..";
    (labelRec ctx filePath (None {}) tree).tree

