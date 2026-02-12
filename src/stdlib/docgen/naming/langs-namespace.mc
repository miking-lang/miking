include "../global/util.mc"
include "../global/logger.mc"
include "../global/objects.mc"
include "./generic-namespace-set.mc"

type LangId = Int

-- For now we only store the names.
type LangNamespace = use Objects in {
     objNamespace: String,
     objIsStdlib: Bool,
     
     parents: [LangId],

     syns: [Object],
     sems: [Object],
     types: [Object]
}


let langNamespaceDefault : LangNamespace = {
    objNamespace = "",
    objIsStdlib = false,

    parents = [],

    syns = [],
    sems = [],
    types = []
}

type LangNamespaceDatas = {
    -- The full rebuilt namespace
    full: LangNamespace,
    -- Only what was already in the namespace
    explicit: LangNamespace,
    -- Only what have been added
    implicit: LangNamespace
}

type LangNamespaceSet = NamespaceSet LangNamespaceDatas

let langNamespaceGetById : LangNamespaceSet -> Id -> Option LangNamespace =
    lam set. lam id.
    optionMap (lam d. d.full) (namespaceSetGetById set id)

let langNamespaceSetBuildNamespace : LangNamespaceSet -> LangNamespace -> [String] -> LangNamespace =
    lam set. lam langNamespace. lam parents.
    let parents = map (lam langName.
        match namespaceSetNameToId set langName with Some id then id
        else namingWarn "Parent language does not exist."; 0) parents in
    { langNamespace with parents = parents }

let langNamespaceSetInsert : LangNamespaceSet -> String -> LangNamespace -> LangNamespaceSet =
    lam set. lam name. lam namespace.
    use Objects in

    let synGetter = (lam namespace. namespace.syns) in
    let semGetter = (lam namespace. namespace.sems) in
    let typeGetter = (lam namespace. namespace.types) in

    -- Contains all the parents items.
    let rawParents = map
        (lam parent.
             match langNamespaceGetById set parent with Some namespace then
                 namespace
             else
                 namingWarn "Failed to retrieve parent language namespace.";
                 langNamespaceDefault
        ) namespace.parents in

    -- We prune the items only appearing in a single parent but not in the current object.
    -- Such an item is generally irelevant to document.
    let parents = map
        (lam parent.
         let otherParents =
             filter
             (lam other. not (eqString parent.objNamespace other.objNamespace)) rawParents
         in
         
         let prune =
             lam getter.
               filter
               (lam item.
                    let shareWith =
                      lam namespace.
                      any
                        (lam candidate.
                           eqString
                             (objName candidate)
                             (objName item))
                        (getter namespace)
                    in
                    or
                      (shareWith namespace)
                      (any shareWith otherParents)
                 )
                 (getter parent)
           in
             
         let syns = prune synGetter in
         let sems = prune semGetter in
         let types = prune typeGetter in
         
         { parent with syns = syns, sems = sems, types = types }
        ) rawParents
    in

    let unite : (LangNamespace -> [Object]) -> [Object] = lam getter.
        let union = foldl (lam acc. lam from.
                let field = getter from in
                foldl (lam acc. lam obj.
                    let name = objName obj in
                    let obj =
                        match hmLookup name acc
                        with Some inner then objMerge inner obj
                        else obj
                    in
                    hmInsert name obj acc 
                ) acc field
            ) (hashmapEmpty ()) (cons namespace parents) in
        hmValues union
    in

    let intersect : (LangNamespace -> [Object]) -> [Object] = lam getter.
        let explicit = foldl (lam acc. lam arg. hmInsert (objName arg) arg acc) (hashmapEmpty ()) (getter namespace) in
        let intersect = foldl (lam acc. lam from.
                let field = getter from in
                foldl (lam acc. lam obj.
                    let name = objName obj in
                    match hmLookup name acc with Some inner then
                        let obj = objMerge inner obj in
                        hmInsert name obj acc
                    else acc
                ) acc field
            ) explicit parents in
        hmValues intersect
    in

    let diff : (LangNamespace -> [Object]) -> [Object] = lam getter.
        let explicit = foldl (lam acc. lam arg. hmInsert (objName arg) () acc) (hashmapEmpty ()) (getter namespace) in
        
        let diff = foldl (lam acc. lam from.
                let field = getter from in
                foldl (lam acc. lam obj.
                    let name = objName obj in
                    match hmLookup name explicit with None {} then
                        let obj =
                            match hmLookup name acc
                            with Some inner then objMerge inner obj
                            else obj
                        in
                        hmInsert name obj acc
                    else acc
                ) acc field
            ) (hashmapEmpty ()) parents in
        hmValues diff
    in
    
    let full = { namespace with 
         syns = unite synGetter,
         sems = unite semGetter,
         types = unite typeGetter
    } in

    let explicit = { namespace with 
         syns = intersect synGetter,
         sems = intersect semGetter,
         types = intersect typeGetter
    } in

    let implicit = { namespace with 
         syns = diff synGetter,
         sems = diff semGetter,
         types = diff typeGetter
    } in

    let datas = {
        explicit = explicit,
        full = full,
        implicit = implicit
    } in

    namespaceSetInsert set name datas

let langNamespaceGetImplicitChildren : LangNamespaceSet -> String -> Option LangNamespace =
    lam set. lam name.
    optionJoin
        (optionMap
        (lam id. optionMap (lam d. d.implicit) (hmIntLookup id set.idMap))
        (namespaceSetNameToId set name))

let langNamespaceGetExplicitChildren : LangNamespaceSet -> String -> Option LangNamespace =
    lam set. lam name.
    optionJoin
        (optionMap
        (lam id. optionMap (lam d. d.explicit) (hmIntLookup id set.idMap))
        (namespaceSetNameToId set name))

let langNamespaceCleanObj : use Objects in Object -> Object =
    use Objects in
    lam obj. objWithSourceCode obj (sourceCodeEmpty ()) 
