include "./langs-namespace.mc"
include "./name-map.mc"
include "./name-context.mc"
include "../global/objects.mc"

type NamingRes = use Objects in  {
     annotatedObj: Object,
     nameContext: NameContext
}

let name : use Objects in Logger -> NamingOptions -> Object -> NamingRes =
    lam log. lam opt. lam obj.
    use Objects in

    let buildUrl = buildUrl opt.stdlibFolder opt.urlPrefix opt.fmt in

    type WorkRes = { ctx: NameContext, nextId: Int, obj: Object } in

    recursive let work : Object -> NameContext -> Int -> WorkRes = use Objects in
        lam obj. lam ctx. lam nextId. 

        let originalChildren = objChildren obj in

        let process : NameContext -> Object -> Int -> [Object] -> WorkRes =
            lam ctx. lam obj. lam nextId. lam children.

            let res = foldl (
                lam acc. lam child.
                let res = work child acc.ctx acc.nextId in
                { res with obj = objAddChild acc.obj res.obj }
            ) { nextId = nextId, ctx = ctx, obj = objWithoutChildren obj } children
            in

            { res with obj = objReverseChildren res.obj }
        in
        
        let annotate : NameContext -> Object -> Int -> WorkRes =
            lam ctx. lam obj. lam nextId.

            let children = objChildren obj in
            let obj = objWithId obj nextId in
            let nextId = addi 1 nextId in

            let ctx = 
                if objHasLink obj then
                    let name = objName obj in
                    let namespace = objNamespace obj in
                    let isStdlib = objIsStdlib obj in
                    let hasChildren = objHasChildren obj in
                    let kind = objGetFirstWord obj in

                    let url = buildUrl hasChildren isStdlib namespace kind in
                    let entryObj = objWithSourceCode obj (sourceCodeEmpty ()) in
                    let entryObj = objWithoutChildren obj in
                    let value = { url = url, obj = entryObj } in
                    let entry = { entry = value, id = objId obj, namespace = namespace } in

                    let nameMap =
                        if objHasUrl obj then nameMapInsert ctx.nameMap name namespace entry
                        else ctx.nameMap
                    in

                    { ctx with nameMap = nameMap }
                else ctx
            in            
            { ctx = ctx, nextId = nextId, obj = obj }
        in

        let annotateAndProcess : Object -> NameContext -> Int -> [Object] -> WorkRes =
            lam obj. lam ctx. lam nextId. lam children.
            match annotate ctx obj nextId with
            { ctx = ctx, nextId = nextId, obj = obj } in
            process ctx obj nextId children
        in

        let processAndAnnotate : Object -> NameContext -> Int -> [Object] -> WorkRes =
            lam obj. lam ctx. lam nextId. lam children.
            match process ctx obj nextId children with
            { ctx = ctx, nextId = nextId, obj = obj } in
            annotate ctx obj nextId
        in

        -- We first insert the direct children, then we call process. So direct children will be
        -- inserted twice, which is absolutly fine and doesn't change correctness.
        let nameDirectChildrenAndProcess : Object -> NameContext -> Int -> WorkRes =
            lam obj. lam ctx. lam nextId.
            let children = objChildren obj in
            match foldl (
                lam acc. lam child.
                let child = objWithoutChildren child in
                match work child acc.ctx acc.nextId with
                { ctx = ctx, nextId = nextId } in -- We throw away the resulting direct child, but keep it in the nameMap
                { ctx = ctx, nextId = nextId }
            ) { ctx = ctx, nextId = nextId } children 
            with { ctx = ctx, nextId = nextId } in
            annotateAndProcess obj ctx nextId children
        in

        switch obj
        case ObjLang { parents = parents} then
            let filterIt : (Object -> Bool) -> [Object] =
                lam keepIt.
                mapOption (
                    lam child.
                    if keepIt child then
                       Some (langNamespaceCleanObj child)
                    else
                       None {}
                ) originalChildren
            in

            let syns = filterIt (lam k. match k with ObjSyn {} then true else false) in
            let sems = filterIt (lam k. match k with ObjSem {} then true else false) in
            let types = filterIt (lam k. match k with ObjType {} then true else false) in

            let langNamespace = {
                objNamespace = objNamespace obj,
                objIsStdlib = objIsStdlib obj,

                parents = [], -- Will be filled in langNamespaceSetBuildNamespace

                types = types,
                syns = syns,
                sems = sems,

                fullSyns = syns,
                fullSems = sems
           } in

           let name = objName obj in
           let namespace = objNamespace obj in
           let isStdlib = objIsStdlib obj in

           let langNamespace = langNamespaceSetBuildNamespace ctx.langNamespaceSet langNamespace parents in
           let langNamespaceSet = langNamespaceSetInsert ctx.langNamespaceSet name langNamespace in
           let ctx = { ctx with langNamespaceSet = langNamespaceSet } in

           let updateChildren : [Object] -> (Object -> [Object]) -> LangNamespace -> [Object] =
               lam children. lam cast. lam namespace.

               let createChildren : [Object] -> [Object] =
                   lam updatedChildren: [Object].
                   join (map cast updatedChildren)
               in

               let syns = createChildren namespace.syns in
               let sems = createChildren namespace.sems in
               let types = createChildren namespace.types in

               join [children, syns, sems, types]
           in

           let explicit =
               match langNamespaceGetExplicitChildren langNamespaceSet name
               with Some explicit then explicit
               else namingWarn (join ["Failed to retrieve explicit namespace for language ", name, "."]); langNamespaceDefault
           in

           -- Recovering the original order
           -- O(n^2) with n the amount of children (n is never big enough to make it problematic)
           let explicit =
               let update =
                   lam mergedChildren.
                   let updated = foldl (lam acc. lam originalChild.
                       match find (lam newChild.
                           and
                             (eqString (objName newChild) (objName originalChild))
                             (eqString (objGetFirstWord newChild) (objGetFirstWord originalChild))
                       ) mergedChildren
                       with Some child then cons child acc
                       else acc
                   ) [] (objChildren obj) in
                   reverse updated
               in
               { explicit with
                   syns = update explicit.syns,
                   sems = update explicit.sems,
                   types = update explicit.types
               }
           in

           let implicit =
               match langNamespaceGetImplicitChildren langNamespaceSet name
               with Some implicit then implicit
               else namingWarn (join ["Failed to retrieve implicit namespace for language ", name, "."]); langNamespaceDefault
           in

           -- Assigning to each merged object there source code and children.
           let children = updateChildren [] (
                   lam obj.
                   let filtered = filter (lam original. eqString (objName original) (objName obj)) originalChildren in
                   if null filtered then
                        namingWarn (join ["Explicit language namespace children do not match actual children for ", objName obj, ".."]);
                        [objWithoutChildren obj]                        
                   else
                        let filtered = reverse filtered in
                        
                        let last = head filtered in
                        let lastSourceCode = objSourceCode last in
                        let lastChildren = objChildren last in

                        let last = objWithSourceCode obj lastSourceCode in
                        let last = objSetChildren last lastChildren in

                        let filtered = cons last (tail filtered) in
                        reverse filtered
              ) explicit
           in

           -- Not really necessary by the way
           let children = updateChildren children (lam obj. [objWithoutChildren obj] ) implicit in
           let children = map (lam child.
               if strStartsWith namespace (objNamespace child) then child
               else objWithIsArtificial child true
               ) children -- Updating namespaces
           in

           let obj = objSetChildren obj children in

           nameDirectChildrenAndProcess obj ctx nextId
           
        case ObjCon {} then
            let namedObj = objWithId obj nextId in
            let ctx = { ctx with typeNamespaceSet = typeNamespaceInsertNewCon ctx.typeNamespaceSet namedObj } in
            annotateAndProcess obj ctx nextId originalChildren
        case ObjType {} then
            let namedObj = objWithId obj nextId in        
            let ctx = { ctx with typeNamespaceSet = typeNamespaceInsertNewType ctx.typeNamespaceSet namedObj } in
            annotateAndProcess obj ctx nextId originalChildren
        case ObjInclude {} | ObjProgram {} then processAndAnnotate obj ctx nextId originalChildren
        case _ then annotateAndProcess obj ctx nextId originalChildren
        end
    in

    let amountOfChildren = objCountChildren obj in
    let cap = divi amountOfChildren 20 in
    let cap = if gti cap 100 then cap else 100 in

    log (join ["Got ", int2string amountOfChildren, " children before naming."]);
    match work obj (nameContextWithCapacity cap) 1 with { ctx = nameContext, obj = annotatedObj } in

    (if opt.debug then    
        let amountOfChildren = objCountChildren annotatedObj in
        log (join ["Got ", int2string amountOfChildren, " children after naming."])
    else ()); -- We don't want to compute objCountChildren if there is no debug.

    { annotatedObj = annotatedObj, nameContext = nameContext }
