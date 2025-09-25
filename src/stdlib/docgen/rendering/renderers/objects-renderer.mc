-- # ObjectsRenderer utilities
--
-- Helpers to compute rendering-related data derived from extracted objects.
-- Provides link building, display titles, and optional name handling.

include "../../extracting/objects.mc"
include "../rendering-options.mc"
include "./headers/search.mc"
include "string.mc"

lang ObjectsRenderer = ObjectKinds + Formats

    -- Resolve a language name to a link using the nameContext map; fallback to the name.
    sem objLangLink : String -> RenderingOptions -> String
    sem objLangLink =
    | name -> lam opt. match hmLookup name opt.nameContext with Some link then link
                       else name
    
    -- Return the object name only for named kinds (let/type/sem/syn/lang/con).
    sem objNameIfHas : Object -> Option String
    sem objNameIfHas =
    | { kind = ObjLet {} | ObjType {} | ObjSem {} | ObjSyn {} | ObjLang {} | ObjCon {} } & obj -> Some (objName obj)
    | _ -> None {}

    -- Preserve the current name context only for Lang and Program roots.
    sem objPreserveNameCtx : Object -> Bool
    sem objPreserveNameCtx =
    | { kind = ObjLang {} | ObjProgram {} } -> true
    | _ -> false
    -- Build the canonical link for an object (prefix + namespace + extension).

    -- Uses "Stdlib" for stdlib objects, "Files" for user sources.
    sem objGetPureLink : Object -> RenderingOptions -> String
    sem objGetPureLink =
    | obj -> lam opt.
        let namespace = objNamespace obj in
        let ext = concat "." (formatGetExtension opt.fmt) in
        let prefix = if objIsStdlib obj then "Stdlib" else "Files" in
        let link =  join [prefix, namespace, ext] in
        if strStartsWith "/" link then link else cons '/' link     

    -- Compute the URL for an object; Lang/Use use name-based mapping, others use file path.
    sem objLink : Object -> RenderingOptions -> String
    sem objLink =
    | obj -> lam opt.
        let link = switch (objKind obj)
            case ObjLang {} | ObjUse {} then
                objLangLink (objName obj) opt   
            case _ then
                 objGetPureLink obj opt
            end
        in
        if strStartsWith "/" link then link else cons '/' link
            
    -- Human-friendly display title; special-cases include/utest.
    sem objTitle : Object -> String
    sem objTitle =    
    | obj ->
        let name = head (reverse (strSplit "/" (objName obj))) in
        let kind = objKind obj in
        switch kind
        case ObjInclude { pathInFile = pathInFile } then pathInFile
        case ObjUtest {} then "utest"
        case _ then name
        end

    -- Debug logger for object rendering info.
    sem objLog : Object -> RenderingOptions -> ()
    sem objLog =
    | obj -> lam opt. opt.log (join [
        "Object ", objName obj, ":\n",
        "   kind: ", objKindToString (objKind obj), "\n",
        "   namespace: ", objNamespace obj, "\n",
        "   prefix: ", objPrefix obj, "\n",
        "   link: ", objLink obj opt, "\n",
        "   isStdlib: ", bool2string (objIsStdlib obj), "\n"
    ])

    sem objToJsDict : RenderingOptions -> ObjectTree -> [SearchDictObj]
    sem objToJsDict opt = 
    | tree ->
      recursive let objToJsDict = lam opt. lam tree. 
          let obj = objTreeObj tree in
          -- Recursive calls: render all children and transmit the name-context through the fold.
          let res =  foldl (lam arg. lam son.
              let obj = objTreeObj son in
              match (objTreeSons son, obj.kind) with ([], ObjInclude {}) then arg else
              let nameContext =
                  match objNameIfHas obj with Some name then
                   hmInsert name (objGetPureLink obj arg.opt) arg.opt.nameContext
                  else arg.opt.nameContext
              in
              let opt = { arg.opt with nameContext = nameContext } in
              match objToJsDict opt son with { dicts = dicts, opt = opt } in
              { opt = opt, dicts = concat dicts arg.dicts }
              ) { dicts = [], opt = opt } (objTreeSons tree)
          in
          let link = concat opt.urlPrefix (objLink obj opt) in
          let link = if strEndsWith ".md" link then subsequence link 0 (subi (length link) 3) else link in 
          {
             opt = if objPreserveNameCtx obj then res.opt else opt,
             dicts = if objRenderIt obj then cons { name = objNamespace obj, link = link } res.dicts else res.dicts
          }
      in (objToJsDict opt tree).dicts 

end
