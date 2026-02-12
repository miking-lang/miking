-- Helpers to compute rendering-related data derived from extracted objects.
-- Provides link building, display titles, and optional name handling.

include "../../global/objects.mc"
include "../rendering-options.mc"
include "./headers/search.mc"
include "string.mc"

lang ObjectsRenderer = Objects + Formats

    sem objUrlFetchFailed =
    | obj -> lam name. lam my.
      renderingWarn (join [
          "Failed to resolve ", if my then "my" else "the", " url for name ", name, ".\n",
          "Object details:\n",
          "    namespace: ", objNamespace obj, "\n",
          "    name: ", objName obj, "\n",
          "    id: ", int2string (objId obj), "\n"
      ])


    sem objBuildUrl : Object -> RenderingOptions -> String
    sem objBuildUrl =
    | obj -> lam opt.
      buildUrl opt.stdlibFolder opt.urlPrefix opt.fmt (objHasChildren obj) (objIsStdlib obj) (objNamespace obj) (objGetFirstWord obj)

    -- Edge case for the mdx renderer, bad practice, feel free to make it better.
    sem objPreprocessLink : String -> Format -> String
    sem objPreprocessLink (link: String) =
    | Mdx {} ->
      let index = "/index.md" in
      if strEndsWith index link then
          subsequence link 0 (subi (length link) (length index))
      else link
    | _ -> link

    sem objGetMyLink : Object -> RenderingOptions -> String
    sem objGetMyLink =
    | obj -> lam opt.
      let url =
          buildUrl
              opt.stdlibFolder
              opt.urlPrefix
              opt.fmt
              (objHasChildren obj)
              (objIsStdlib obj)
              (objNamespace obj)
              (objGetFirstWord obj)
      in
      objPreprocessLink url opt.fmt

    sem objGetLink : Object -> RenderingOptions -> String -> String
    sem objGetLink =
    | obj -> lam opt. lam name.
      let link =
          if not (objHasLink obj) then ""
          else match nameContextFetch opt.nameContext obj name with Some res then res.url
          else objUrlFetchFailed obj name false; ""
      in
      objPreprocessLink link opt.fmt

    sem objTryFetch : Object -> RenderingOptions -> String -> Option NameMapValue
    sem objTryFetch =
    | obj -> lam opt. lam name.
      let link =
          if not (objHasLink obj) then None {}
          else nameContextFetch opt.nameContext obj name
      in
      optionMap (lam v. { v with url = objPreprocessLink v.url opt.fmt }) link

    sem objGetMyLocation : Object -> RenderingOptions -> String
    sem objGetMyLocation =
    | obj -> lam opt.
      let name = objName obj in
      let link = objBuildUrl obj opt in
      let prefixLength = length opt.urlPrefix in
      let link = subsequence link prefixLength (length link) in
      pathConcat "/" link
            
    -- Human-friendly display title; special-cases include/utest.
    sem objTitle : Object -> String
    sem objTitle =    
    | obj ->
        let name = head (reverse (strSplit "/" (objName obj))) in
        switch obj
        case ObjInclude { pathInFile = pathInFile } then pathInFile
        case ObjUtest {} then "utest"
        case _ then name
        end

    -- Debug logger for object rendering info.
    sem objLog : Object -> RenderingOptions -> ()
    sem objLog =
    | obj -> lam opt. opt.log (join [
        "Object ", objName obj, ":\n",
        "   form: ", objToString obj, "\n",
        "   namespace: ", objNamespace obj, "\n",
        "   link: ", objGetMyLink obj opt, "\n",
        "   isStdlib: ", bool2string (objIsStdlib obj), "\n"
    ])

    sem objToJsDict : RenderingOptions -> Object -> [SearchDictObj]
    sem objToJsDict opt = 
    | obj ->
      recursive let objToJsDict = lam obj.
          -- Recursive calls: render all children and transmit the name-context through the fold.
          let dicts =  foldl (lam dicts. lam child.
              match (objChildren child, child) with ([], ObjInclude {}) then dicts else
              let newDicts = objToJsDict child in
              concat newDicts dicts
              ) [] (objChildren obj)
          in
          let link = objGetMyLink obj opt in
          let link = if strEndsWith ".md" link then subsequence link 0 (subi (length link) 3) else link in 
          if objHasUrl obj then
             cons { name = objNamespace obj, link = link } dicts
          else dicts
      in objToJsDict obj
end
