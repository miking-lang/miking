-- This file implements the raw renderer based on the raw format.
-- The raw format wraps another format. The wrapped format should be the
-- actual rendering target (though nothing prevents you from wrapping a
-- different format on purpose, resulting in hybrid outputs).
--
-- The core idea: implement general behavior here that always delegates by
-- passing the wrapped format as the argument—never the raw format itself.
-- This way, dispatch automatically reaches the correct implementation.

include "../source-code-spliter.mc"
include "./renderer-interface.mc"
include "../../global/ext-utils.mc"

lang RawRenderer = RendererInterface

    sem renderSetup =
    | opt -> ()

    -- We just render the parent link.
    sem renderHeader (obj : Object) =
    | opt -> let opt = fixOptFormat opt in
      renderParentLink obj opt

    sem renderFooter (obj : Object) =
    | _ -> ""

    sem renderSearchPath (path: String) =
    | opt -> pathConcat path (searchPath "")

    sem renderSearchFile (searchDatas: [SearchDictObj]) =
    | opt -> let opt = fixOptFormat opt in
        let path = renderGetSearchPath opt in
        match docgenFileWriteOpen path with Some wc then
              docgenFileWriteString wc (searchReact searchDatas);
              docgenFileWriteClose wc
        else
              renderingWarn (join ["Failed to write file: ", path, "."])

    
    -- Top page section: title + details (e.g., parent langs) + default block.
    sem renderTopPageDoc (data: RenderingData) =
    | opt -> let opt = fixOptFormat opt in
        let nl = renderNewLine opt in
        let obj = data.obj in
        
        let renderStemFrom = lam obj. lam from.
            let link = renderSourceCodeStr from (Some obj) opt in
            let sectionTitle = renderBold "From:" opt in
            strJoin nl [sectionTitle, link, ""]
        in

        let details = switch obj
        case ObjLang { parents = parents & ([_] ++ _) } then
            let parents = strJoin " + " (map (lam p. renderSourceCodeStr p (Some obj) opt) parents) in
            let sectionTitle = renderBold "Stem from:" opt in
            strJoin nl [sectionTitle, parents, ""]
        case ObjCon { parentType = parentType } then
             renderStemFrom obj parentType
        case ObjSyn { variants = variants } then
             renderStemFrom obj (objLangName obj)
        case ObjSem {} then
            renderStemFrom obj (objLangName obj)
        case _ then
            ""
        end in
        renderBlocDefault data false opt "" "" details ""
    


    -- Default block renderer: composes signature, description, code, and tests.
    sem renderBlocDefault : RenderingData -> Bool -> RenderingOptions -> String -> String -> String -> String -> String
    sem renderBlocDefault =
    | { obj = obj } & data -> lam asChildren. lam opt. lam bonusTopDoc. lam bonusSignDescDoc. lam bonusDescCodeDoc. lam bonusBottomDoc.
        let opt = fixOptFormat opt in
        let signature = renderDocSignature obj opt in

        let doc = objDoc obj in
        let doc = renderDocObjectParse doc opt in
        let doc = renderFormattedDoc obj doc true opt in
        let doc = renderDocDescription doc opt in

        let code = if opt.noCode then "" else renderCodeWithoutPreview data opt in
        let tests = renderDocTests data asChildren opt in
        join [bonusTopDoc, signature, bonusSignDescDoc, doc, bonusDescCodeDoc, code, bonusBottomDoc, tests]
            
    sem renderGetSearchPath =
    | opt -> ""

    -- Documentation block (optionally includes a “goto” link).
    sem renderDocBloc (data : RenderingData) (asChildren: Bool) =
    | opt -> let opt = fixOptFormat opt in
        let obj = data.obj in
        let link =
            if and (not (objIsArtificial obj)) (objHasUrl obj) then
                let link = objGetMyLink obj opt in
                let link = concat (if strStartsWith "/" link then "" else "/") link in
                renderGotoLink link opt
            else ""
        in

        renderBlocDefault data asChildren opt "" "" link ""
    
    -- Renders the description text of an object (from obj.doc).
    sem renderDocDescription (desc: String) =
    | opt -> let opt = fixOptFormat opt in desc

    sem renderVariants (obj: Object) =
    | opt -> let opt = fixOptFormat opt in
        switch obj
        case ObjSyn { variants = variants } then 
            let variants = renderSynVariants obj variants opt in
            renderHidenCode "▶" "▼" variants true opt
        case ObjType {} then
            let cons = renderTypeConstructors obj opt in            
            if null cons then "" else renderHidenCode "▶" "▼" cons true opt
        case _ then ""
        end

    sem renderPureDocSignature (obj : Object) =
    | opt -> let opt = fixOptFormat opt in
        let name = objName obj in

        switch obj
        case ObjLet { ty = ty } then
            let t = match ty with Some t then type2str t else "?" in
            join ["let ", name, " : ", t]
        case ObjType { t = t } then
            let t = match t with Some t then type2str t else "" in
            join ["type ", name, if null t then "" else concat " : " t]
        case ObjCon { t = t } then
            join ["con ", name, " : ", type2str t]
        case (ObjMexpr {} | ObjUtest {}) & form then
            objGetFirstWord form
        case ObjLang {} then
            concat "lang " name
        case ObjProgram {} then ""
        case ObjSem { ty = ty } then
            let t = match ty with Some t then type2str t else "?" in
            join ["sem ", name, " : ", t]
        case form then
            join [objGetFirstWord form, " ", name]
        end

    -- Renders the object signature as source code.
    sem renderDocSignature (obj : Object) =
    | opt -> let opt = fixOptFormat opt in
        let code = renderPureDocSignature obj opt in
        let variants = renderVariants obj opt in
        let sign = renderSourceCodeStr code (Some obj) opt in
        if null variants then sign else concat sign variants
        

    -- Renders the unit tests section (hidden if empty).
    sem renderDocTests (data: RenderingData) (hide: Bool) =
    | opt -> let opt = fixOptFormat opt in
        let tests = data.tests in
        if null tests then ""
        else if hide then renderHidenCode "Show Tests" "Hide Tests" tests true opt
        else tests
    
    sem renderTypeConstructors (obj: Object) =
    | opt -> let opt = fixOptFormat opt in
        match nameContextGetTypeConstructors opt.nameContext obj with Some constructors then
            strJoin (renderNewLine opt)
                (map (lam cons.
                 let name = objName cons in
                 match cons with ObjCon { t = t } then
                     let doc = objTryGetDoc cons in
                     let doc = strTrim doc in
                     let variant = {
                         name = name,
                         vtype = type2str t,
                         doc = doc
                     } in

                     renderOneVariant cons variant opt
                 else renderingWarn "Constructor expected here (internal error)."; "")
                 constructors)
        else renderingWarn (join ["Failed to retrieve constructors for type ", objName obj, "."]); ""

    sem renderOneVariant (obj: Object) (v: SynVariant) =
    | opt -> let opt = fixOptFormat opt in
        let right = join [v.name, " ", v.vtype] in
        let right = strToSourceCode right in
        let right = renderSourceCode right (Some obj) opt in
        let doc = renderRemoveDocForbidenChars v.doc opt in
        if null v.doc then right else join [right, ": ", doc]

    sem renderSynVariants (obj: Object) (variants: [SynVariant]) =
    | opt -> let opt = fixOptFormat opt in
        strJoin "\n" (map (lam v. renderOneVariant obj v opt) variants)

    -- Goto link wrapper (uses renderLink).
    sem renderGotoLink (link: String) =
    | opt -> let opt = fixOptFormat opt in
        renderLink "[→]" link opt

    sem renderHookLink (title: String) (link: String) (highlight: Bool) =
    | opt -> let opt = fixOptFormat opt in
        renderLink title link opt

    sem renderPageLink (title: String) (link: String) =
    | opt ->  let opt = fixOptFormat opt in
        renderLink title link opt

    -- Goto link wrapper (uses renderLink).
    sem renderParentLink (obj: Object) =
    | opt -> let opt = fixOptFormat opt in
        let namespace = objNamespace obj in
        let subnamespace = namespaceGetSubNamespace namespace in
        if namespaceIsRoot namespace then ""
        else match namespaceLast subnamespace with Some parentName then
              let link =
                  if strEndsWith ".mc" parentName then
                     buildUrl
                         opt.stdlibFolder
                         opt.urlPrefix
                         opt.fmt
                         true
                         (objIsStdlib obj)
                         subnamespace
                         ""
                  else
                    let parentName =
                        match strSplitOnce parentName '-' with Some (left, _) then left
                        else parentName
                    in
                    objGetLink obj opt parentName
              in
              if null link then "" else renderLink "←" link opt
        else ""


    -- Renders a comma-separated list of links for objects (with newline).
    sem renderLinkList (objects: [Object]) =
    | opt -> let opt = fixOptFormat opt in
        let doc = map (lam u.
            let link = objGetLink u opt (objName u) in
            renderPageLink (objTitle u) link opt
            ) objects
        in
        let doc = strJoin ", " doc in
        match doc with "" then "" else
            concat (renderText doc opt) (renderNewLine opt)
    
    -- Renders code as a hidden, toggleable block (raw + preview-less).
    sem renderCodeWithoutPreview (data: RenderingData) = 
    | opt -> let opt = fixOptFormat opt in
        if objHasChildren data.obj then
            renderHidenCode "Show Implementation" "Hide Implementation" data.code true opt
        else
            data.code

    -- Renders code with an optional preview section (uses renderHidenCode).
    sem renderCodeWithPreview (data: RenderingData) =
    | opt -> let opt = fixOptFormat opt in
        match data.right with [] then
            data.left
        else 
            join [data.left, renderHidenCode "..." "..." data.right false opt]

    -- Default hidden-code renderer (no-op for raw).
    sem renderHidenCode (hidden: String) (shown: String) (code : String) (jumpLine: Bool) =
    | _ -> ""

    -- String -> tokenized/colored source code (delegates to renderSourceCode).
    sem renderSourceCodeStr (code: String) (obj: Option Object) =
    | opt -> let opt = fixOptFormat opt in
         renderSourceCode (strToSourceCode code) obj opt

    -- SourceCode -> rendered string (maps each word with renderWord).
    sem renderSourceCode (code: SourceCode) (obj: Option Object) =
    | opt -> let opt = fixOptFormat opt in
        join (map (lam code. renderWord code obj opt) code)
    
    -- Renders a single token/word according to its form (with escaping).
    sem renderWord (word: SourceCodeWord) (obj: Option Object) =
    | opt -> let opt = fixOptFormat opt in
        let renderSkiped: [Token] -> String = lam skiped.
            join (map (lam s. renderWord ( { word = s, kind = CodeDefault {} } ) obj opt) skiped)
        in

        match word with { word = TokenInclude { content = content, skiped = skiped } } then
            join [renderKeyword "include" opt, renderSkiped skiped, renderString (join ["\"", (renderRemoveCodeForbidenChars content opt), "\""]) opt]    
        else match word with { word = word, kind = kind } in
            let renderer = 
                let lit = lit word in
                switch word
                case TokenStr {} then renderString
                case TokenMultiLineComment {} then renderMultiLineComment
                case TokenComment {} then renderComment
                case _ then
                    switch kind
                    case CodeKeyword {} then renderKeyword
                    case CodeName {} then renderVar
                    case CodeType {} then (lam word.
                                          let word = match strSplitOnce word '_' with Some (left, word) then word else word in
                                          let word =
                                              match obj with Some obj then renderHook obj word false opt
                                              else word
                                          in
                                          renderType word)
                    case CodeNumber {} then renderNumber
                    case CodeDefault {} then renderDefault
                    end       
                end
            in

            let word = lit word in
            let word = renderRemoveCodeForbidenChars word opt in
            renderer word opt

    sem renderCreateTests (tests: [RenderingData]) =
    | opt -> let opt = fixOptFormat opt in
        strJoin "\n" (map (lam t. t.code) tests)

    sem renderCreateRenderingData (obj: Object) (tests: [RenderingData]) =
    | opt -> let opt = fixOptFormat opt in
        let split = sourceCodeSplit (objSourceCode obj) in
        let split = (length split.left) in

        let code = renderSourceCode (objSourceCode obj) (None {}) opt in
        let tests = renderCreateTests tests opt in

        renderingDataNew obj code split tests

    -- Section titles and basic text formatting.
    sem renderSectionTitle (title: String) =
    | opt -> let opt = fixOptFormat opt in
        renderTitle 2 title opt

    sem renderBold (text : String) =
    | _ -> text

    sem renderItalic (text : String) =
    | _ -> text

    -- Escaping/sanitizing hooks for docs and code (no-op in raw).
    sem renderRemoveDocForbidenChars (s: String) =
    | _ -> s

     sem renderRemoveCodeForbidenChars (s: String) =
    | _ -> s

    -- Title helpers.
    sem renderTitle (size : Int) (s : String) =
    | _ -> s

    sem renderObjTitle (size : Int) (obj : Object) =
    | opt -> let opt = fixOptFormat opt in
        renderTitle size (objTitle obj) opt
    
    -- Text, link, and color helpers (raw → passthrough).
    sem renderText (text : String) =
    | _ -> text

    sem renderStdlibConstLink (file: String) =
    | opt ->
        let ext = formatGetExtension opt.fmt in
        normalizePath (join ["/", opt.stdlibFolder, "/", opt.urlPrefix, "/", file, "/index.", ext])

    sem renderHook (obj: Object) (name: String) (highlight: Bool) =
    | opt -> let opt = fixOptFormat opt in
         let datas =
             switch name
             case "Int" then { url = renderStdlibConstLink "int.mc" opt, obj = None {}}
             case "Bool" then { url = renderStdlibConstLink "bool.mc" opt, obj = None {}}
             case "String" then { url = renderStdlibConstLink "string.mc" opt, obj = None {}}
             case "Char" then { url = renderStdlibConstLink "char.mc" opt, obj = None {}}
             case _ then
                match objTryFetch obj opt name with Some datas then
                    { url = datas.url, obj = Some datas.obj }
                else if eqString (objName obj) name then
                    { url = objGetMyLink obj opt, obj = Some obj }
                else
                    { url = "", obj = None {} }
             end
         in  
         if null datas.url then name else
         let link = renderHookLink name datas.url highlight opt in
         match datas.obj with Some obj then
             let doc = objTryGetDoc obj in
             let doc = strTrim doc in
             let doc = renderDocObjectParse doc opt in
             let doc = renderFormattedDoc obj doc false opt in
             let sign = renderTooltipSign obj opt in
             let doc = join [sign, if or (null sign) (null doc) then "" else "\n\n", doc] in
             renderTooltip link doc opt
         else link


    sem renderLink (title : String) (link : String) =
    | _ -> join [title, " (", link, ")"]

    sem renderTooltip (title : String) (content : String) =
    | _ -> title

    sem renderTooltipSign (obj: Object) =
    | opt -> let opt = fixOptFormat opt in
        let sign = renderPureDocSignature obj opt in
        renderSourceCodeStr sign (None {}) opt

    sem renderType (content : String) = 
    | _ -> content

    sem renderVar (content : String) =
    | _ -> content
    
    sem renderKeyword (content : String) =
    | _ -> content
    
    sem renderComment (content : String) =
    | _ -> content
    
    sem renderString (content : String) =
    | _ -> content

    sem renderNumber (content : String) =
    | _ -> content
    
    sem renderDefault (content : String) =
    | _ -> content
    
    sem renderMultiLineComment (content : String) =
    | _ -> content

    -- Newline helper.
    sem renderNewLine =
    | _ -> "\n"
    
end
