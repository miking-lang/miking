-- # Raw renderer
--
-- This file implements the raw renderer based on the raw format.
-- The raw format wraps another format. The wrapped format should be the
-- actual rendering target (though nothing prevents you from wrapping a
-- different format on purpose, resulting in hybrid outputs).
--
-- The core idea: implement general behavior here that always delegates by
-- passing the **wrapped** format as the argument—never the raw format itself.
-- This way, dispatch automatically reaches the correct implementation.

include "../source-code-spliter.mc"
include "./renderer-interface.mc"

lang RawRenderer = RendererInterface

    -- Runs before rendering all files (e.g., to generate global headers).
    sem renderSetup obj =
    | opt -> ()
    
    -- Default block renderer: composes signature, description, code, and tests.
    sem renderBlocDefault : RenderingData -> RenderingOptions -> String -> String -> String -> String -> String
    sem renderBlocDefault =
    | { obj = obj } & data -> lam opt. lam bonusTopDoc. lam bonusSignDescDoc. lam bonusDescCodeDoc. lam bonusBottomDoc.
        let signature = renderDocSignature obj opt in
        let description = renderDocDescription obj opt in
        let code = renderCodeWithoutPreview data opt in
        let tests = renderDocTests data opt in

        join [bonusTopDoc, signature, bonusSignDescDoc, description, bonusDescCodeDoc, code, bonusBottomDoc, tests]

    -- Ensure RenderingOptions uses the wrapped (non-raw) format.
    sem fixOptFormat : RenderingOptions -> RenderingOptions
    sem fixOptFormat = | opt -> { opt with fmt = unwrapRaw opt.fmt }
            
    -- Top page section: title + details (e.g., parent langs) + default block.
    sem renderTopPageDoc (data: RenderingData) =
    | opt -> let opt = fixOptFormat opt in
        let nl = renderNewLine opt in
        let details = switch data
        case { obj = { kind = ObjLang { parents = parents & ([_] ++ _) } } } then
            let parents = strJoin " + " (map (lam p. renderLink p (objLangLink p opt) opt) parents) in
            let sectionTitle = renderBold "Stem from:" opt in
            strJoin nl [sectionTitle, parents]
        case { obj = { kind = ( ObjSyn {} | ObjSem {} )} & obj } then
            let langName = objGetLangName obj in
            let langLink = renderLink langName (objLangLink langName opt) opt in
            let sectionTitle = renderBold "From:" opt in
            strJoin nl [sectionTitle, langLink]
        case { obj = obj } then
            ""
        end in
        renderBlocDefault data opt "" "" details ""
    
    -- Documentation block (optionally includes a “goto” link).
    sem renderDocBloc (data : RenderingData) =
    | opt -> let opt = fixOptFormat opt in
        match data with { obj = obj } in
        let link =
            if objRenderIt obj then
                let link = objLink obj opt in
                let link = concat (if strStartsWith "/" link then "" else "/") link in
                renderGotoLink link opt
            else ""
        in
        renderBlocDefault data opt "" "" link ""
    
    -- Renders the description text of an object (from obj.doc).
    sem renderDocDescription (obj: Object) =
    | opt -> let opt = fixOptFormat opt in
        let doc = objDoc obj in
        concat (renderRemoveDocForbidenChars doc opt) (renderNewLine opt)

    -- Renders the object signature as source code.
    sem renderDocSignature (obj : Object) =
    | opt -> let opt = fixOptFormat opt in
        let type2str = lam t. strReplace "[Char]" "String" (type2str t) in
        let name = objName obj in
        let kind = objKind obj in
        let code = switch obj.kind
        case ObjLet { args = args, ty = ty } then
            let t = match ty with Some t then type2str t else "?" in
            let args = strJoin " " args in
            join ["let ", name, " : ", t]
        case ObjType { t = t } then
            join ["type ", name, match t with Some t then concat " : " t else ""]
        case ObjCon { t = t } then
            join ["con ", name, " : ", t]
        case (ObjMexpr {} | ObjUtest {}) & kind then
            getFirstWord kind
        case ObjLang {} then
            concat "lang " name
        case ObjProgram {} then ""
        case ObjSem { ty = ty } then
            let t = match ty with Some t then type2str t else "?" in
            join ["sem ", name, " : ", t]
        case kind then
            join [getFirstWord kind, " ", name]
        end in
        renderSourceCodeStr code opt

    -- Renders the unit tests section (hidden if empty).
    sem renderDocTests (data: RenderingData) =
    | opt -> let opt = fixOptFormat opt in
        let nl = renderNewLine opt in
        if eqString data.tests "" then ""
        else concat nl (renderHidenCode "Show Tests" (strFullTrim data.tests) true opt)
    
    -- Goto link wrapper (uses renderLink).
    sem renderGotoLink (link: String) =
    | opt -> let opt = fixOptFormat opt in
        renderLink "[→]" link opt
        
    -- Renders a comma-separated list of links for objects (with newline).
    sem renderLinkList (objects: [Object]) =
    | opt -> let opt = fixOptFormat opt in
        let doc = map (lam u. renderLink (objTitle u) (objLink u opt) opt) objects in
        let doc = strJoin ", " doc in
        match doc with "" then "" else
            concat (renderText doc opt) (renderNewLine opt)
    
    -- Renders code as a hidden, toggleable block (raw + preview-less).
    sem renderCodeWithoutPreview (data: RenderingData) = 
    | opt -> let opt = fixOptFormat opt in
        renderHidenCode "Show Implementation" (concat data.left data.right) true opt

    -- Renders code with an optional preview section (uses renderHidenCode).
    sem renderCodeWithPreview (data: RenderingData) =
    | opt -> let opt = fixOptFormat opt in
        match data.right with [] then
            join [data.left, data.trimmed]
        else 
            join [data.left, renderHidenCode "..." data.right false opt, data.trimmed]

    -- Default hidden-code renderer (no-op for raw).
    sem renderHidenCode (buttonText: String) (code : String) (jumpLine: Bool) =
    | _ -> ""

    -- String → tokenized/colored source code (delegates to renderSourceCode).
    sem renderSourceCodeStr (code: String) =
    | opt -> let opt = fixOptFormat opt in
         renderSourceCode (strToSourceCode code) opt

    -- SourceCode → rendered string (maps each word with renderWord).
    sem renderSourceCode (code: SourceCode) =
    | opt -> let opt = fixOptFormat opt in
        join (map (lam code. match code with Some code then renderWord code opt else "") code)
    
    -- Renders a single token/word according to its kind (with escaping).
    sem renderWord (word: SourceCodeWord) = 
    | opt -> let opt = fixOptFormat opt in
        let renderSkiped: [Token] -> String = lam skiped.
            join (map (lam s. renderWord ( { word = s, kind = CodeDefault {} } ) opt) skiped) in

        switch word
        case { word = TokenInclude { content = content, skiped = skiped } } then
            join [renderKeyword "include" opt, renderSkiped skiped, renderString (join ["\"", (renderRemoveCodeForbidenChars content opt), "\""]) opt]    
        case { word = word, kind = kind } then
            let renderer = (switch word
            case TokenStr {} then renderString
            case TokenMultiLineComment {} then renderMultiLineComment
            case TokenComment {} then renderComment
            case _ then
                switch kind
                case CodeKeyword {} then renderKeyword
                case CodeName {} then renderVar
                case CodeType {} then renderType
                case CodeNumber {} then renderNumber
                case CodeDefault {} then renderDefault
                end       
            end) in
            let word = renderRemoveCodeForbidenChars (lit word) opt in
            renderer word opt
        end

    -- Top-level source code rendering: splits, renders, and aggregates.
    -- If row's length is length than 30, we concatenate everything in left.
    sem renderTreeSourceCode (tree: [TreeSourceCode]) (obj : Object) =
    | opt -> let opt = fixOptFormat opt in
        match sourceCodeSplit tree with { left = left, right = right, trimmed = trimmed } in
        let renderSourceCode = lam b. renderSourceCode (wordBufferToSourceCode b) opt in
    
        let getFormatedString : [TreeSourceCode] -> String = lam code.
            foldl (lam s. lam node.
                concat (switch node 
                case TreeSourceCodeNode child then renderCodeWithPreview child opt
                case TreeSourceCodeSnippet code then renderSourceCode code
                end) s
                ) "" (reverse code) in

        let buildSourceCodeRaw = lam code. join (map (lam w. lit w.word) code) in
        let row = foldl (lam row. lam tree.
             concat (switch tree 
                case TreeSourceCodeNode child then child.row
                case TreeSourceCodeSnippet code then buildSourceCodeRaw code
                end) row)
                "" (reverse (concat left right)) in
        let row = concat row (match trimmed with TrimmedNotFormated code then buildSourceCodeRaw code else "") in
    
        let res = {
            obj = obj,
            left = getFormatedString left,
            right = getFormatedString right,
            trimmed = switch trimmed
                case TrimmedFormated s then s
                case TrimmedNotFormated b then renderSourceCode b
                end,
            tests = "",
            rowTests = "",
            row = row
        } in
        if gti 50 (length res.row) then
           { res with left = join [res.left, res.right, res.trimmed], right = "", trimmed = "" }
        else res

    -- File-level wrappers (raw renderer leaves them empty).
    sem renderHeader (obj : Object) =
    | _ -> ""

    sem renderFooter (obj : Object) =
    | _ -> ""

    -- Section titles and basic text formatting.
    sem renderSectionTitle (title: String) =
    | opt -> let opt = fixOptFormat opt in
        renderTitle 2 title opt

    sem renderBold (text : String) =
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

    sem renderLink (title : String) (link : String) =
    | _ -> join [title, " (", link, ")"]
    
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
