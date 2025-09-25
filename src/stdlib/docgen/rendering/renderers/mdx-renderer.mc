-- # MDX Renderer for mi-doc-gen
--
-- This module implements the **MdxRenderer**, an instance of `RendererInterface`.
-- It outputs MDX pages compatible with Docusaurus, delegating text formatting to
-- the Markdown renderer where appropriate, and using shared MDX components.
--
-- ## Design
-- - Writes a reusable MDX components file (`MikingDocGen.tsx/.jsx`) at setup.
-- - Renders headings/markdown via the Markdown renderer to keep escaping consistent.
-- - Builds semantic blocks (`DocBlock`, `ToggleWrapper`, etc.) in MDX.
-- - Trims trailing comment/blank lines from raw code when rendering code blocks.
-- - Removes `.md` from links so Docusaurus routes match clean URLs.
-- - Search bar here is still in todo.

include "./renderer-interface.mc"
include "./headers/mdx-components.mc"

include "sys.mc"

let componentFileName = "MikingDocGen"
let searchFileName = searchPath ""

-- Provides the MDX renderer implementation and its dispatch rules.
lang MdxRenderer = RendererInterface

    -- Build an absolute path "<folder>/<name>.<ext>" for the components file.
    sem getComponentPath : FormatLanguage -> String -> String -> String
    sem getComponentPath =
    | fmtLang -> lam path. lam name.
        let path = if not (strEndsWith "/" path) then concat path "/" else path in
        let ext = concat "." (formatLanguageGetExt fmtLang) in
        let name = concatIfNot name (strEndsWith ext) ext in
        concat path name

    -- Create the MDX components file (TSX/JSX) in the output folder.
    sem renderSetup obj =
    | { fmt = Mdx {} } & opt ->
        let srcPath = normalizePath (join [opt.outputFolder, "/", opt.srcFolder, "/"]) in
        let path = getComponentPath opt.fmtLang srcPath componentFileName in
        (match fileWriteOpen path with Some wc then
            let write = fileWriteString wc in
            let components = match opt.fmtLang with Ts {} then mdxTsComponents else mdxJsComponents in
            write components;
            fileWriteClose wc
        else
            renderingWarn (concat "Failed to create components file: " path));

        let path = getComponentPath (Js {}) srcPath searchFileName in
        (match fileWriteOpen path with Some wc then
            fileWriteString wc (searchReact (objToJsDict opt obj));
            fileWriteClose wc
        else
            renderingWarn (concat "Failed to create search file: " path))

    -- Emit import line for MDX components used by the page.
    sem renderHeader obj =
    | { fmt = Mdx {} } & opt ->
        let formatPath = lam full.
            let importPath = if strStartsWith "/" full
                             then subsequence full 1 (length full)
                             else full in
            --  strip .tsx/.js extension from the import path if present
            let path = if strEndsWith ".tsx" importPath
            then subsequence importPath 0 (subi (length importPath) 4)
            else if strEndsWith ".jsx" importPath
            then subsequence importPath 0 (subi (length importPath) 4)
            else importPath in
            normalizePath path
        in
            

        let path = normalizePath (join [opt.urlPrefix, "/", opt.srcFolder]) in
        let import = formatPath (getComponentPath opt.fmtLang path componentFileName) in
        let search = formatPath (getComponentPath (Js {}) path searchFileName) in
        
        join [
          "import { DocBlock, Signature, Description, ToggleWrapper, S} from '@site/", import, "';\n",
          "import Search from '@site/", search, "';\n\n",

          "<Search />\n"
        ]

    -- Reuse Markdown escaping for code.
    sem renderRemoveCodeForbidenChars (s: String) =
    | { fmt = Mdx {} } & opt -> renderRemoveCodeForbidenChars s { opt with fmt = Md {} }

    -- Reuse Markdown escaping for docs.
    sem renderRemoveDocForbidenChars (s: String) =
    | { fmt = Mdx {} } & opt -> renderRemoveCodeForbidenChars s { opt with fmt = Md {} }

    -- Delegate headings to Markdown renderer.
    sem renderTitle size s =
    | { fmt = Mdx {} } & opt -> renderTitle size s { opt with fmt = Md {} }

    -- Delegate bold text to Markdown renderer.
    sem renderBold (text : String) =
    | { fmt = Mdx {} } & opt -> renderBold text { opt with fmt = Md {} }

    -- Delegate newline rendering to Markdown renderer ("  \n").
    sem renderNewLine =
    | { fmt = Mdx {} } & opt -> renderNewLine { opt with fmt = Md {} }

    -- Render object description as an MDX <Description> block (omit empty default).
    sem renderDocDescription obj =
    | { fmt = Mdx {} } & opt ->
      let rawDesc = renderDocDescription obj { opt with fmt = Md {} } in
      let desc = if eqString rawDesc "No documentation available here." then "" else rawDesc in
      if eqString "" desc then "" else join ["<Description>{`", desc, "`}</Description>\n"]
        
    -- Delegate goto link rendering to Markdown renderer (keeps URL rules consistent).
    sem renderGotoLink (link: String) =
    | { fmt = Mdx {} } & opt -> renderGotoLink link { opt with fmt = Md {} }
    
    -- Render a single link, removing the trailing ".md" for Docusaurus routes.
    sem renderLink (title : String) (link : String) =
    | { fmt = Mdx {} } & opt ->
          let link = concat opt.urlPrefix link in
          let linkLength = length link in
          let link = subsequence link 0 (subi linkLength 3) in -- remove extension for Docusaurus
          join ["<a href={\"", link, "\"} style={S.link}>", title, "</a>"]
    
    -- Render a list of links by delegating to raw rendering, then add a newline.
    sem renderLinkList (objects: [Object]) =
    | { fmt = Mdx {} } & opt ->
        let nl = renderNewLine opt in
        join [renderLinkList objects { opt with fmt = Raw { fmt = Mdx {}} }, nl]

    -- Format a code string as a fenced block ```mc (with proper escaping).
    sem mdxRenderCode : RenderingOptions -> String -> String
    sem mdxRenderCode =
    | opt -> lam code. join ["\n```mc\n", renderRemoveCodeForbidenChars code opt, "\n```\n"]

    -- Render signature via the raw MDX dispatcher; omit if empty.
    sem renderDocSignature (obj: Object) =
    | { fmt = Mdx {} } & opt -> 
        let sign = renderDocSignature obj { opt with fmt = Raw { fmt = Mdx {} } } in
        if eqString sign "" then "" else sign

    -- Render the full code (trim trailing comments/empties), escaped for MDX.
    sem renderCodeWithoutPreview (data: RenderingData) =
    | { fmt = Mdx {} } & opt ->
        let split = strSplit "\n" data.row in
        match splitOnR (lam l.
            let trimmed = strTrim l in
            not (or (strStartsWith "--" trimmed) (eqString "" trimmed))
        ) (reverse split) with { right = right } in
        let row = strJoin "\n" (reverse right) in
        renderRemoveCodeForbidenChars row opt

    -- Render tests as raw text if available (panels are added by the caller).
    sem renderDocTests (data: RenderingData) =
    | { fmt = Mdx {} } & opt ->
        if eqString data.rowTests "" then "" else strFullTrim data.rowTests

    -- Render the top-of-page doc + a toggleable code preview.
    sem renderTopPageDoc (data: RenderingData) =
    | { fmt = Mdx {} } & opt ->
        let rawDesc = renderDocDescription data.obj { opt with fmt = Md {} } in
        let desc = strTrim rawDesc in
        let desc = if eqString rawDesc "No documentation available here." then "" else rawDesc in
        join ["\n", desc, if eqString desc "" then "" else "\n\n"]

    -- Render a full documentation block (title, signature, desc, code, optional tests).
    sem renderDocBloc (data: RenderingData) =
    | { fmt = Mdx {} } & opt ->
        let sign = renderDocSignature data.obj opt in
        let code  = renderCodeWithoutPreview data opt in
        let tests = renderDocTests data opt in
        let desc = renderDocDescription data.obj opt in
 
        let hasTests = not (eqString tests "") in

        let link = objLink data.obj opt in
        let link = concat opt.urlPrefix link in
        let linkLength = length link in
        let link = subsequence link 0 (subi linkLength 3) in -- remove extension for Docusaurus
        let link = if objRenderIt data.obj then join [" link=\"", link, "\""] else "" in 
        
        let title = objTitle data.obj in
        let kind  = getFirstWord (objKind data.obj) in
    
        let ns = objNamespace data.obj in
        let codeId  = join ["code-", ns] in
        let testsId = join ["tests-", ns] in
    
        join [
          "
          <DocBlock title=\"", title, "\" kind=\"", kind, "\"", link, ">\n",
          mdxRenderCode opt sign, "\n",
          desc, "\n\n",
          "<ToggleWrapper text=\"Code..\">", mdxRenderCode opt code, "</ToggleWrapper>\n",
          (if hasTests then join ["<ToggleWrapper text=\"Tests..\">", mdxRenderCode opt tests, "</ToggleWrapper>\n"] else ""),
          "</DocBlock>\n\n"
        ]
end
