-- # HTML Renderer for mi-doc-gen
--
-- This module implements the **HtmlRenderer**, an instance of `RendererInterface`.
-- It generates HTML pages from the extracted ObjectTree.
--
-- ## Design
-- - The HTML renderer wraps the **raw** renderer: whenever we need to render inner
--   parts (titles, doc strings, code, …) as plain text, we temporarily switch
--   the format to `Raw { fmt = Html {} }` and call the corresponding raw function.
--   This ensures consistent escaping and avoids recursion issues.
-- - `htmlRenderWrapper` centralizes this pattern: it calls a raw-rendered function
--   and, if the result is non-empty, wraps it with provided HTML tags.
-- - Syntax coloring is implemented with `<span class="...">` using short CSS class
--   names: `tp`, `var`, `kw`, `comment`, `string`, `multi`, `number`.
-- - Newlines in HTML are rendered as `<br>` (see `renderNewLine`), whereas blocks
--   such as documentation and code are wrapped in `<pre>` for whitespace fidelity.
-- - `renderHidenCode` (sic) provides a simple toggle button + collapsible container.
--   The actual JS/CSS hooks are assumed to be present in the page header.

include "./renderer-interface.mc"
include "./headers/html-header.mc"

-- The HTML renderer implementation 
lang HtmlRenderer = RendererInterface

    -- Create the scripts and stylesheet in the output folder.
    sem renderSetup obj =
    | { fmt = Html {} } & opt ->
        let srcPath = normalizePath (join [opt.outputFolder, "/", opt.srcFolder]) in
        let openAndWrite = lam s. lam path.
            let path = normalizePath (join [srcPath, "/", path]) in
            match fileWriteOpen path with Some wc then
                fileWriteString wc s;
                fileWriteClose wc
            else
                renderingWarn (join ["Failed to create ", path, " file."])
        in
        openAndWrite (searchJs (objToJsDict opt obj)) (searchPath ".js");
        openAndWrite htmlStyle htmlStylePath;
        openAndWrite htmlScript htmlScriptPath
        

    -- Page/file header: injects theme header and object name into the HTML head/body.
    sem renderHeader obj =
    | { fmt = Html {} } & opt -> getHeader (objName obj) opt.srcFolder

    -- HTML heading: delegates inner text to raw title rendering, then wraps as <hN>.
    sem renderTitle size s =
    | { fmt = Html {} } & opt ->
        let sizeStr = int2string (if gti size 6 then 6 else size) in
        join ["<h", sizeStr, ">", renderTitle size s { opt with fmt = Raw { fmt = Html {}} }, "</h", sizeStr, ">", renderNewLine opt]
    
    -- Bold text
    sem renderBold (text : String) =
    | { fmt = Html {} } & opt -> join ["<strong>", text, "</strong>"]

    -- Page/file footer
    sem renderFooter obj =
    | { fmt = Html {} } & opt -> "</div></body>\n</html>"   

    -- New line for inline contexts
    sem renderNewLine =
    | { fmt = Html {} } & opt -> "<br>"

    -- Escaping for documentation content (also normalizes `<br>` to actual newlines)
    sem renderRemoveDocForbidenChars (s: String) =
    | { fmt = Html {} } & opt ->
        switch s
        case "&" ++ s then concat "&amp;" (renderRemoveDocForbidenChars s opt)
        case "<br>" ++ s then cons '\n' (renderRemoveDocForbidenChars s opt)
        case "<" ++ s then concat "&lt;" (renderRemoveDocForbidenChars s opt)
        case ">" ++ s then concat "&gt;" (renderRemoveDocForbidenChars s opt)    
        case [x] ++ s then cons x (renderRemoveDocForbidenChars s opt)
        case "" then ""
        end

    -- Code escaping reuses the doc escaping logic
    sem renderRemoveCodeForbidenChars (s: String) =
    | { fmt = Html {} } & opt -> renderRemoveDocForbidenChars s opt

    -- Small helper to wrap inner content with an HTML span and a CSS class
    sem htmlRenderSpan : String -> String -> String
    sem htmlRenderSpan =
    | content -> lam kind. join ["<span class=\"", kind, "\">", content, "</span>"]

    -- Syntax coloring: types, vars, keywords, comments, strings, multi-line comments, numbers
    sem renderType (content : String) = 
    | { fmt = Html {} } & opt -> htmlRenderSpan content "tp"

    sem renderVar (content : String) =
    | { fmt = Html {} } & opt -> htmlRenderSpan content "var"
    
    sem renderKeyword (content : String) =
    | { fmt = Html {} } & opt -> htmlRenderSpan content "kw"
    
    sem renderComment (content : String) =
    | { fmt = Html {} } & opt -> htmlRenderSpan content "comment"
    
    sem renderString (content : String) =
    | { fmt = Html {} } & opt -> htmlRenderSpan content "string"
    
    sem renderMultiLineComment (content : String) =
    | { fmt = Html {} } & opt -> htmlRenderSpan content "multi"

    sem renderNumber (content : String) =
    | { fmt = Html {} } & opt -> htmlRenderSpan content "number"

    -- Wrapper that renders inner content via raw renderer, then wraps it with HTML
    sem htmlRenderWrapper : all a. RenderingOptions -> String -> (a -> RenderingOptions -> String) -> a -> String -> String
    sem htmlRenderWrapper =
    | opt -> lam left. lam f. lam arg. lam right.
        let inner = f arg { opt with fmt = Raw { fmt = Html {} } } in
        match inner with "" then "" else join [left, inner, right]

    -- Top-of-page documentation wrapper
    sem renderTopPageDoc (data: RenderingData) =
    | { fmt = Html {} } & opt -> htmlRenderWrapper opt "<div class=\"top-doc\">\n<pre>" renderTopPageDoc data "</pre>\n</div>"    
    
    -- Doc block wrapper; the Bool controls the goto-link inclusion
    sem renderDocBloc (data : RenderingData) =
    | { fmt = Html {} } & opt -> htmlRenderWrapper opt "<div class=\"doc-block\">\n<pre>" renderDocBloc data "</pre>\n</div>"

    -- Object description wrapper
    sem renderDocDescription (obj: Object) =
    | { fmt = Html {} } & opt -> htmlRenderWrapper opt "<div class = \"doc-description\"><pre>" renderDocDescription obj "</pre></div>"

    -- Object signature wrapper
    sem renderDocSignature (obj: Object) =
    | { fmt = Html {} } & opt -> htmlRenderWrapper opt "<div class=\"doc-signature\">" renderDocSignature obj "</div>"
    
    -- Code block wrapper (without preview toggle)
    sem renderCodeWithoutPreview (data: RenderingData) =
    | { fmt = Html {} } & opt -> htmlRenderWrapper opt "<div class=\"code-block\"><pre>" renderCodeWithoutPreview data "</pre></div>"

    -- Plain anchor for “goto” links
    sem renderGotoLink (link: String) =
    | { fmt = Html {} } & opt -> join ["<a class=\"gotoLink\" href=\"", link, "\">[→]</a>"]
    
    -- Toggleable hidden code block; uses a button and a collapsible div
    sem renderHidenCode (code: String) (jumpLine: Bool) =
    | { fmt = Html {} } & opt ->
        let jsDisplay = "<button class=\"toggle-btn\" onclick=\"toggle(this)\">...</button><div class=\"hiden-code\" style=\"display: none;\">" in
        join [jsDisplay, if jumpLine then "\n" else "", code, "</div>"]
    
    -- Generic link with optional URL prefix
    sem renderLink (title : String) (link : String) =
    | { fmt = Html {}, urlPrefix = urlPrefix } & opt -> join ["<a href=\"", concat urlPrefix link, "\">", title, "</a>"]

    
end
