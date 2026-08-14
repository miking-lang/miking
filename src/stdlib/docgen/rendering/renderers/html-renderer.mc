include "./renderer-interface.mc"
include "./headers/html-header.mc"
include "../../global/ext-utils.mc"
include "../util.mc"
include "docgen/rendering/rendering-options.mc"
include "docgen/global/util.mc"
include "docgen/rendering/renderers/headers/html-style.mc"
include "docgen/rendering/renderers/headers/html-script.mc"
include "seq.mc"
include "docgen/rendering/renderers/headers/search.mc"
include "docgen/rendering/rendering-data.mc"
include "string.mc"

-- The HTML renderer implementation 
lang HtmlRenderer = RendererInterface

    sem renderSetup +=
    | { fmt = Html {} } & opt ->
        let srcPath = renderingOptionsSrcPath opt in
        renderFileOrWarn (pathConcat srcPath htmlStylePath) htmlStyle;
        renderFileOrWarn (pathConcat srcPath htmlScriptPath) htmlScript

    sem renderHeader obj +=
    | { fmt = Html {} } & opt ->
      let header = getHeader (objName obj) opt.srcFolder in
      let rawHeader = renderWithRaw opt "" renderHeader obj "" in -- Render the parent link
      join [header, "\n", rawHeader]

    sem renderFooter obj +=
    | { fmt = Html {} } & opt -> "</div></body>\n</html>"   

    sem renderSearchPath (path: String) +=
    | { fmt = Html {} } & opt ->
       pathConcat path (searchPath ".js")

    sem renderSearchFile (searchDatas: [SearchDictObj]) +=
    | { fmt = Html {} } & opt ->
      let path = pathConcat (renderingOptionsSrcPath opt) (searchPath ".js") in
      let content = searchJs searchDatas in
      renderFileOrWarn path content

    sem renderTopPageDoc (data: RenderingData) +=
    | { fmt = Html {} } & opt -> renderWithRaw opt "<div class=\"top-doc\">\n<pre>" renderTopPageDoc data "</pre>\n</div>"

    sem renderTitle size s +=
    | { fmt = Html {} } & opt ->
        let sizeStr = int2string (if gti size 6 then 6 else size) in
        join ["<h", sizeStr, ">", renderTitle size s { opt with fmt = Raw { fmt = Html {}} }, "</h", sizeStr, ">", renderNewLine opt]
    
    -- Bold text
    sem renderBold (text : String) +=
    | { fmt = Html {} } & opt -> join ["<strong>", text, "</strong>"]

    -- Italic text
    sem renderItalic (text : String) +=
    | { fmt = Html {} } & opt -> join ["<em>", text, "</em>"]

    -- New line for inline contexts
    sem renderNewLine +=
    | { fmt = Html {} } & opt -> "<br>"

    -- Escaping for documentation content (also normalizes `<br>` to actual newlines)
    sem renderRemoveDocForbidenChars (s: String) +=
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
    sem renderRemoveCodeForbidenChars (s: String) +=
    | { fmt = Html {} } & opt -> renderRemoveDocForbidenChars s opt

    -- Small helper to wrap inner content with an HTML span and a CSS class
    sem htmlRenderSpan : String -> String -> String
    sem htmlRenderSpan =
    | content -> lam form. join ["<span class=\"", form, "\">", content, "</span>"]

    -- Syntax coloring: types, vars, keywords, comments, strings, multi-line comments, numbers
    sem renderType (content : String) += 
    | { fmt = Html {} } & opt -> htmlRenderSpan content "tp"

    sem renderVar (content : String) +=
    | { fmt = Html {} } & opt -> htmlRenderSpan content "var"
    
    sem renderKeyword (content : String) +=
    | { fmt = Html {} } & opt -> htmlRenderSpan content "kw"
    
    sem renderComment (content : String) +=
    | { fmt = Html {} } & opt -> htmlRenderSpan content "comment"
    
    sem renderString (content : String) +=
    | { fmt = Html {} } & opt -> htmlRenderSpan content "string"
    
    sem renderMultiLineComment (content : String) +=
    | { fmt = Html {} } & opt -> htmlRenderSpan content "multi"

    sem renderNumber (content : String) +=
    | { fmt = Html {} } & opt -> htmlRenderSpan content "number"


    sem renderSynVariants (obj: Object) (variants: [SynVariant]) +=
    | { fmt = Html {} } & opt -> renderWithRaw opt "<div class=\"syn-variants\">" (renderSynVariants obj) variants "</div>"
    
    -- Doc block wrapper; the Bool controls the goto-link inclusion
    sem renderDocBloc (data : RenderingData) (asChildren: Bool) +=
    | { fmt = Html {} } & opt -> renderWithRaw opt "<div class=\"doc-block\">\n<pre>" (renderDocBloc data) asChildren "</pre>\n</div>"

    -- Object description wrapper
    sem renderDocDescription (desc: String) +=
    | { fmt = Html {} } & opt -> renderWithRaw opt "<div class = \"doc-description\"><pre>" renderDocDescription desc "</pre></div>"
    -- Object signature wrapper
    sem renderDocSignature (obj: Object) +=
    | { fmt = Html {} } & opt -> renderWithRaw opt "<div class=\"doc-signature\">" renderDocSignature obj "</div>"
    
    -- Code block wrapper (without preview toggle)
    sem renderCodeWithoutPreview (data: RenderingData) +=
    | { fmt = Html {} } & opt -> renderWithRaw opt "<div class=\"code-block\"><pre>" renderCodeWithoutPreview data "</pre></div>"

    -- Tests block wrapper (without preview toggle)
    sem renderDocTests (data: RenderingData) (hide: Bool) +=
    | { fmt = Html {} } & opt -> renderWithRaw opt "<div class=\"code-block\"><pre>" (renderDocTests data) hide "</pre></div>"

    -- Plain anchor for “goto” links
    sem renderGotoLink (link: String) +=
    | { fmt = Html {} } & opt -> join ["<a class=\"gotoLink\" href=\"", link, "\">[→]</a>"]
    
    sem renderHookLink (title: String) (link: String) (highlight: Bool) +=
    | { fmt = Html {} } & opt -> join ["<a class=\"hookLink", if highlight then " hookLink--highlight" else "", "\" href=\"", link, "\">", title,"</a>"]

    sem renderPageLink (title: String) (link: String) +=
    | { fmt = Html {} } & opt -> join ["<a class=\"pageLink\" href=\"", link, "\">", title, "</a>"]

    sem renderParentLink (obj: Object) +=
    | { fmt = Html {} } & opt -> renderWithRaw opt "<div class=\"parent-link\">" renderParentLink obj "</div>"

    -- Toggleable hidden code block; uses a button and a collapsible div
    sem renderHidenCode (hidden: String) (shown: String) (code: String) (jumpLine: Bool) +=
    | { fmt = Html {} } & opt ->
        let jsDisplay = join ["<button class=\"toggle-btn\" data-hidden=\"", hidden, "\" data-shown=\"", shown, "\" onclick=\"toggle(this)\">",
                      hidden, "</button><div class=\"hiden-code\" style=\"display: none;\">"] in
        join [jsDisplay, if jumpLine then "\n" else "", code, "</div>"]
    
    -- Generic link with optional URL prefix
    sem renderLink (title : String) (link : String) +=
    | { fmt = Html {}, urlPrefix = urlPrefix } & opt -> join ["<a href=\"", link, "\">", title, "</a>"]

    sem renderTooltip (title : String) (content : String) +=
    | { fmt = Html {}, urlPrefix = urlPrefix } & opt ->
      join ["<div class=\"tooltip\">", title, "<span class=\"tooltip-text\">", content, "</span></div>"]

    
end
