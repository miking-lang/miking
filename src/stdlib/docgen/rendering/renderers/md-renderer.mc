-- # Markdown Renderer for mi-doc-gen
--
-- This module implements the **MarkdownRenderer**, an instance of `RendererInterface`.
-- It generates Markdown (`.md`) documentation files from the extracted ObjectTree.
--
-- ## Design
-- - Titles are rendered as Markdown headings (`#`, `##`, … up to 6 levels).
-- - Bold text is wrapped in `**`.
-- - Newlines use the Markdown convention `"  \n"` (two spaces + newline).
-- - Documentation and code require escaping of Markdown special characters
--   (done in `renderRemoveDocForbidenChars` and `renderRemoveCodeForbidenChars`).
-- - Signatures are wrapped in fenced code blocks ```mc.
-- - Links and goto links are rendered as `[title](url)`.
-- - `renderLinkList` generates a comma-separated list of object links.
--
-- Like other renderers, it sometimes delegates to the **RawRenderer**
-- to ensure base rendering logic is reused consistently.

include "./renderer-interface.mc"

lang MarkdownRenderer = RendererInterface

    -- Render headings as Markdown titles (#, ##, …)
    sem renderTitle size s =
    | { fmt = Md {} } & opt -> 
        let size = if gti size 6 then 6 else size in
        let nl = renderNewLine opt in    
        join [make size '#', " ", s, nl, nl]

    -- Bold text
    sem renderBold (text : String) =
    | { fmt = Md {} } & opt -> join ["**", text, "**"]

    -- New line (Markdown convention: 2 spaces before newline)
    sem renderNewLine =
    | { fmt = Md {} } & opt -> "  \n"

    -- Escape forbidden characters in docstrings
    sem renderRemoveDocForbidenChars (s: String) =
    | { fmt = Md {} } & opt ->
        switch s
        case "*" ++ r | "_" ++ r | "`" ++ r | "[" ++ r | "]" ++ r | "(" ++ r | ")" ++ r | "#" ++ r | "+" ++ r | "-" ++ r | "!" ++ r | "\\" ++ r | "<" ++ r | ">" ++ r | "`" ++ r | "{" ++ r | "}" ++ r then
             concat ['\\', head s] (renderRemoveDocForbidenChars r opt)
        case [x] ++ r then cons x (renderRemoveDocForbidenChars r opt)
        case "" then ""
        end

    -- Escape forbidden characters in code snippets
    sem renderRemoveCodeForbidenChars (s: String) =
    | { fmt = Md {} } & opt ->
        switch s
        case "`" ++ r then
             concat ['\\', head s] (renderRemoveCodeForbidenChars r opt)
        case [x] ++ r then cons x (renderRemoveCodeForbidenChars r opt)
        case "" then ""
        end

    -- Render documentation text (cleans spaces and escapes forbidden chars)
    sem renderDocDescription : Object -> Format -> String
    sem renderDocDescription obj =
    | { fmt = Md {} } & opt ->
        let nl = renderNewLine opt in
        let doc = objDoc obj in
        match splitOnR (lam c. match c with ' ' | '\n' then false else true) doc with { right = doc } in
        let doc = strReplace "\n " "\n" doc in
        renderRemoveDocForbidenChars doc opt
    

    -- Render object signature inside a fenced code block
    sem renderDocSignature (obj: Object) =
    | { fmt = Md {} } & opt ->
        let sign = renderDocSignature obj  { opt with fmt = Raw { fmt = Md {} } } in
        let nl = renderNewLine opt in    
        match sign with "" then
            ""
        else
            join ["```mc\n", sign, "\n```", nl]

    -- Render "goto" link (delegates to raw link, wrapped with spacing)
    sem renderGotoLink (link: String) =
    | { fmt = Md {} } & opt -> let nl = renderNewLine opt in
        join [nl, renderGotoLink link  { opt with fmt = Raw { fmt = Md {} } }, nl, nl]
    
    -- Render a single link
    sem renderLink (title : String) (link : String) =
    | { fmt = Md {}, urlPrefix = urlPrefix } & opt -> join ["[", title, "](", concat urlPrefix link, ")"]

    -- Render list of links (comma separated)
    sem renderLinkList (objects: [Object]) =
    | { fmt = Md {} } & opt ->
        let nl = renderNewLine opt in
        join [renderLinkList objects { opt with fmt = Raw { fmt = Md {}} }, nl]
end
