include "./renderer-interface.mc"
include "seq.mc"
include "docgen/global/util.mc"
include "char.mc"

lang MarkdownRenderer = RendererInterface

    -- Render headings as Markdown titles (#, ##, …)
    sem renderTitle size s +=
    | { fmt = Md {} } & opt -> 
        let size = if gti size 6 then 6 else size in
        let nl = renderNewLine opt in    
        join [make size '#', " ", s, nl, nl]


    sem mdRenderItem : String -> String -> String
    sem mdRenderItem =
    | guard -> lam s.
        -- We avoid putting the ending guards on the newline
        match splitOnR (neqChar '\n') (reverse s) with (newlines, content) in
        let content = reverse content in
        join [guard, content, guard, newlines]

    -- Bold text
    sem renderBold (text : String) +=
    | { fmt = Md {} } & opt -> mdRenderItem "**" text
    
    -- Italic text
    sem renderItalic (text : String) +=
    | { fmt = Md {} } & opt -> mdRenderItem "*" text

    -- New line (Markdown convention: 2 spaces before newline)
    sem renderNewLine +=
    | { fmt = Md {} } & opt -> "  \n"

    -- Escape forbidden characters in docstrings
    sem renderRemoveDocForbidenChars (s: String) +=
    | { fmt = Md {} } & opt ->
        switch s
        case "*" ++ r | "_" ++ r | "`" ++ r | "[" ++ r | "]" ++ r | "(" ++ r | ")" ++ r | "#" ++ r | "+" ++ r | "-" ++ r | "!" ++ r | "\\" ++ r | "<" ++ r | ">" ++ r | "`" ++ r | "{" ++ r | "}" ++ r then
             concat ['\\', head s] (renderRemoveDocForbidenChars r opt)
        case [x] ++ r then cons x (renderRemoveDocForbidenChars r opt)
        case "" then ""
        end

    -- Escape forbidden characters in code snippets
    sem renderRemoveCodeForbidenChars (s: String) +=
    | { fmt = Md {} } & opt ->
        switch s
        case "```" ++ r then
             concat "'''" (renderRemoveCodeForbidenChars r opt)
        case [x] ++ r then cons x (renderRemoveCodeForbidenChars r opt)
        case "" then ""
        end

    -- Render documentation text (cleans spaces and escapes forbidden chars)
    sem renderDocDescription desc +=
    | { fmt = Md {} } & opt -> desc

    -- Render object signature inside a fenced code block
    sem renderDocSignature (obj: Object) +=
    | { fmt = Md {} } & opt ->
        let sign = renderDocSignature obj  { opt with fmt = Raw { fmt = Md {} } } in
        let nl = renderNewLine opt in    
        match sign with "" then
            ""
        else
            join ["```mc\n", sign, "\n```", nl]

    -- Render "goto" link (delegates to raw link, wrapped with spacing)
    sem renderGotoLink (link: String) +=
    | { fmt = Md {} } & opt -> let nl = renderNewLine opt in
        join [nl, renderGotoLink link  { opt with fmt = Raw { fmt = Md {} } }, nl, nl]
    
    -- Render a single link
    sem renderLink (title : String) (link : String) +=
    | { fmt = Md {}, urlPrefix = urlPrefix } & opt -> join ["[", title, "](", link, ")"]

    -- Render list of links (comma separated)
    sem renderLinkList (objects: [Object]) +=
    | { fmt = Md {} } & opt ->
        let nl = renderNewLine opt in
        join [renderLinkList objects { opt with fmt = Raw { fmt = Md {}} }, nl]
end
