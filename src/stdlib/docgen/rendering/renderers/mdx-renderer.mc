-- This module implements the MdxRenderer, an instance of `RendererInterface`.
-- It outputs MDX pages compatible with Docusaurus, delegating text formatting to
-- the Markdown renderer where appropriate, and using shared MDX components.

include "./renderer-interface.mc"
include "./headers/mdx-components.mc"
include "../util.mc"
include "../../global/ext-utils.mc"

include "sys.mc"
include "docgen/rendering/renderers/headers/search.mc"
include "string.mc"
include "docgen/global/util.mc"
include "docgen/rendering/rendering-options.mc"
include "docgen/rendering/renderers/headers/mdx-style.mc"
include "bool.mc"
include "fileutils.mc"
include "seq.mc"
include "docgen/global/source-code.mc"
include "basic-types.mc"
include "option.mc"
include "docgen/rendering/rendering-data.mc"

let componentFileName = "MikingDocGen"
let searchFileName = searchPath ""

-- Provides the MDX renderer implementation and its dispatch rules.
lang MdxRenderer = RendererInterface

    ----------------- MDX helpers -----------------

    -- Build an absolute path "<folder>/<name>.<ext>" for the components file.
    sem mdxGetComponentPath : FormatLanguage -> String -> String -> String
    sem mdxGetComponentPath =
    | fmtLang -> lam path. lam name.
        let ext = formatLanguageGetExtWithDot fmtLang in
        let name = if strEndsWith ext name then name else concat name ext in
        pathConcat path name

    sem mdxCreateCategoryFile =
    | opt -> lam dir. lam name.
        let path = pathConcat dir "_category_.yaml" in
        let path = pathConcat opt.outDir path in
        let content = concat "label: " name in
        renderFileOrWarn path content

    ----------------- Renderer Implementation -----------------

    -- Create the MDX components file (TSX/JSX) in the output folder.
    sem renderSetup +=
    | { fmt = Mdx {} } & opt ->
        let srcPath = renderingOptionsSrcPath opt in
        let path = mdxGetComponentPath opt.fmtLang srcPath componentFileName in

        let components = match opt.fmtLang with Ts {} then mdxTsComponents else mdxJsComponents in
        renderFileOrWarn path components;

        let path = pathConcat srcPath mdxCssFileName in
        renderFileOrWarn path mdxCss


    -- Emit import line for MDX components used by the page.
    sem renderHeader obj +=
    | { fmt = Mdx {} } & opt ->
        let formatPath = lam path.
            --  strip .tsx/.jsx extension from the import path if present
            let path = 
                if or (strEndsWith ".tsx" path) (strEndsWith ".jsx" path)
                    then subsequence path 0 (subi (length path) 4)
                else path
            in
            normalizePath path
        in

        let loc = objGetMyLocation obj opt in
        let name = objName obj in

        -- We only create category.yml if the object has children.
        (if objHasChildren obj then mdxCreateCategoryFile opt (dirname loc) name else ());

        let componentsPath = mdxGetComponentPath opt.fmtLang opt.urlPrefix componentFileName in
        let searchPath = renderSearchPath opt.urlPrefix opt in

        let imports = formatPath componentsPath in
        let search = formatPath searchPath in
        
        join [
          "import { DocBlock, Span, Signature, Description, ToggleWrapper} from '@site/", imports, "';\n",
          "import Search from '@site/", search, "';\n\n",

          "<Search />\n\n"
        ]

    sem renderSearchPath (path: String) +=
    | { fmt = Mdx {} } & opt ->
        mdxGetComponentPath (Js {}) path searchFileName

    sem renderSearchFile (searchDatas: [SearchDictObj]) += 
    | { fmt = Mdx {} } & opt ->
        let path = renderSearchPath (renderingOptionsSrcPath opt) opt in
        let content = searchReact searchDatas in
        renderFileOrWarn path content


    -- Reuse Markdown escaping for code.
    sem renderRemoveCodeForbidenChars (s: String) +=
    | { fmt = Mdx {} } & opt -> renderRemoveCodeForbidenChars s { opt with fmt = Md {} }

    -- Reuse Markdown escaping for docs.
    sem renderRemoveDocForbidenChars (s: String) +=
    | { fmt = Mdx {} } & opt -> mdxEscape s

    -- Delegate headings to Markdown renderer.
    sem renderTitle size s +=
    | { fmt = Mdx {} } & opt -> renderTitle size s { opt with fmt = Md {} }

    -- Delegate bold text to Markdown renderer.
    sem renderBold (text : String) +=
    | { fmt = Mdx {} } & opt -> renderBold text { opt with fmt = Md {} }

    -- Delegate italic text to Markdown renderer.
    sem renderItalic (text : String) +=
    | { fmt = Mdx {} } & opt -> renderItalic text { opt with fmt = Md {} }

    -- Delegate newline rendering to Markdown renderer ("  \n").
    sem renderNewLine +=
    | { fmt = Mdx {} } & opt -> renderNewLine { opt with fmt = Md {} }

    -- Render object description as an MDX <Description> block (omit empty default).
    sem renderDocDescription desc +=
    | { fmt = Mdx {} } & opt ->
      let desc = renderDocDescription desc { opt with fmt = Md {} } in
      let desc = if eqString desc "No documentation available here." then "" else desc in
      if eqString "" desc then "" else join ["\n<Description>\n", desc, "\n</Description>\n"]
        
    -- The goto link is directly handled in mdx component, so we always return empty string.    
    sem renderGotoLink (link: String) +=
    | { fmt = Mdx {} } & opt -> ""
    
    -- Render a single link, removing the trailing ".md" for Docusaurus routes.
    sem renderLink (title : String) (link : String) +=
    | { fmt = Mdx {} } & opt ->
          let linkLength = length link in
          let link =
              if strEndsWith ".md" link then subsequence link 0 (subi linkLength 3)
              else link
          in
          join ["<a href={\"", link, "\"} className=\"link\">", title, "</a>"]
    
    -- Render a list of links by delegating to raw rendering, then add a newline.
    sem renderLinkList (objects: [Object]) +=
    | { fmt = Mdx {} } & opt ->
        renderWithRaw opt "" renderLinkList objects (renderNewLine opt)

    -- Escape characters unsafe for MDX / JSX / Markdown text
    sem mdxEscape =
    | s ->
        if null s then "" else
        match switch s
        case "&" ++ r then ("&#38;",  r)
        case "<" ++ r then ("&#60;",  r)
        case ">" ++ r then ("&#62;",  r)
        case "{" ++ r then ("&#123;", r)
        case "}" ++ r then ("&#125;", r)
        case "\"" ++ r then ("&#34;", r)
        case "'" ++ r then ("&#39;", r)
        case "`" ++ r then ("&#96;",  r)
        case "=" ++ r then ("&#61;",  r)
        case "/" ++ r then ("&#47;",  r)
        case "*" ++ r then ("&#42;",  r)
        case "_" ++ r then ("&#95;",  r)
        case [x] ++ r then ([x], r)
        end with (prefix, rest) in
        concat prefix (mdxEscape rest)


    -- Render a list of links by delegating to raw rendering, then add a newline.
    sem renderSourceCode (code: SourceCode) (obj: Option Object) +=
    | { fmt = Mdx {} } & opt ->
        if optionIsNone obj then
            let code = sourceCodeToStr code in
            let code = renderRemoveCodeForbidenChars code opt in
            if null code then ""
            else join ["\n```mc\n", code, "\n```\n"]
        else
            let code = sourceCodeToStr code in
            let code = mdxEscape code in
            let code = strToSourceCode code in
            renderWithRaw opt "" (renderSourceCode code) obj ""

    sem renderHidenCode (hidden: String) (shown: String) (code: String) (jumpLine: Bool) +=
    | { fmt = Mdx {} } & opt ->
      join ["\n<ToggleWrapper shownText=\"", shown, "\" hiddenText=\"", hidden, "\">\n", code, "\n</ToggleWrapper>", if jumpLine then "\n" else ""]

    sem renderDocSignature (obj: Object) +=
    | { fmt = Mdx {} } & opt ->
        let sign = renderPureDocSignature obj opt in
        let sign = mdxEscape sign in
        let sign = strToSourceCode sign in
        let sign = join (map (lam code. renderWord code (Some obj) { opt with fmt = Raw { fmt = Mdx {} }}) sign) in
        
        let variants = renderVariants obj opt in
        let sign = if null variants then sign else concat sign variants in
        mdxRenderSpan sign "doc-signature"

    -- Render the full code (trim trailing comments/empties), escaped for MDX.
    sem renderCodeWithoutPreview (data: RenderingData) +=
    | { fmt = Mdx {} } & opt ->
        let split = strSplit "\n" data.code in
        match splitOnR (lam l.
            let trimmed = strTrim l in
            not (or (strStartsWith "--" trimmed) (null trimmed))
        ) (reverse split) with (_, right)  in
        let code = strJoin "\n" (reverse right) in
        let data = { data with code = code } in
        renderWithRaw opt "" renderCodeWithoutPreview data ""


    -- Render a full documentation block (title, signature, desc, code, optional tests).
    sem renderDocBloc (data: RenderingData) (asChildren: Bool) +=
    | { fmt = Mdx {} } & opt ->
        let link = objGetMyLink data.obj opt in
        let linkLength = length link in
        let link = if strEndsWith ".md" link then subsequence link 0 (subi linkLength 3) else link in -- remove extension for Docusaurus
        let link = if and (not (objIsArtificial data.obj)) (objHasUrl data.obj) then join [" link=\"", link, "\""] else "" in 
        
        let title = objTitle data.obj in
        let form  = objGetFirstWord data.obj in
    
        let left = join ["<DocBlock title=\"", title, "\" form=\"", form, "\"", link, ">\n"] in
        let right = "\n</DocBlock>\n\n" in
        renderWithRaw opt left (renderDocBloc data) asChildren right

    sem renderCreateTests (tests: [RenderingData]) +=
    | { fmt = Mdx {} } & opt ->
        let tests = strJoin "\n\n" (map
            (lam t. sourceCodeToStr (objSourceCode t.obj)) tests)
        in
        let tests = strToSourceCode tests in
        renderSourceCode tests (None {}) opt

    sem mdxRenderSpan : String -> String -> String
    sem mdxRenderSpan =
    | content -> lam form.
        -- We trim to make sure the string doesn't break mdx syntax.
        let content = strTrim content in
        let content = strJoin " " (strSplit "\n" content) in
        if null content then "" else
        join [
          "<span className=\"",
          form,
          "\">",
          content,
          "</span>"
        ]

    sem renderType (content : String) +=
    | { fmt = Mdx {} } & opt -> mdxRenderSpan content "tp"

    sem renderVar (content : String) +=
    | { fmt = Mdx {} } & opt -> content

    sem renderKeyword (content : String) +=
    | { fmt = Mdx {} } & opt -> mdxRenderSpan content "kw"

    sem renderComment (content : String) +=
    | { fmt = Mdx {} } & opt -> mdxRenderSpan content "comment"

    sem renderString (content : String) +=
    | { fmt = Mdx {} } & opt -> mdxRenderSpan content "string"

    sem renderMultiLineComment (content : String) +=
    | { fmt = Mdx {} } & opt -> mdxRenderSpan content "multi"

    sem renderNumber (content : String) +=
    | { fmt = Mdx {} } & opt -> mdxRenderSpan content "number"

    sem renderStdlibConstLink (file: String) +=
    | { fmt = Mdx {} } & opt -> normalizePath (join ["/", opt.stdlibFolder, "/", opt.urlPrefix, "/", file])

    sem renderSynVariants (obj: Object) (variants: [SynVariant]) +=
    | { fmt = Mdx {} } & opt ->
        renderWithRaw opt "<div class=\"variants\">" (renderSynVariants obj) variants "</div>"

    sem renderTypeConstructors (obj: Object) +=
    | { fmt = Mdx {} } & opt ->
        renderWithRaw opt "<div className=\"variants\">" renderTypeConstructors obj "</div>"

    sem renderOneVariant (obj: Object) (v: SynVariant) +=
    | { fmt = Mdx {} } & opt ->
        renderWithRaw opt "<div className=\"variant\">" (renderOneVariant obj) v "</div>"


end
