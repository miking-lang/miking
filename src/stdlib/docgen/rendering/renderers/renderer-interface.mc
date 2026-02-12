-- This file defines the interface for a renderer.
--
-- To add a new format:
-- 1. Implement this interface for your format.
-- 2. Add the new format in ../../global/format.mc.
-- 3. Override only the functions you need. 
--    A default implementation (raw text renderer) is available in ./raw-renderer.mc.
-- 
-- It is strongly recommended to inspect `raw-renderer.mc` first.
-- The default implementation is well-structured, so you rarely need to redefine everything.

include "../../global/objects.mc"
include "../../global/format.mc"
include "../../global/format-language.mc"
include "../../global/source-code.mc"

include "../rendering-data.mc"
include "../rendering-options.mc"

include "./objects-renderer.mc"

include "mexpr/type-check.mc"
include "mexpr/pprint.mc"

lang RendererInterface = 
    Formats + ObjectsRenderer + TokenReader + SourceCodeWordKinds + 
    MExprPrettyPrint + MetaVarTypePrettyPrint + FormatLanguages

    -------------------- Setup --------------------

    -- Called before rendering starts for all files.
    -- Typically used to generate global headers.
    sem renderSetup : RenderingOptions -> ()

    -- Called before rendering each file.
    -- Typically used to push file headers or includes.
    sem renderHeader : Object -> RenderingOptions -> String

    -- Called after rendering each file.
    -- Can be used to push file footers.
    sem renderFooter : Object -> RenderingOptions -> String


    -------------------- Search File --------------------

    -- Build the path to the search file.
    -- The first parameter is the path to the search file folder.
    sem renderSearchPath : String -> RenderingOptions -> String

    -- Write the final version of the search engine.
    sem renderSearchFile : [SearchDictObj] -> RenderingOptions -> ()


    ----------------- Page Items -----------------

    -- Renders the top section of a page.
    -- Includes code toggle, and top documentation.
    sem renderTopPageDoc : RenderingData -> RenderingOptions -> String

    -- Renders a documentation block for an object.
    -- Includes title, goto link, code toggle, top doc, and signature.
    sem renderDocBloc : RenderingData -> Bool -> RenderingOptions -> String

    -- Renders the raw string of the signature without colorising it
    sem renderPureDocSignature : Object -> RenderingOptions -> String

    -- Renders the signature of an object.
    sem renderDocSignature : Object -> RenderingOptions -> String

    sem renderVariants : Object -> RenderingOptions -> String

    sem renderOneVariant : Object -> SynVariant -> RenderingOptions -> String

    -- Renders the documentation string of an object (from its `doc` field).
    sem renderDocDescription : String -> RenderingOptions -> String

    -- Renders the unit tests associated with an object.
    sem renderDocTests : RenderingData -> Bool -> RenderingOptions -> String

    syn DocObjectParsed =

    -- Parses a documentation block.
    sem renderDocObjectParse : String -> RenderingOptions -> DocObjectParsed

    -- Render the output of renderDocObjectParse into a string well formatted.
    sem renderFormattedDoc : Object -> DocObjectParsed -> Bool -> RenderingOptions -> String

    -- Render a tooltip, which is a popup containing text,
    -- activated on mouseover.
    sem renderTooltip : String -> String -> RenderingOptions -> String 

    sem renderTooltipSign : Object -> RenderingOptions -> String

    ----------------- Linking -----------------

    -- Renders a list of links for a list of objects.
    sem renderLinkList : [Object] -> RenderingOptions -> String

    -- Renders a single "goto" link to another documentation page.
    sem renderGotoLink : String -> RenderingOptions -> String

    -- Renders a link toward a page indicated in the title.
    -- Used for the include and use links.
    sem renderPageLink : String -> String -> RenderingOptions -> String

    -- Render a hook link.
    sem renderHookLink : String -> String -> Bool -> RenderingOptions -> String

    -- Renders the "parent" link to another documentation page.
    sem renderParentLink : Object -> RenderingOptions -> String

    -- Renders a single link: first argument is title, second is raw link.
    sem renderLink : String -> String -> RenderingOptions -> String

    -- Render a link toward another object page.
    sem renderHook : Object -> String -> Bool -> RenderingOptions -> String 

    sem renderStdlibConstLink : String -> RenderingOptions -> String

    ----------------- Code Rendering -----------------

    -- Renders a block of code wrapped in a toggleable hidden section.
    -- Bool argument decides whether it starts hidden.
    sem renderHidenCode : String -> String -> String -> Bool -> RenderingOptions -> String


    sem renderCodeWithPreview : RenderingData -> RenderingOptions -> String

    -- Renders code directly, without preview/toggling.
    sem renderCodeWithoutPreview : RenderingData -> RenderingOptions -> String

    -- Renders a source code string with syntax highlighting.
    -- If an object is provided, the types will be clickable
    sem renderSourceCodeStr : String -> Option Object -> RenderingOptions -> String

    -- Renders structured source code (tokenized/colored).
    -- If an object is provided, the types will be clickable    
    sem renderSourceCode : SourceCode -> Option Object -> RenderingOptions -> String

    -- Renders a single token word.
    -- If an object is provided, the types will be clickable
    sem renderWord : SourceCodeWord -> Option Object -> RenderingOptions -> String


    ----------------- Rendering Objects Creation -----------------

    sem renderCreateTests : [RenderingData] -> RenderingOptions -> String

    -- Create The rendering data for the given object.
    -- The list of rendering data are supposed to be the associated tests.
    sem renderCreateRenderingData : Object -> [RenderingData] -> RenderingOptions -> RenderingData

    -- Render the variants from list of a syn.
    sem renderSynVariants : Object -> [SynVariant] -> RenderingOptions -> String

    -- Render the constructors of a given type (using the name context API)
    sem renderTypeConstructors : Object -> RenderingOptions -> String

    ----------------- Basic Formatting Helpers -----------------

    -- Renders a section title (e.g., "Variables", "Types").
    sem renderSectionTitle : String -> RenderingOptions -> String

    -- Renders a string in bold.
    sem renderBold : String -> RenderingOptions -> String

    -- Renders a string in italic.
    sem renderItalic : String -> RenderingOptions -> String

    -- Renders a page title, size determines heading level
    -- (larger size -> smaller title).
    sem renderTitle : Int -> String -> RenderingOptions -> String

    -- Calls renderTitle with the title of an object.
    sem renderObjTitle : Int -> Object -> RenderingOptions -> String

    -- Renders a block of text.
    sem renderText : String -> RenderingOptions -> String

    sem renderNewLine : RenderingOptions -> String

    ----------------- Escaping -----------------

    -- Sanitizes a string for safe inclusion in documentation.
    sem renderRemoveDocForbidenChars : String -> RenderingOptions -> String

    -- Sanitizes a string for safe inclusion in code.
    sem renderRemoveCodeForbidenChars : String -> RenderingOptions -> String    


    ----------------- Syntax Coloring -----------------

    -- Renders a type word.
    sem renderType : String -> RenderingOptions -> String

    -- Renders a variable word.
    sem renderVar : String -> RenderingOptions -> String

    -- Renders a keyword.
    sem renderKeyword : String -> RenderingOptions -> String

    -- Renders a comment.
    sem renderComment : String -> RenderingOptions -> String

    -- Renders a string literal.
    sem renderString : String -> RenderingOptions -> String

    -- Renders a number literal.
    sem renderNumber : String -> RenderingOptions -> String

    -- Renders a word with the default color.
    sem renderDefault : String -> RenderingOptions -> String

    -- Renders a multi-line comment.
    sem renderMultiLineComment : String -> RenderingOptions -> String


    ----------------- Shared helpers -----------------

    -- Wrapper that renders inner content via raw renderer, then wraps it with HTML
    sem renderWithRaw : all a. RenderingOptions -> String -> (a -> RenderingOptions -> String) -> a -> String -> String
    sem renderWithRaw =
    | opt -> lam left. lam f. lam arg. lam right.
        let inner = f arg { opt with fmt = Raw { fmt = opt.fmt } } in
        match inner with "" then "" else join [left, inner, right]


end
