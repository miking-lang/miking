-- # Renderer Interface
--
-- This file defines the interface for a renderer.
-- 
-- ## General Overview
-- - At startup, the application reads the format option (see ../../global/format.mc).
-- - Based on this format, the renderer dispatches function calls to the correct implementation.
-- - All functions return `String`, which will be written to the output file.
--
-- ## Adding a New Format
-- To add a new format:
-- 1. Implement this interface for your format.
-- 2. Add the new format in ../../global/format.mc.
-- 3. Override only the functions you need. 
--    A default implementation (raw text renderer) is available in ./raw-renderer.mc.
-- 
-- It is strongly recommended to inspect `raw-renderer.mc` first.
-- The default implementation is well-structured, so you rarely need to redefine everything.
--
-- ## Dispatch
-- Functions here are called by ../renderer.mc. They form the contract for rendering
-- headers, footers, documentation, code, links, and text formatting.

include "../../extracting/objects.mc"
include "../../global/format.mc"
include "../../global/format-language.mc"
include "../../extracting/source-code-word.mc"
include "../rendering-types.mc"
include "../rendering-options.mc"

include "./objects-renderer.mc"

include "mexpr/type-check.mc"
include "mexpr/pprint.mc"

lang RendererInterface = 
    Formats + ObjectsRenderer + TokenReader + SourceCodeWordKinds + 
    MExprPrettyPrint + MetaVarTypePrettyPrint + FormatLanguages

    -- ## Setup and File Wrappers

    -- Called before rendering starts for all files.
    -- Typically used to generate global headers.
    sem renderSetup : ObjectTree -> RenderingOptions -> ()

    -- Called before rendering each file.
    -- Typically used to push file headers or includes.
    sem renderHeader : Object -> RenderingOptions -> String

    -- Called after rendering each file.
    -- Can be used to push file footers.
    sem renderFooter : Object -> RenderingOptions -> String


    -- ## Documentation Blocks

    -- Renders the top section of a page.
    -- Includes code toggle, and top documentation.
    sem renderTopPageDoc : RenderingData -> RenderingOptions -> String

    -- Renders a documentation block for an object.
    -- Includes title, goto link, code toggle, top doc, and signature.
    sem renderDocBloc : RenderingData -> RenderingOptions -> String

    -- Renders the signature of an object.
    sem renderDocSignature : Object -> RenderingOptions -> String

    -- Renders the documentation string of an object (from its `doc` field).
    sem renderDocDescription : Object -> RenderingOptions -> String

    -- Renders the unit tests associated with an object.
    sem renderDocTests : RenderingData -> RenderingOptions -> String


    -- ## Navigation / Linking

    -- Renders a list of links for a list of objects.
    sem renderLinkList : [Object] -> RenderingOptions -> String

    -- Renders a single "goto" link to another documentation page.
    -- Takes the raw link, then calls renderLink internally.
    sem renderGotoLink : String -> RenderingOptions -> String

    -- Renders a single link: first argument is title, second is raw link.
    sem renderLink : String -> String -> RenderingOptions -> String


    -- ## Code Rendering

    -- Renders a block of code wrapped in a toggleable hidden section.
    -- Bool argument decides whether it starts hidden.
    sem renderHidenCode : String -> String -> Bool -> RenderingOptions -> String

    -- Renders code with preview:
    -- - Left part (raw code)
    -- - Right part (hidden code via renderHidenCode)
    -- - Trimmed part (raw, always visible)
    -- If the right part is empty, no toggle is shown.
    sem renderCodeWithPreview : RenderingData -> RenderingOptions -> String

    -- Renders code directly, without preview/toggling.
    sem renderCodeWithoutPreview : RenderingData -> RenderingOptions -> String

    -- Renders a source code string with syntax highlighting.
    sem renderSourceCodeStr : String -> RenderingOptions -> String

    -- Renders structured source code (tokenized/colored).
    sem renderSourceCode : SourceCode -> RenderingOptions -> String

    -- Renders a single token word.
    sem renderWord : SourceCodeWord -> RenderingOptions -> String

    -- Renders top-level source code for an object.
    -- Takes children TreeSourceCode and produces RenderingData.
    sem renderTreeSourceCode : [TreeSourceCode] -> Object -> RenderingOptions -> RenderingData


    -- ## Formatting Helpers

    -- Renders a section title (e.g., "Variables", "Types").
    sem renderSectionTitle : String -> RenderingOptions -> String

    -- Renders a string in bold.
    sem renderBold : String -> RenderingOptions -> String

    -- Sanitizes a string for safe inclusion in documentation.
    sem renderRemoveDocForbidenChars : String -> RenderingOptions -> String

    -- Sanitizes a string for safe inclusion in code.
    sem renderRemoveCodeForbidenChars : String -> RenderingOptions -> String    

    -- Renders a page title, size determines heading level
    -- (larger size -> smaller title).
    sem renderTitle : Int -> String -> RenderingOptions -> String

    -- Calls renderTitle with the title of an object.
    sem renderObjTitle : Int -> Object -> RenderingOptions -> String

    -- Renders a block of text.
    sem renderText : String -> RenderingOptions -> String


    -- ## Syntax Coloring

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

    -- Renders a single newline.
    sem renderNewLine : RenderingOptions -> String

end
