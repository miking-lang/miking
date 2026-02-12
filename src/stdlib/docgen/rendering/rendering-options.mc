include "./../global/format-language.mc"
include "./../global/format.mc"
include "../naming/name-context.mc"

include "./rendered-map.mc"

-- The configuration object passed around during rendering.
type RenderingOptions = use Formats in use FormatLanguages in
    {
        fmt: Format,
        stdlibFolder: String,
        outputFolder: String,
        srcFolder: String,
        urlPrefix: String, 
        fmtLang: FormatLanguage, 
        letDepth: Option Int, 
        nameContext: NameContext,
        noCode: Bool,
        renderedMap: RenderedMap,
        log: Logger
    }

let renderingOptionsSrcPath : RenderingOptions -> String =
    lam opt. pathConcat opt.outputFolder opt.srcFolder


-- Ensure RenderingOptions uses the wrapped (non-raw) format.
let fixOptFormat : RenderingOptions -> RenderingOptions = lam opt. { opt with fmt = use Formats in unwrapRaw opt.fmt }
