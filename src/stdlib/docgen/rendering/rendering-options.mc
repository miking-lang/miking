-- # Rendering Options
--
-- Throughout the rendering process, we keep track of a `RenderingOptions` object.  
-- This structure stores essential information that controls how documentation is generated.  

-- ## Name Context
--
-- The `nameContext` is crucial: it allows us to determine the link to an object **without having direct access to the object itself**, 
-- relying only on its name.
--
-- This is achieved with a hashmap that tracks all rendered objects:
-- - Each time we render a new named object, we register it in the map.
-- - If a name already exists, it may be shadowed by the new entry.
--
-- The name map naturally handles nested names. For example:
-- ```miking
-- let x = let y = 2 in 3
-- ```
-- After rendering `x`, `y` will no longer be visible in the `nameContext`.
--
-- ## Handling Nested Variables
--
-- A subtle issue arises when dealing with **nested variables**:  
-- - Some should not shadow global variables (e.g., local variables inside a `let`).  
-- - Others, however, should remain accessible (e.g., variables defined inside a `Program`, since they are part of an `include`).  
--
-- To resolve this, we preserve or update the `nameContext` only when the current node is of kind **Program** or **Lang**.  
-- For details, see `./renderers/objects-renderer.mc`.

include "./../global/format-language.mc"
include "./../global/format.mc"
include "./rendering-types.mc"

-- ## RenderingOptions
--
-- The configuration object passed around during rendering.
type RenderingOptions = use Formats in use FormatLanguages in
    {
        fmt: Format, 
        noStdlib: Bool, 
        outputFolder: String,
        srcFolder: String,
        urlPrefix: String, 
        fmtLang: FormatLanguage, 
        letDepth: Option Int, 
        nameContext: HashMap String String,
        jsSearchCode: String,
        log: Logger
    }
