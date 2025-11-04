-- # Renderer Composition
--
-- This module aggregates all renderer implementations into a single `Renderer`.
-- 
-- It imports:
-- - `RawRenderer`      → generic fallback, delegates to underlying format
-- - `HtmlRenderer`     → generates HTML pages
-- - `MarkdownRenderer` → generates Markdown output
-- - `MdxRenderer`      → generates MDX output (for Docusaurus integration)
--
-- The resulting `Renderer` is the union of all these modules, implementing the
-- `RendererInterface` and providing format-dispatched rendering.

include "./html-renderer.mc"
include "./raw-renderer.mc"
include "./md-renderer.mc"
include "./mdx-renderer.mc"

-- Unification of all the renderers, language used in ../renderer.mc.
lang Renderer = RawRenderer + HtmlRenderer + MarkdownRenderer + MdxRenderer end
