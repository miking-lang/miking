include "./html-renderer.mc"
include "./raw-renderer.mc"
include "./md-renderer.mc"
include "./mdx-renderer.mc"
include "./doc-renderer.mc"

-- Unification of all the renderers, language used in ../renderer.mc.
lang Renderer = RawRenderer + DocRenderer + HtmlRenderer + MarkdownRenderer + MdxRenderer end
