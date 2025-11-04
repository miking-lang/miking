-- # Format Module
--
-- This module defines supported output formats for rendering and provides
-- utility functions for converting to/from strings. It is used primarily by the
-- CLI or renderer to determine the output mode.
--
-- We have 3 formats: mdx, md, and html. The Raw format is a generic wrapper
-- around another format. Its purpose is to preserve the real format while
-- enabling temporary generic code, useful for factorization and composition.

include "option.mc"
include "string.mc"

lang Formats

    -- Represents the supported output formats.
    syn Format =
    | Html {}
    | Md {}
    | Mdx {}
    | Raw { fmt : Format }

    -- Recursively unwraps a Raw format to get the underlying format.
    sem unwrapRaw : Format -> Format
    sem unwrapRaw =
    | Raw { fmt = fmt } -> unwrapRaw fmt
    | fmt -> fmt
        
    -- Converts a string into a `Format` if possible.
    -- Accepts various case-insensitive aliases and extensions.    
    sem formatFromStr : String -> Option Format
    sem formatFromStr =
     | "html" | "HTML" | "Html" | ".html" -> Some (Html {})
     | "md" | "Markdown" | "markdown" | "MARKDOWN" | "MD" | ".md" -> Some (Md {})
     | "mdx" | "MarkdownExtended" | "MarkdownExt" | "markdownext" | "MARKDOWNEXT" | "MDX" | ".mdx" -> Some (Mdx {})
     | _ -> None {}

    -- Converts a `Format` value back into a printable string.    
    sem formatToStr : Format -> String
    sem formatToStr =
    | Html {} -> "Html"
    | Md {} -> "Md"
    | Mdx {} -> "Mdx"
    | Raw { fmt = fmt } -> join ["Raw { fmt = ", formatToStr fmt, " }"]

    -- Returns the file extension associated with a given `Format`.
    sem formatGetExtension : Format -> String
    sem formatGetExtension =
    | Html {} -> "html"
    | Md {} | Mdx {} -> "md"
    | Raw { fmt = fmt } -> formatGetExtension fmt


    -- Returns the default rendering format to use when none is specified.    
    sem defaultFormat /- () -> Format -/ =
    | _ -> Html {}

    
end
