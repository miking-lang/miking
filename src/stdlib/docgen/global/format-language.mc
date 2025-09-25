-- # FormatLanguages Module
--
-- Miking-doc-gen can generate MDX code. MDX is written in React, and React
-- supports both TypeScript and JavaScript. This module defines a small language
-- to indicate in which format the output should be produced.

include "string.mc"

lang FormatLanguages
    -- Represents the supported output languages for MDX rendering.
    syn FormatLanguage =
    | Js {}
    | Ts {}

    -- Converts a `FormatLanguage` into its string representation.
    sem formatLanguageToStr : FormatLanguage -> String
    sem formatLanguageToStr =
    | Js {} -> "Js"
    | Ts {} -> "Ts"

    -- Returns the default output language.
    sem defaultFormatLanguage : () -> FormatLanguage
    sem defaultFormatLanguage =
    | _ -> Ts {}

    -- Returns the file extension associated with a `FormatLanguage`.
    sem formatLanguageGetExt : FormatLanguage -> String
    sem formatLanguageGetExt =
    | Ts {} -> "tsx"
    | Js {} -> "jsx"

end
