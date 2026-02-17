include "../global/format.mc"
include "../global/format-language.mc"

type NamingOptions = use Formats in use FormatLanguages in
    {
        debug: Bool,
        fmt: Format, 
        urlPrefix: String,
        stdlibFolder: String
    }
