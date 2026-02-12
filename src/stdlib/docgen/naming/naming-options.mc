include "../global/format.mc"

type NamingOptions = use Formats in use FormatLanguages in
    {
        debug: Bool,
        fmt: Format, 
        urlPrefix: String,
        stdlibFolder: String
    }
