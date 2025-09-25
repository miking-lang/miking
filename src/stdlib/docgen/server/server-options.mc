include "../global/format.mc"
    
type ServerOptions = use Formats in {
    fmt: Format,
    folder: String,
    firstFile: String,
    noOpen: Bool,
    link: String
}
