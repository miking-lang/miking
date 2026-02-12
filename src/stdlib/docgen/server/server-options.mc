include "../global/format.mc"
    
type ServerOptions = use Formats in {
    fmt: Format,
    folder: String,
    noOpen: Bool,
    link: String
}
