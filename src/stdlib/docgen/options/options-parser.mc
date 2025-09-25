include "./docgen-options.mc"

-- ## parseDocGenOptions
-- Parse the list of command-line arguments into an `DocGenOptions` record.
-- Exits with an error if the arguments are invalid.
let parseDocGenOptions : [String] -> DocGenOptions = lam argv.
    recursive let parse : [String] -> DocGenOptions -> DocGenOptions = use Formats in use FormatLanguages in lam args. lam opts.
        switch args
        case ["--help" | "--h"] then usage ()

        case ["--debug"] ++ rest then parse rest { opts with debug = true } 
        case ["--no-warn"] ++ rest then parse rest { opts with noWarn = true }

        case ["--javascript"] ++ rest then parse rest { opts with fmtLang = Js {} }
        case ["--typescript"] ++ rest then parse rest { opts with fmtLang = Ts {} }

        case ["--output-folder", outputFolder] ++ rest then parse rest { opts with outputFolder = outputFolder }
        case ["--src-folder", srcFolder] ++ rest then parse rest { opts with srcFolder = srcFolder }
        case ["--url-prefix", urlPrefix] ++ rest then parse rest { opts with urlPrefix = urlPrefix }
        case ["--no-open"] ++ rest then parse rest { opts with noOpen = true }
 
        case ["--depth", letDepth] ++ rest then
            match letDepth with "none" then
                parse rest { opts with letDepth = None {} }
            else if stringIsInt letDepth then
                parse rest { opts with letDepth = Some (string2int letDepth) }
            else usage ()

        case ["--format", fmt] ++ rest then
            match formatFromStr fmt with Some fmt then
                parse rest { opts with fmt = fmt }
            else usage ()

        case [s] ++ rest then
            if eqString opts.file "" then
               if sysFileExists s then
                  parse rest { opts with file = s }
               else
                  error (join ["While parsing options: file", s, " does not exist."])
            else usage ()

        case [] then opts
        end
    in
    parse (tail argv) docGenOptionsDefault

