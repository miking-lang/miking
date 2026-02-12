include "./docgen-options.mc"

-- Parse the list of command-line arguments into an `DocGenOptions` record.
-- Exits with an error if the arguments are invalid.
let parseDocGenOptions : [String] -> DocGenOptions = lam argv.
    recursive let parse : [String] -> DocGenOptions -> DocGenOptions = use Formats in use FormatLanguages in lam args. lam opts.
        switch args
        case ["--help" | "--h"] then usage ()

        case ["--debug"] ++ rest then parse rest { opts with debug = true } 
        case ["--scan-only"] ++ rest then parse rest { opts with scanOnly = true }

        case ["--javascript"] ++ rest then parse rest { opts with fmtLang = Js {} }
        case ["--typescript"] ++ rest then parse rest { opts with fmtLang = Ts {} }

        case ["--output-folder", outputFolder] ++ rest then parse rest { opts with outputFolder = outputFolder }
        case ["--src-folder", srcFolder] ++ rest then parse rest { opts with srcFolder = srcFolder }
        case ["--url-prefix", urlPrefix] ++ rest then parse rest { opts with urlPrefix = urlPrefix }
        case ["--no-open"] ++ rest then parse rest { opts with noOpen = true }
        case ["--no-code"] ++ rest then parse rest { opts with noCode = true }
        case ["--stdlib-loc", loc] ++ rest then parse rest { opts with stdlibFolder = loc }
 
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
           if sysFileExists s then
              parse rest { opts with files = cons s opts.files }
           else
              error (join ["File not found: ", s, "."])
        case [] then opts
        end
    in
    parse (tail argv) docGenOptionsDefault

