include "arg.mc"
include "basic-types.mc"
include "options-config.mc"
include "options-type.mc"
include "docgen/options/docgen-options.mc"
include "docgen/global/format-language.mc"
include "docgen/global/format.mc"
include "assoc.mc"

let docGenOptionsConfig : ParseConfig Options = concat optionsConfig [

  ([("--debug", "", "")],
    "Enable all debug modes",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with debug = true}}),

  ([("--scan-only", "", "")],
    "Only process the scan of the project and print it",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with scanOnly = true}}),

  ([("--no-open", "", "")],
    "Do not open the result in a web browser",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with noOpen = true}}),

  ([("--no-code", "", "")],
    "If true, implementations will not appears on the output",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with noCode = true}}),

  ([("--javascript", "", "")],
    "Use JavaScript for the React components",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with fmtLang = use FormatLanguages in Js {}}}),

  ([("--typescript", "", "")],
    "Use TypeScript for the React components",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with fmtLang = use FormatLanguages in Ts {}}}),

  ([("--out-dir", " ", "<name>")],
    "Set the output folder",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with outDir = p.str}}),

  ([("--src-folder", " ", "<name>")],
    "Destination folder for src files relative to outputFolder",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with srcFolder = p.str}}),

  ([("--url-prefix", " ", "<prefix>")],
    "Prefix for all generated URLs",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with urlPrefix = p.str}}),

  ([("--stdlib-loc", " ", "<loc>")],
    "Name of the folder in which we should store stdlib files",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with stdlibFolder = p.str}}),

  ([("--format", " ", "<html|md|mdx>")],
    "Choose output format",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      switch use Formats in formatFromStr p.str
      case Some fmt then {o with docgenOptions = {d with fmt = fmt}}
      case None {} then
        modref p.fail (Some (ParseTypeGeneric ("Unknown format", p.str)));
        o
      end)
]
