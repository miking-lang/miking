include "options-config.mc"
include "options-type.mc"
include "docgen/options/docgen-options.mc"
include "assoc.mc"

let docGenOptionsConfig : ParseConfig Options = concat optionsConfig [

  ([("--debug", "", "")],
    "Enable debug mode",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with debug = true}}),

  ([("--no-warn", "", "")],
    "Suppress warnings",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with noWarn = true}}),

  ([("--javascript", "", "")],
    "Use JavaScript as the formatting language",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with fmtLang = use FormatLanguages in Js {}}}),

  ([("--typescript", "", "")],
    "Use TypeScript as the formatting language",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with fmtLang = use FormatLanguages in Ts {}}}),

  ([("--output-folder", " ", "<path>")],
    "Set the output folder for generated files",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with outputFolder = p.str}}),

  ([("--src-folder", " ", "<path>")],
    "Set the output folder for shared js files",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with srcFolder = p.str}}),


  ([("--url-prefix", " ", "<prefix>")],
    "Set the URL prefix for links",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with urlPrefix = p.str}}),

  ([("--no-open", "", "")],
    "Do not open the generated documentation automatically",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      {o with docgenOptions = {d with noOpen = true}}),

  ([("--depth", " ", "<n|none>")],
    "Set the let-binding expansion depth (integer or 'none')",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let d: DocGenOptions = o.docgenOptions in
      if eqString p.str "none" then
        {o with docgenOptions = {d with letDepth = None {}}}
      else if stringIsInt p.str then
        {o with docgenOptions = {d with letDepth = Some (string2int p.str)}}
      else (
        modref p.fail (Some (ParseTypeGeneric ("Invalid depth", p.str)));
        o
      )),

  ([("--format", " ", "<fmt>")],
    "Output format (e.g. html, md).",
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
