include "mexpr/boot-parser.mc"
include "ocaml/external.mc"

type ParseOptions = {
  -- Keep utests
  keepUtests : Bool,

  -- Prune external dependet utests
  pruneExternalUtests : Bool,

  -- Exclude pruning of utest for externals with whose dependencies are met on
  -- this system.
  findExternalsExclude : Bool,

  -- Warn if there are pruned utests
  pruneExternalUtestsWarning : Bool,

  -- Run dead code elimination
  eliminateDeadCode : Bool,

  -- Additional keywords
  keywords : [String]
}

let parseParseMCoreFile : ParseOptions -> String -> use Ast in Expr =
  lam opt. lam file.
    use BootParser in
    if opt.pruneExternalUtests then
      let externalsExclude =
        if opt.findExternalsExclude then
          mapKeys (externalGetSupportedExternalImpls ())
        else []
      in
      parseMCoreFile {{{{{{ defaultBootParserParseMCoreFileArg
        with keepUtests = opt.keepUtests }
        with pruneExternalUtests = true }
        with externalsExclude = externalsExclude }
        with pruneExternalUtestsWarning = opt.pruneExternalUtestsWarning }
        with eliminateDeadCode = opt.eliminateDeadCode }
        with keywords = opt.keywords } file
    else
      parseMCoreFile {{{{{{ defaultBootParserParseMCoreFileArg
        with keepUtests = opt.keepUtests }
        with pruneExternalUtests = false }
        with externalsExclude = [] }
        with pruneExternalUtestsWarning = false }
        with eliminateDeadCode = opt.eliminateDeadCode }
        with keywords = opt.keywords } file
