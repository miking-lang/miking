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

  -- Additional keywords
  keywords : [String]
}

let defaultParseOptions = {
  keepUtests = true,
  pruneExternalUtests = false,
  pruneExternalUtestsWarning = true,
  findExternalsExclude = false,
  keywords = []
}

let parseParseMCoreFile : ParseOptions -> String -> Expr = lam opt. lam file.
  use BootParser in
  if opt.pruneExternalUtests then
    let externalsExclude =
      if opt.findExternalsExclude then
        mapKeys (externalGetSupportedExternalImpls ())
      else []
    in
    parseMCoreFile {
      keepUtests = opt.keepUtests,
      pruneExternalUtests = true,
      externalsExclude = externalsExclude,
      pruneExternalUtestsWarning = opt.pruneExternalUtestsWarning,
      keywords = opt.keywords
    } file
  else
    parseMCoreFile {
      keepUtests = opt.keepUtests,
      pruneExternalUtests = false,
      externalsExclude = [],
      pruneExternalUtestsWarning = false,
      keywords = opt.keywords
  } file
