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

  -- Additional keywords
  keywords : [String]
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
      keywords = opt.keywords
    } file
  else
    parseMCoreFile {
      keepUtests = opt.keepUtests,
      pruneExternalUtests = false,
      externalsExclude = [],
      keywords = opt.keywords
  } file
