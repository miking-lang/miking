-- # Step-Specific Options
--
-- Some steps in the documentation pipeline require a set of arguments
-- that are usually a subset of the full `DocGenOptions` type.
-- Instead of passing the entire `DocGenOptions` record, or a large number of parameters,
-- we define helper functions that convert `DocGenOptions` into step-specific option types.
--
-- This file provides basic utilities to cast `DocGenOptions` into
-- `ServerOptions` and `RenderingOptions`.

include "./docgen-options.mc"
include "../server/server-options.mc"
include "../rendering/rendering-options.mc"
include "hashmap.mc"

-- Convert a global `DocGenOptions` record and a link string representing the URL of the opening file.
-- into a `ServerOptions` record used by the server.
let getServeOption : DocGenOptions -> String -> ServerOptions  = lam opt. lam link.
    {
        fmt = opt.fmt,
        folder = opt.outputFolder,
        firstFile = opt.file,
        noOpen = opt.noOpen,
        link = link
    }

-- Convert a global `DocGenOptions` record into a `RenderingOptions` record
-- used by the rendering step.
let getRenderingOption : DocGenOptions -> Logger -> RenderingOptions = use FormatLanguages in lam opt. lam log.
    {
        fmt = opt.fmt,
        noStdlib = opt.noStdlib,
        outputFolder = opt.outputFolder,
        srcFolder = opt.srcFolder,
        urlPrefix = opt.urlPrefix,
        fmtLang = opt.fmtLang,
        letDepth = opt.letDepth,
        nameContext = hashmapEmpty (),
        jsSearchCode = "",
        log = log
    }
