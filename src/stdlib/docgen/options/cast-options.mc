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
include "../scanning/scanning-options.mc"
include "../parsing/parsing-options.mc"
include "../server/server-options.mc"
include "../rendering/rendering-options.mc"
include "../naming/naming-options.mc"
include "docgen/global/logger.mc"
include "docgen/naming/name-context.mc"
include "docgen/rendering/rendered-map.mc"
include "docgen/global/format-language.mc"

let getScanningOptions : DocGenOptions -> ScanningOptions = lam opt.
    {
       files = opt.files,
       outDir = opt.outDir,
       stdlibFolder = opt.stdlibFolder,
       scanOnly = opt.scanOnly
    }

let getParsingOptions : Logger -> String -> String -> ParsingOptions =
    lam log. lam basePath. lam longestPrefix.
    {
        log = log,
        basePath = basePath,
        longestPrefix = longestPrefix
    }

let getNamingOption : DocGenOptions -> NamingOptions = lam opt.
    {
        fmt = opt.fmt,
        debug = opt.debug,
        urlPrefix = opt.urlPrefix,
        stdlibFolder = opt.stdlibFolder
    }

-- convert a global `DocGenOptions` record into a `RenderingOptions` record
-- used by the rendering step.
let getRenderingOption : DocGenOptions -> Logger -> NameContext -> RenderedMap -> RenderingOptions =
    use FormatLanguages in lam opt. lam log. lam nameContext. lam renderedMap.
    {
        fmt = opt.fmt,
        stdlibFolder = opt.stdlibFolder,
        outDir = opt.outDir,
        srcFolder = opt.srcFolder,
        urlPrefix = opt.urlPrefix,
        fmtLang = opt.fmtLang,
        nameContext = nameContext,
        log = log,
        noCode = opt.noCode,
        renderedMap = renderedMap
    }

-- Convert a global `DocGenOptions` record and a link string representing the URL of the opening file.
-- into a `ServerOptions` record used by the server.
let getServeOption : DocGenOptions -> String -> ServerOptions  = lam opt. lam link.
    {
        fmt = opt.fmt,
        folder = opt.outDir,
        noOpen = opt.noOpen,
        link = link
    }
