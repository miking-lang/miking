-- # Mast Generator Module
--
-- This is the first step of the Miking Doc Gen pipeline.
-- Later in the pipeline, we need the complete Miking compiler AST to fetch
-- types and resolve ambiguity. This module generates the Miking compiler AST,
-- which we call the MAST.
--
-- Generating the MAST from a file is simple: call `parseMCoreFile` with the
-- right options. However, the Miking compiler drops `utests` and `mexpr` in
-- non-entry point files, but we need an MAST of the entire program.
--
-- To address this, we generate a temporary file using the `sys.mc` API,
-- combining all included files so that `utests` and `mexpr` remain. This
-- process has three challenges:
--
-- 1. We must remove all `include`s from this file, otherwise parsing fails
--    since the temporary file is in `/tmp`. This is handled with the
--    `file-opener` API.
-- 2. Miking syntax allows only one `mexpr`. We must process all files and
--    replace `mexpr` with `let #var"x" =`.
-- 3. The parsing step later needs the raw code, and re-opening files would be
--    wasteful. We therefore insert all file contents into the `include-set`.

include "mexpr/boot-parser.mc"
include "mexpr/keywords.mc"
include "ocaml/external.mc"
include "mexpr/type-check.mc"
include "mexpr/ast.mc"
include "mexpr/info.mc"
include "sys.mc"

include "../parsing/include-set.mc"
include "../global/file-opener.mc"
include "./mast.mc"

include "../global/ext-utils.mc"
include "../global/util.mc"
include "../global/logger.mc"
include "mexpr/symbolize.mc"
include "docgen/parsing/token-readers.mc"
include "map.mc"
include "ocaml/external-includes.mc"
include "seq.mc"
include "docgen/parsing/pos.mc"
include "basic-types.mc"
include "string.mc"

-- Builds the AST from a file using the Miking compiler parser.
-- Generates a temporary file, processes includes, preserves utests/mexpr,
-- and type-checks the final AST.
let buildMAstFromFile: Logger -> String -> MAst = lam log. lam file.
    use MExprTypeCheck in
    use MExprSym in
    use BootParser in
    use TokenReader in

    let externalsExclude = mapKeys (externalGetSupportedExternalImpls ()) in
    let parseOpt = {{{{{{{ defaultBootParserParseMCoreFileArg
          with keepUtests = true }
          with allowFree = true }
          with pruneExternalUtests = false }
          with externalsExclude = externalsExclude }
          with pruneExternalUtestsWarning = true }
          with eliminateDeadCode = false }
          with keywords = mexprExtendedKeywords } in
    
    type Arg = { acc: [String], includeSet: IncludeSet ParsingFile } in

    recursive let work : Arg -> String -> Arg = lam arg. lam file.
        log (join ["Assembling ast for the file ", file, "."]);
        match arg with { acc = acc, includeSet = includeSet } in

        let removeMexpr : String -> String = lam s.
            recursive let removeMexpr : String -> String -> String = lam s. lam acc.
                match next s pos0 with { stream = stream, token = token } in
                switch token
                case TokenEof {} then acc
                case TokenWord { content = "mexpr"} then removeMexpr stream (concat (reverse (join ["let #var\"\" = "])) acc)
                case _ then removeMexpr stream (concat (reverse (lit token)) acc)
                end
            in
            removeMexpr s ""
        in        

        match parsingOpenFile file with Some ({ includes = topIncludes, fileText = rest } & f) then
            let includeSet = includeSetReplace includeSet file f in
            let arg = { arg with includeSet = includeSet } in

            let rest = removeMexpr rest in
    
            let arg = foldl (lam arg. lam topInclude.
                
                match includeSetInsert arg.includeSet file topInclude parsingFileEmpty with -- We insert a dummy value because the actual insertion takes place after.
                { includeSet = includeSet, inserted = inserted, path = path } in
                if inserted then work { arg with includeSet = includeSet} path
                else arg
            ) arg topIncludes in
    
            { arg with acc = cons rest arg.acc }
        else error (join ["Found an invalid path while assembling ast: ", file, "."])

    in

    let includeSet = includeSetNew () in

    match work { acc = [], includeSet = includeSet } file with { acc = code } in

    let code = reverse (strJoin "\n" code) in
    let tmpFile = sysTempFileMake () in
    match docgenFileWriteOpen tmpFile with Some wc then
        docgenFileWriteString wc code;
        docgenFileWriteFlush wc;

        log "Parsing final ast";
        let ast = parseMCoreFile parseOpt tmpFile in
        log "Symbolizing final ast";
        let ast = symbolize ast in

        log "Type checking final ast";
        let ast = typeCheckExpr { typcheckEnvDefault with disableConstructorTypes = true} ast in
        ast
    else error "Failed to create temporary file."
