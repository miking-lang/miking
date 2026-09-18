-- # Miking Doc Gen
--
-- This file defines the main execution pipeline for Miking doc gen.
-- It chains together all major stages, starting from parsing and file loading,
-- down to rendering and serving the generated documentation.
--
-- Each stage transforms the `ExecutionContext` in sequence,
-- progressively enriching it until the final output is produced.

-- To generate the stdlib documentation, you can run the following command
-- assuming you want all the files in miking-lang.github.io/docs/stdlib/ and
-- that entry.mc is the entry point of the stdlib.
-- ```
-- mi docgen ~/.local/lib/mcore/stdlib/ --format mdx --out-dir miking-lang.github.io/docs/stdlib --url-prefix "/docs/stdlib/"
-- ```
-- For more details about each option, see options/options.mc

include "./execution-context.mc"
include "docgen/options/docgen-options.mc"
include "basic-types.mc"

let docgen : DocGenOptions -> () = lam opt.
    match execContextNew opt with Some execCtx then
        recursive let process: ExecutionContext -> ExecutionContext =
            lam execCtx.
            let execCtx = gen execCtx in
            let execCtx = parse execCtx in
            let execCtx = name execCtx in        
            let execCtx = render execCtx in
            match execCtxNext execCtx
            with Some newExecCtx then process newExecCtx
            else execCtx
        in

        let execCtx = process execCtx in
        let execCtx = serve execCtx in
        ()
    else ()

