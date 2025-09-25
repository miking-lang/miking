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
-- ./mi-doc-gen entry.mc --format mdx --output-folder miking-lang.github.io/docs/stdlib --url-prefix "/docs/stdlib" --depth 0
-- ```
-- For more details about each option, see options/options.mc

include "./execution-context.mc"

let docgen : DocGenOptions -> () = lam opt.
    let execCtx = execContextNew opt in
    let execCtx = gen execCtx in
    let execCtx = parse execCtx in
    let execCtx = extract execCtx in
    let execCtx = label execCtx in
    let execCtx = render execCtx in
    let execCtx = serve execCtx in
    ()


