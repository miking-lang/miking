-- # Server Entrypoint
--
-- This module wires server options to the Python static server used for previewing
-- generated documentation. It decides what to do based on the selected output format.

include "./server-options.mc"
include "./python-server.mc"
include "./server-options.mc"
include "../options/cast-options.mc"

-- ## startServer
--
-- Starts the preview server or prints where the output was generated, depending on `opt.fmt`.
-- If `opt.noOpen` is true, it performs no action.
let startServer : ServerOptions -> () = use Formats in lam opt.
    if opt.noOpen then () else
       switch opt.fmt
       case Md {} then pythonServerStart true opt    -- Serve Markdown with MD-aware flags
       case Html {} then pythonServerStart false opt -- Serve static HTML
       case Mdx {} then printLn (join ["Mdx generated in ", opt.folder, "."]) -- MDX not served here
       end
