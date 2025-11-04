-- # file-opener.mc
-- This module provides an API to open documentation output
-- files according to the renderIt field in the object.

include "./renderers/objects-renderer.mc"
include "./rendering-options.mc"

include "ext/file-ext.mc"

-- Result of opening a file for writing.
type FileOpenerResult = {
    wc: Option WriteChannel,   -- Optional write channel if the file is open
    write: String -> (),       -- Function to write a string to the file
    path: String               -- Path of the opened file
}


-- Attempts to open the output file for a given object.
let fileOpenerOpen : ObjectTree -> RenderingOptions -> Option FileOpenerResult =
    use ObjectsRenderer in lam tree. lam opt.
    let obj = objTreeObj tree in
    
    if objRenderIt obj then
        let path = concat opt.outputFolder (objLink obj opt) in
         match fileWriteOpen path with Some wc then
             Some {
                 wc = Some wc,
                 write = fileWriteString wc,
                 path = path
             }
         else
             renderingWarn (concat "Failed to open " path); None {}

    else
        Some {
             wc = None {},
             write = lam. (),
             path = ""
         } 
