-- This file defines all the utils function using ext features.

include "./logger.mc"
include "./objects.mc"
include "ext/file-ext.mc"
include "string.mc"
include "basic-types.mc"
include "seq.mc"

let docgenFileReadOpen = fileReadOpen

let docgenFileWriteOpen = fileWriteOpen

let docgenFileWriteString = fileWriteString

let docgenFileWriteFlush = fileWriteFlush

let docgenFileReadString = fileReadString

let docgenFileReadClose = fileReadClose

let docgenFileWriteClose = fileWriteClose

let readOrNever : String -> String = lam fileName.
    match fileReadOpen fileName with Some rc then
        let s = fileReadString rc in
        fileReadClose rc;
        s
    else
        error (join ["Failed to read a file ", fileName, " does not exist."])


let renderFileOrWarn : String -> String -> () = lam path. lam content.
    match fileWriteOpen path with Some wc then
          fileWriteString wc content;
          fileWriteClose wc
    else
          warn (join ["Failed to create file: ", path, "."])
