include "common.mc"
include "string.mc"
include "seq.mc"

type FileToProcess = { path: String, outDir: String }

type ScanningOutput = {
    inputs: [FileToProcess],
    ignored: [FileToProcess],
    longestPrefix: String,
    onlyStdlib: Bool
}

let defaultScanningOutput : () -> ScanningOutput = lam. {
    inputs = [],
    ignored = [],
    longestPrefix = "",
    onlyStdlib = false
}


let logScanningOutput : ScanningOutput -> () =
    lam output.
    printLn (join [
        "Docgen will process the following ",
        int2string (length output.inputs),
        " files:"
    ]);
    iter (lam f. printLn f.path) output.inputs;
    (if null output.ignored then
        printLn "\nIf you want to ignore some of these files, you can create a .docgen-ignore file."
    else
        printLn "\nThe following files will be ignored as requested:");
    iter (lam f. printLn f.path) output.ignored;
    ()
