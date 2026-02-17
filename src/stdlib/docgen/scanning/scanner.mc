include "../global/file-opener.mc"
include "../global/util.mc"

include "./scanning-options.mc"
include "./docgen-ignore.mc"
include "./scanning-output.mc"

let scan : ScanningOptions -> ScanningOutput =
    lam opt.

    if null opt.files then defaultScanningOutput () else
    let first = normalizePath (join [pwd, "/", head opt.files]) in

    let files =
        foldl (lam files: [String]. lam file: String.
            if isFolder file then
               match folderFetchMcFiles file
               with Some newFiles then concat newFiles files
               else error (join ["Cannot read directory ", file, " (permission denied or not accessible)."])
            else if sysFileExists file then cons file files
            else error (join ["File not found: '", file, "'."])
        ) [] opt.files
    in

    -- Always include string.mc, because we
    -- need a definition for the builtin type
    -- such as Int, Char, and String, so we use
    -- pages of the stdlib string.mc int.mc char.mc,
    -- all included by string.mc.
    let files = cons "string.mc" files in
    
    let normalizeFiles : String -> [String] -> [String] = lam pos.
        map (lam f.
            if strStartsWith "/" f then f
            else
                let stdlibFile = normalizePath (join [stdlibLoc, "/", f]) in
                if sysFileExists stdlibFile then stdlibFile
                else normalizePath (join [pos, "/", f]))
    in

    let files = normalizeFiles pwd files in

    type InputFileSet = HashMap String () in
    type Visited = HashMap String () in
    type Ctx = { visited : Visited, set: InputFileSet } in

    recursive

    let go : Ctx -> [String] -> Ctx =
        lam ctx. lam files.
        foldl (
            lam ctx. lam f.
                if hmMem f ctx.visited then ctx
                else scanFile ctx f
        ) ctx files

    let scanFile : Ctx -> String -> Ctx =
        lam ctx. lam pos.
        let ctx = { ctx with visited = hmInsert pos () ctx.visited } in
        match parsingOpenFile pos with Some { includes = includes } then
            let pos = dirname pos in
            let includes = normalizeFiles pos includes in
            let set = foldl (lam set. lam i. hmRemove i set) ctx.set includes in
            go { ctx with set = set } includes
        else
            error (join ["Failed to open file: '", pos, "'."])
    in                           

    let filesSet = foldl (lam acc. lam f. hmInsert f () acc) (hashmapEmpty ()) files in
    let files = foldl scanFile { set = filesSet, visited = hashmapEmpty () } files in

    let visited = hmKeys files.visited in
    let files = hmKeys files.set in

    let nonStdlib = filter (lam f. not (pathIsInStdlib f)) visited in
    let onlyStdlib = null nonStdlib in

    let commonPrefix = strLongestCommonPrefixArray (if onlyStdlib then visited else nonStdlib) in
    let commonPrefix = dirname commonPrefix in

    let commonPrefixLength = length commonPrefix in
    let stdlibLocLength = length stdlibLoc in
    let stdlibOutputFolder =
        if onlyStdlib then opt.outDir
        else join [opt.outDir, "/", opt.stdlibFolder]
    in

    let originalLength = length files in
    let files = filter (lam f. not (eqString first f)) files in
    let files = if eqi (length files) originalLength then files else concat files [first] in

    let files =
        map (
            lam path.
            let getRelativeOutputFolder =
                lam outDir. lam commonPrefixLength.
                let f = subsequence path commonPrefixLength (length path) in
                let outDir = normalizePath (join [outDir, "/", f]) in
                let outDir = dirname outDir in
                concat outDir "/"
             in

            let outDir = if pathIsInStdlib path then               
               getRelativeOutputFolder stdlibOutputFolder stdlibLocLength
            else
               getRelativeOutputFolder opt.outDir commonPrefixLength
            in

            { path = path, outDir = dirname outDir }
        ) files
    in

    let output = { defaultScanningOutput () with
        inputs = files,
        longestPrefix = commonPrefix,
        onlyStdlib = onlyStdlib
    } in
    let output = ignoreFilesToIgnore output in
    
    (if opt.scanOnly then logScanningOutput output else ());

    output
