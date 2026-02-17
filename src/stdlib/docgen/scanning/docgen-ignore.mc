include "./scanning-output.mc"
include "../global/logger.mc"
include "../global/util.mc"
include "../global/ext-utils.mc"

let docgenIgnorePath = ".docgen-ignore"

let ignoreFilesToIgnore : ScanningOutput -> ScanningOutput =
    lam output.
    match docgenFileReadOpen docgenIgnorePath with Some rc then
        let s = docgenFileReadString rc in
        docgenFileReadClose rc;
        let toIgnore = strSplit "\n" s in
        let toIgnore = map strFullTrim toIgnore in
        let toIgnore = filter (lam f. not (null f)) toIgnore in
        let toIgnore = map (
            lam f.
            let f = pathRemoveHome f in
            let f =
                if pathIsAbsolute f then f
                else pathConcat (pathConcat pwd f) "" -- We make sure the path ends with a '/', otherwise correctness is not respected.
            in
            let f = { path = f, isFolder = isFolder f } in

            f
            ) toIgnore
        in

        let output = foldl
            (lam output. lam file.
                if any (lam candidate. (if candidate.isFolder then strStartsWith else eqString) candidate.path file.path) toIgnore then
                    { output with ignored = cons file output.ignored }
                else
                    { output with inputs = cons file output.inputs }
            )
            { output with inputs = [], ignored = [] }
            output.inputs
        in

        { output with ignored = reverse output.ignored, inputs = reverse output.inputs }
    else
        output


