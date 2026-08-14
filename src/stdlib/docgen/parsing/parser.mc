include "./parsing-options.mc"
include "./ast-stream.mc"
include "./doc-parser.mc"
include "./lang-parser.mc"

include "../global/util.mc"
include "../global/file-opener.mc"
include "../global/namespace-utils.mc"
include "../global/source-code.mc"
include "../options/docgen-options.mc"
include "../global/objects.mc"

include "seq.mc"
include "hashmap.mc"
include "fileutils.mc"
include "hashmap.mc"
include "sys.mc"
include "docgen/mast-gen/mast.mc"
include "docgen/parsing/token-readers.mc"
include "docgen/parsing/include-set.mc"
include "docgen/parsing/pos.mc"
include "basic-types.mc"
include "docgen/parsing/utils.mc"
include "mexpr/info.mc"
include "docgen/global/logger.mc"
include "docgen/global/ext-utils.mc"
include "option.mc"
include "./pos.mc"

let parse : use Objects in ParsingOptions -> MAst -> Object =
    use Objects in
    use TokenReader in
    use AstStream in

    lam opt. lam ast.

    match opt with { log = log, basePath = basePath, longestPrefix = longestPrefix } in

    let openers =
        foldl
        (lam m. lam k. hmInsert k () m)
            (hashmapEmpty ())
        ["let", "lang", "type", "syn", "sem", "con", "mexpr", "use", "utest", "recursive"] in

    type ParseRes = { includeSet: IncludeSet (), astStream: AstStreamContext, obj: Object, newPos: Pos } in
    type ParseFileRes = { astStream: AstStreamContext, children: [Object], newPos: Pos } in

    recursive
    -- This function is parsing the text of the file without any includes
    let parseFile : AstStreamContext -> Pos -> String -> String -> ParseFileRes =
        lam astStream. lam pos. lam namespace. lam content.
        let isStdlib = pathIsInStdlib namespace in

        type CollectRes = { obj: Option Object, rest: String, astStream: AstStreamContext, newPos: Pos } in
        let collectOneNode : String -> CollectRes =
            lam content.
            let default = { obj = None {}, astStream = astStream, rest = "", newPos = pos } in

            let objWithDoc =
                lam obj. lam doc.
                match parseDoc doc with Some doc then objWithDoc obj doc else obj
            in

            let assignObject =
                lam obj. lam namespace.
                let obj = objWithIsStdlib obj isStdlib in
                let obj = objWithNamespace obj namespace in
                let obj = objWithPrefix obj longestPrefix in
                obj
            in

            match gotoFirstWord content [] pos with Some { doc = doc, pos = pos, rest = rest, isLang = isLang } then
                if isLang then
                    match extractName rest with Some name in
                    log (join ["Parsing lang ", name, "."]);
                    match typeStreamCreateLangDatabase astStream name with { database = database, ctx = astStream} in
                    match parseLang rest pos database longestPrefix isStdlib namespace with { obj = obj, stream = rest, newPos = newPos } in

                    let namespace = namespaceAdd namespace (objName obj) in
                    let obj = assignObject obj namespace in

                    { obj = Some obj, astStream = astStream, rest = rest, newPos = newPos }
                else match typeStreamNext astStream with Some {
                   ctx = astStream,
                   name = name,
                   info = info,
                   obj = obj
                } then
                    let namespace = namespaceAdd namespace name in
                    let lastPos = strGetLastPos rest pos in

                    let obj = assignObject obj namespace in
                    let obj = objWithName obj name in
                    let obj = objWithDoc obj doc in

                    let info = match info with Info {} then info else
                        Info { filename = "", row1 = pos.y, col1 = pos.x, row2 = lastPos.y, col2 = lastPos.x }
                    in

                    match info with Info { row1 = row1, col1 = col1, row2 = row2, col2 = col2 } in
                    let p1 = getPos col1 row1 in
                    let p2 = getPos col2 row2 in
                    let p2 = correctSpanning rest p1 p2 in

                    match computeObjectSpanning rest pos p1 p2
                    with { code = code, rest = rest, newPos = newPos } in

                    let obj = objWithDoc obj doc in
                    let code = strToSourceCode code in
                    let obj = objWithSourceCode obj code in
                    { obj = Some obj, astStream = astStream, rest = rest, newPos = newPos }
                else
                    parsingWarn (join ["AstStream ended unexpectedly while parsing. Current position: ", namespace, "."]);
                    default
            else
                let lastPos = strGetLastPos content pos in
                { default with newPos = lastPos } -- End of the current file



        in

        match collectOneNode content with { obj = obj, astStream = astStream, rest = rest, newPos = newPos } in

        match obj with Some obj then
             let res = parseFile astStream newPos namespace rest in
             if null (objName obj) then res -- Mexpr filtering.
             else { res with children = cons obj res.children }
        else { children = [], astStream = astStream, newPos = newPos }

    -- Here we parse the include header of the file, jump in all the includes before processing the actual code.
    let parse: IncludeSet () -> AstStreamContext -> Pos -> String -> ParseRes =
        lam includeSet. lam astStream. lam pos. lam loc.

        let fileIsStdlib = pathIsInStdlib loc in

        match parsingOpenFile loc with
        Some { headerTokens = headerTokens } then

        let fileContent = match docgenFileReadOpen loc with Some rc then
            let s = docgenFileReadString rc in
            docgenFileReadClose rc;
            s
        else
            parsingWarn (join ["Failed to open file: ", loc, "."]);
            ""
        in

        let tokens = lex fileContent pos0 in
        let tokens = map (lam t. t.0) tokens in

        let getProgName : String -> String =
            lam loc.
            optionGetOrElse
                (lam. parsingWarn "Failed to determine namespace from file path."; "")
                (namespaceLast loc)
        in
        let progName = getProgName loc in
        let progSourceCode = tokensToSourceCode tokens in
        let progDoc = optionGetOr (objDefaultDoc ()) (parseProgramDoc fileContent) in

        let progObj = ObjProgram { children = [], datas = objDefaultDatas () } in
        let progObj = objWithName progObj progName in

        let progObj = objWithIsStdlib progObj fileIsStdlib in
        let progObj = objWithDoc progObj progDoc in
        let progObj = objWithNamespace progObj loc in
        let progObj = objWithPrefix progObj longestPrefix in
        let progObj = objWithSourceCode progObj progSourceCode in

        let progNamespace = loc in

        let headerDocTree = foldl (lam arg: ParseRes. lam token.
            match arg with { includeSet = includeSet, obj = obj, astStream = astStream } in
            match token with { token = token, pos = pos } in

            let go : ParseRes -> Object -> ParseRes =
                lam arg. lam child.
                { arg with obj = objAddChild obj child }
            in

            match token with TokenInclude { content = content } then
                match includeSetInsert includeSet loc content () with
                { includeSet = includeSet, inserted = inserted, path = path } in

                let insertResult = if inserted then
                    match parse includeSet astStream pos path with
                    { includeSet = includeSet, obj = obj, astStream = astStream, newPos = newPos } in
                    ({ arg with includeSet = includeSet, astStream = astStream, newPos = newPos }, Some obj)
                else
                    (arg, None {}) in

                match insertResult with (arg, obj) in
                let child = ObjInclude { datas = objDefaultDatas (), pathInFile = content, child = obj } in
                let child = objWithIsStdlib child fileIsStdlib in
                let child = objWithNamespace child progNamespace in
                let child = objWithPrefix child longestPrefix in
                let child = objWithName child (getProgName path) in

                go arg child
            else
                arg
            ) { includeSet = includeSet, astStream = astStream, obj = progObj, newPos = pos } headerTokens
        in

        match headerDocTree with { includeSet = includeSet, astStream = astStream, obj = obj, newPos = newPos } in
        log (concat "Beginning of parsing stage on " loc);

        match parseFile astStream newPos progNamespace fileContent
            with { children = children, astStream = astStream, newPos = newPos }
        in

        let obj = objAddChildren obj (reverse children) in
        let obj = objReverseChildren obj in

        { includeSet = includeSet, astStream = astStream, obj = obj, newPos = newPos }
        else
            error (join ["Invalid file path encountered during parsing: ", loc, "."])
    in

    match goHere pwd basePath with { path = basePos } in

    let includeSet = includeSetNew () in

    match includeSetInsert includeSet "." basePath () with { includeSet = includeSet } in

    match parse includeSet (buildAstStream ast) pos0 basePath with { includeSet = includeSet, obj = obj } in

    log "Parsing is over.";
    obj
