include "./preprocessor.mc"
include "./renderers/main-renderer.mc"
include "./source-code-spliter.mc"
include "./rendering-options.mc"
include "./util.mc"

include "../global/objects.mc"
include "../global/ext-utils.mc"
include "../global/util.mc"
include "../global/logger.mc"
include "../global/format.mc"
include "hashmap.mc"
include "docgen/rendering/renderers/headers/search.mc"
include "docgen/rendering/rendered-map.mc"
include "docgen/rendering/rendering-data.mc"
include "basic-types.mc"
include "seq.mc"
include "ext/file-ext.mc"

type RenderingResult = {
     renderedMap: HashMap String (),
     searchDatas: [SearchDictObj]
}

let render : use Objects in RenderingOptions -> Object -> RenderingResult = use Renderer in
    lam opt. lam obj.
    use Objects in
    
    let log = opt.log in
    
    let searchDatas = objToJsDict opt obj in
    
    preprocess obj opt;
    renderSetup opt;

    log "Beginning of rendering stage.";

    recursive
    let render: RenderedMap -> Object -> [RenderingData] -> { datas: RenderingData, renderedMap: RenderedMap } =
        lam renderedMap. lam obj. lam tests.

        let emptyPreview = lam obj.
            { datas = renderCreateRenderingData obj tests opt, renderedMap = renderedMap }
        in

        objLog obj opt;

        switch obj
        case ObjInclude { child = Some child } then
            let res = render renderedMap child [] in
            { emptyPreview obj with renderedMap = res.renderedMap }
        case ObjInclude { child = None {} } then emptyPreview obj
        case _ then
            if objIsArtificial obj then emptyPreview obj else

            let loc = objGetMyLocation obj opt in
            match renderedMapInsert renderedMap obj loc with
            { renderedMap = renderedMap, prune = prune } in
            
            if prune then
                { datas = renderCreateRenderingData obj tests opt, renderedMap = renderedMap }
            else

            let f =
                if objHasUrl obj then
                    let path = concat opt.outDir (objGetMyLocation obj opt) in
                    match docgenFileWriteOpen path with Some wc then
                        Some {
                            wc = Some wc,
                            write = docgenFileWriteString wc,
                            path = path
                        }
                    else
                        renderingWarn (join ["Failed to open output file ", path, " during rendering"]); None {}
                else
                    Some {
                         wc = None {},
                         write = lam. (),
                         path = ""
                     } 
            in

            match f with Some { wc = wc, write = write, path = path } then
                (match path with "" then () else log (concat "Rendering file " path));

                type Acc = { tests: [RenderingData], children: [RenderingData], renderedMap: RenderedMap } in
                let acc = foldl
                    (lam acc: Acc. lam child.
                        match child with ObjUtest {} then
                            match render acc.renderedMap child [] with {renderedMap = renderedMap, datas = datas} in
                            {
                                children = cons datas acc.children,
                                tests = cons datas acc.tests,
                                renderedMap = renderedMap
                            }
                        else
                            match
                                if objHasTests child then render acc.renderedMap child acc.tests
                                else render acc.renderedMap child []
                            with { datas = datas, renderedMap = renderedMap } in
                            { children = cons datas acc.children, tests = [], renderedMap = renderedMap }
                    ) { tests = [], children = [], renderedMap = renderedMap } (reverse (objChildren obj))
                in

                let renderedMap = acc.renderedMap in
                let children = acc.children in

                -- Build source code for the current node
                let data = renderCreateRenderingData obj tests opt in

                (if objHasUrl obj then                

                    write (renderHeader obj opt);
                    write (renderObjTitle 1 obj opt);
                    write (renderTopPageDoc data opt);

                    let children = removeDoubleNames opt children in

                    -- Order objects into a set
                    let set = buildSet children in

                     -- Display includes
                    let displayIncludes = lam title. lam arr.
                        let title = match arr with [] then "" else match title with "" then "" else
                                renderSectionTitle title opt in
                        write title;
                        write (renderLinkList arr opt)
                    in

                    -- Display types and constructors
                    let displayDefault = lam title. lam arr.
                        let opt = { opt with noCode = true } in
                        let title = match arr with [] then "" else match title with "" then "" else
                                renderSectionTitle title opt in
                        write title;
                        iter (lam u. write (renderDocBloc u true opt)) arr
                    in

                    iter (lam a. displayIncludes a.0 a.1)
                         [("Includes", set.sInclude),
                         ("Stdlib Includes", set.sLibInclude)];
                    iter (lam a. displayDefault a.0 a.1)
                        [("Types", set.sType),
                        ("Constructors", set.sCon),
                        ("Languages", set.sLang),
                        ("Syntaxes", set.sSyn),
                        ("Variables", set.sLet),
                        ("Semantics", set.sSem)];

                    -- Push the footer of the page
                    write (renderFooter obj opt);

                    (match wc with Some wc then fileWriteClose wc else ())
                else ());

                { datas = data, renderedMap = renderedMap }
            else emptyPreview obj
        end
    in

    match render opt.renderedMap obj [] with { renderedMap = renderedMap } in
    
    {
         renderedMap = renderedMap,
         searchDatas = searchDatas
    }
