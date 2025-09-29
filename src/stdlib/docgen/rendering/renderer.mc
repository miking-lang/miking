-- # Global Rendering Pipeline
--
-- This module defines the entry point for rendering an object tree into formatted output.
-- It traverses the parsed object structure, organizes its children,
-- reconstructs the source code, and writes the formatted documentation files to disk.
--
-- After the extraction phase (and the labeling phase), we obtain an `Object`.
-- From this object, generating documentation pages becomes straightforward.
-- RenderingOptions contains very useful informations, such as nameContext. See rendering-options.mc
-- for more informations.
--
-- Here’s how the renderer works:
--
-- - To produce the correct output format, we define a rendering interface in `renderer-interface.mc`,
--   which is implemented by each specific renderer. Then, we unify all language renderers inside the main `Renderer`,
--   allowing us to abstract away the output format and work uniformly.
--
-- - Rendering the children on an object’s page is relatively simple.
--   We can distinguish each child’s type via its `kind` field and display them in the desired order.
--   Additionally, linking to a child is easy thanks to its `namespace`, which provides a unique and structured identifier.
--
-- - Reconstructing the source code is by far the most challenging part.
--   We don’t just want to dump a raw string into the documentation;
--   we want syntax highlighting, block-by-block collapsibility (folding), and contextual formatting.
--   Importantly, this reconstruction must **re-use data from the children**:
--   otherwise, we would have to recompute syntax highlighting and toggle button placement from scratch,
--   which is clearly not an acceptable solution. For more information, see `source-code-spliter.mc`
--
-- NOTE: As we do not want a recursive block to be considered as regular children, we need to extract its children,
-- render them, and inject them into the node’s children list.
-- For example:
-- let x =
--   recursive
--   let y = 2
--   in 3
-- Here we want `y` to be considered a direct child of `x`, not the child of a recursive block. But we still need to compute
-- the RenderingData of the recursive block to be able to build the source code correctly. By rendering the recursive block we
-- lose information about children, as we do not keep grandchild information, so the only solution that preserves the architecture
-- is to unwrap all the recursive blocks and render them a second time. As Recursive is considered as a never object by the file-opener, meaning all its children will not have documentation page, the writing part only occurs once.
            

include "./preprocessor.mc"
include "./renderers/main-renderer.mc"
include "./source-code-reconstruction.mc"
include "./rendering-options.mc"
include "./files-opener.mc"
include "./util.mc"

include "../extracting/objects.mc"

include "../global/util.mc"
include "../global/logger.mc"
include "../global/format.mc"

-- ## render
--
-- Entrypoint to rendering. This function traverses the entire `ObjectTree` and writes
-- structured documentation for each object node.
--
-- ### Behavior:
-- - Preprocesses the object tree.
-- - Defines a recursive `render` function that:
--     - Preprocesses children: recursive unwrapping, test injection.
--     - Recursively renders them.
--     - Organizes them by type.
--     - Writes formatted output to file.
--     - Returns `RenderingData` and updated `RenderingOptions` for each node.
let render : RenderingOptions -> ObjectTree -> () = use Renderer in
    lam opt. lam obj.
    
    let log = opt.log in
    let opt = { opt with jsSearchCode = searchJs (objToJsDict opt obj) } in
    
    preprocess obj opt;
    renderSetup obj opt;

    log "Beginning of rendering stage.";
    recursive
    let render: RenderingOptions -> ObjectTree -> (RenderingData, RenderingOptions) = lam oldOpt. lam objTree.  -- # Global Rendering Pipeline

        -- Base case for objects that do not require a documentation page.
        -- For objects such as Use or Include we just want to return source code data.
        let emptyPreview = lam obj.
            let trees = reconstructSourceCode (objSourceCode obj) [] in
            renderTreeSourceCode trees obj opt
        in

        objLog (objTreeObj objTree) oldOpt;

        switch objTree
        case ObjectNode { obj = { kind = ObjUse {}} & obj, children = children } then (emptyPreview obj, oldOpt)
        case ObjectNode { obj = { kind = ObjInclude {} } & obj, children = [ p ] } then
            if and (objIsStdlib obj) oldOpt.noStdlib then (emptyPreview obj, oldOpt) else
            let res = render oldOpt p in
            (emptyPreview obj, res.1)
        case ObjectNode { obj = { kind = ObjInclude {} } & obj, children = [] } then (emptyPreview obj, oldOpt)
        case ObjectNode { obj = { kind = ObjInclude {} } & obj } then
             renderingWarn "Include with more than one child detected"; (emptyPreview obj, oldOpt)
        case ObjectNode { obj = obj, children = children } then

            match fileOpenerOpen objTree oldOpt with Some { wc = wc, write = write, path = path } then
                (match path with "" then () else log (concat "Rendering file " path));
                -- Push header of the output file
                write (renderHeader obj oldOpt);

                -- Unwrapping the recursive blocks and rendering all the children.
                let recDatas: [[RenderingData]] = foldl (lam buffer. lam tree.
                    let obj = objTreeObj tree in
                    match obj.kind with ObjRecursiveBloc {} then
                        let datas = map (lam child. (render opt child).0) (objTreeChildren tree) in
                        cons datas buffer
                    else buffer) [] children
                in

                -- Recursive calls: render all children and transmit the name-context through the fold.
                match foldl (lam arg. lam child.
                      let obj = objTreeObj child in
                      let nameContext =
                          match objNameIfHas obj with Some name then
                           hmInsert name (objGetPureLink obj arg.opt) arg.opt.nameContext
                          else arg.opt.nameContext
                      in
                      let opt = { arg.opt with nameContext = nameContext } in
                      match render opt child with (child, opt) in
                      { opt = opt, children = cons child arg.children }
                      ) { children = [], opt = oldOpt } children with { children = children, opt = opt }
                in
                let children = reverse children in

                -- Inject test data into children
                let children = injectTests children in

                -- Build source code for the current node
                let trees = reconstructSourceCode (objSourceCode obj) children in

                -- From the source code tree, build the RenderingData
                let data = renderTreeSourceCode trees obj opt in
    
                write (renderObjTitle 1 data.obj opt);
                write (renderTopPageDoc data opt);

                let children = removeDoubleNames children in

                -- Order objects into a set
                let set = buildSet children recDatas in
    
                 -- Display uses and includes
                let displayUseInclude = lam title. lam arr.
                    let title = match arr with [] then "" else match title with "" then "" else
                            renderSectionTitle title opt in
                    write title;
                    write (renderLinkList arr opt)
                in
    
                -- Display types and constructors
                let displayDefault = lam title. lam arr.
                    let title = match arr with [] then "" else match title with "" then "" else
                            renderSectionTitle title opt in
                    write title;
                    iter (lam u. write (renderDocBloc u opt)) arr
                in
    
                iter (lam a. displayUseInclude a.0 a.1) [("Using", set.sUse), ("Includes", set.sInclude), ("Stdlib Includes", if opt.noStdlib then [] else set.sLibInclude)];
                iter (lam a. displayDefault a.0 a.1)
                    [("Types", set.sType), ("Constructors", set.sCon), ("Languages", set.sLang),
                    ("Syntaxes", set.sSyn), ("Variables", set.sLet), ("Semantics", set.sSem), ("Mexpr", set.sMexpr)];

                -- Push the footer of the page
                write (renderFooter obj opt);

                (match wc with Some wc then fileWriteClose wc else ());

                -- Only preserving name-context embedded in options if accepted in the node.
                (data, if objPreserveNameCtx obj then opt else oldOpt)
            else (emptyPreview obj, oldOpt)
        end
    in
    let res = render opt obj in ()
