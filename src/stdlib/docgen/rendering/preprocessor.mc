-- # Preprocess step: create output directories
--
-- This module implements the preprocessing step:
-- - Walks the ObjectTree
-- - Computes all the output directories needed to generate doc files
-- - Creates them using `mkdir -p`
--
-- It builds a PathMap and runs a system command at the end.
-- The preprocessor have to use the NameContext too generate all the folders correctly.

include "../extracting/objects.mc"
include "./renderers/objects-renderer.mc"
include "../global/util.mc"
include "fileutils.mc"
include "hashmap.mc"
include "../options/docgen-options.mc"
include "../global/format.mc"    

let preprocess : ObjectTree -> RenderingOptions -> () = use ObjectsRenderer in lam obj. lam opt.
    -- Map of all output paths (acts as a Set)
    type PathMap = HashMap String () in
    -- Recursively visit the ObjectTree and collect paths
    recursive let preprocessRec : PathMap -> ObjectTree -> PathMap = use ObjectKinds in
        lam pathMap. lam obj.
        let inner = objTreeObj obj in
        let nameContext =
            match objNameIfHas inner with Some name then
             hmInsert name (objGetPureLink inner opt) opt.nameContext
            else opt.nameContext
        in
        
        let opt = { opt with nameContext = nameContext } in
        switch obj
        case ObjectNode { obj = { kind = ObjInclude {} } & obj, children = [ p ] } then
            if and (objIsStdlib obj) opt.noStdlib then pathMap else
                preprocessRec pathMap p
        case ObjectNode { obj = { kind = ObjRecursiveBloc {} }, children = children } then
            foldl preprocessRec pathMap children
        case ObjectNode { obj = obj, children = children } then
            let path = dirname (join [opt.outputFolder, objLink obj opt]) in
            let map = hmInsert path () pathMap in
            if objRenderIt obj then
                foldl preprocessRec map children
            else pathMap            
        case _ then pathMap
        end

    in
    let pathMap = preprocessRec (hashmapEmpty ()) obj in
    recursive let create = lam arr.
        let batchSize = 1000 in
        match arr with [] then ()
        else
            let arr = if lti (length arr) batchSize then (arr, []) else splitAt arr batchSize in
            let command = concat ["mkdir", "-p", join [opt.outputFolder, "/", opt.srcFolder]] arr.0 in
            let res = sysRunCommand command "" "." in
            match res.returncode with 0 then create arr.1 else error "Failed to create folders during preprocessing"
    in create (hmKeys pathMap)
