include "../global/objects.mc"
include "./renderers/objects-renderer.mc"
include "../global/util.mc"
include "fileutils.mc"
include "hashmap.mc"
include "../options/docgen-options.mc"
include "../global/format.mc"    
include "docgen/rendering/rendering-options.mc"
include "basic-types.mc"
include "seq.mc"
include "sys.mc"

let preprocess : use Objects in Object -> RenderingOptions -> () = use ObjectsRenderer in lam obj. lam opt.
    type PathMap = HashMap String () in

    recursive let preprocessRec : PathMap -> Object -> PathMap = use Objects in
        lam pathMap. lam obj.

        match obj with ObjInclude { child = Some child } then
            preprocessRec pathMap child
        else
            if objHasUrl obj then
               let path = dirname (join [opt.outDir, objGetMyLocation obj opt]) in
               let map = hmInsert path () pathMap in
               foldl preprocessRec map (objChildren obj)
            else pathMap            
    in

    let pathMap = preprocessRec (hashmapEmpty ()) obj in
    recursive let create = lam arr.
        let batchSize = 1000 in
        match arr with [] then ()
        else
            let arr = if lti (length arr) batchSize then (arr, []) else splitAt arr batchSize in

            let command = concat ["mkdir", "-p", join [opt.outDir, "/", opt.srcFolder]] arr.0 in
            let res = sysRunCommand command "" "." in
            match res.returncode with 0 then create arr.1
            else error "Failed to create output directories during preprocessing." -- We fail here because otherwise we might generate files in the wrong place which could be very annoying for the user.
    in create (hmKeys pathMap)
