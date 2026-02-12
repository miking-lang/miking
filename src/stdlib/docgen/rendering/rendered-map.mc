include "hashmap.mc"

include "../global/objects.mc"

type RenderedMap = HashMap String ()

let renderedMapEmpty : () -> RenderedMap = hashmapEmpty

let renderedMapInsert : RenderedMap -> use Objects in Object -> String -> { renderedMap: RenderedMap, prune: Bool } =
    use Objects in
    lam renderedMap. lam obj. lam loc.
 
    let isProg = match obj with ObjProgram {} then true else false in

    let prune =
        if isProg then hmMem loc renderedMap
        else false
    in

    let renderedMap = if isProg then hmInsert loc () renderedMap else renderedMap in

    { prune = prune, renderedMap = renderedMap }
