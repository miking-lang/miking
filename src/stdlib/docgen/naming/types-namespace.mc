include "./generic-namespace-set.mc"
include "../global/util.mc"
include "../global/objects.mc"
include "docgen/global/source-code.mc"
include "basic-types.mc"
include "docgen/global/logger.mc"
include "seq.mc"
include "string.mc"

type TypeNamespace = use Objects in  {
    typeObj: Object,
    constructors: [Object]
}

type TypeNamespaceSet = NamespaceSet TypeNamespace

let typeNamespaceInsertNewType : TypeNamespaceSet -> use Objects in Object -> TypeNamespaceSet =
    lam set. lam obj.
    use Objects in 
    let obj = objWithSourceCode obj (sourceCodeEmpty ()) in
    namespaceSetInsert set (objName obj) { typeObj = obj, constructors = [] }

let typeNamespaceInsertNewCon : TypeNamespaceSet -> use Objects in Object -> TypeNamespaceSet =
    use Objects in
    lam set. lam obj.
    let obj = objWithSourceCode obj (sourceCodeEmpty ()) in

    match obj with ObjCon { parentType = parentType } then
        match namespaceSetGetByName set parentType with Some typedef then
            let typedef = { typedef with constructors = concat typedef.constructors [obj] } in
            namespaceSetUpdate set (objName typedef.typeObj) typedef
        else
            namingWarn (join ["Type ", parentType, " is not registered in the type namespace."]); set
    else namingWarn "Invalid object passed to typeNamespaceInsertNewCon (expected constructor)."; set

let typeNamespaceGetTypeConstructors : use Objects in TypeNamespaceSet -> Object -> Option [Object] =
    use Objects in
    lam set. lam obj.
    match obj with ObjType {} then
    let name = objName obj in
    match hmLookup name set.nameMap with Some ids then
        findMap (
            lam id.
            match namespaceSetGetById set id with Some typedef then
                if eqi (objId obj) (objId typedef.typeObj) then
                     Some typedef.constructors
                else None {}
            else namingWarn (join ["Failed to retrieve type namespace entry with id ", int2string id, "."]); None {}
        ) ids
    else namingWarn (join ["Failed to retrieve constructors for type ", name, "."]); None {}
    else namingWarn "typeNamespaceGetTypeConstructors expects a type object."; None {}
