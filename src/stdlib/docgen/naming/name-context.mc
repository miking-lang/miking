include "./langs-namespace.mc"
include "./name-map.mc"
include "./types-namespace.mc"
include "../global/objects.mc"
include "docgen/global/format.mc"
include "seq.mc"
include "string.mc"
include "docgen/global/util.mc"
include "docgen/naming/generic-namespace-set.mc"
include "basic-types.mc"

let buildUrl : use Formats in String -> String -> Format -> Bool -> Bool -> String -> String -> String =
    use Formats in
    lam stdlibFolder. lam urlPrefix. lam fmt. lam hasChildren. lam isStdlib. lam namespace. lam kind.
    let ext = concat "." (formatGetExtension fmt) in
    let prefix = if isStdlib then stdlibFolder  else "" in

    let name = join [namespace, if null kind then "" else concat "-" kind] in

    let name =
        if hasChildren then join [name, "/index", ext]
        else concat name ext
    in

    let link = strJoin "/" [urlPrefix, prefix, name] in
    normalizePath link

type NameMapValue = use Objects in {
    url: String,
    obj: Object
}

type NameMap = NameMap NameMapValue

type NameContext = {
    langNamespaceSet: LangNamespaceSet,
    typeNamespaceSet: TypeNamespaceSet,
    nameMap: NameMap
}

let nameContextEmpty : () -> NameContext = lam. {
    langNamespaceSet = namespaceSetEmpty (),
    typeNamespaceSet = namespaceSetEmpty (),
    nameMap = nameMapEmpty ()
}

let nameContextWithCapacity : Int -> NameContext = lam n. {
    langNamespaceSet = namespaceSetEmpty (),
    typeNamespaceSet = namespaceSetEmpty (),
    nameMap = nameMapWithCapacity n
}

let nameContextFetch : NameContext -> use Objects in Object -> String -> Option NameMapValue =
    use Objects in
    lam ctx. lam obj. lam name.
    let namespace = objNamespace obj in
    nameMapFetch ctx.nameMap name (objId obj) namespace false

let nameContextGetTypeConstructors : use Objects in NameContext -> Object -> Option [Object] =
    lam ctx.
    typeNamespaceGetTypeConstructors ctx.typeNamespaceSet
    
