-- # ObjectKinds and Object helpers
--
-- This module defines:
-- - `ObjectKind`: kinds of program elements (let, type, lang, sem, …)
-- - `Object`: carries name, namespace, doc, kind, source code, prefix, stdlib flag
-- - `ObjectTree`: a simple tree wrapper for grouping objects
--
-- Used in doc generation and object representation.

include "../global/util.mc"
include "./source-code-builder.mc"
include "util.mc"

include "mexpr/ast.mc"

-- The ObjectKinds language augments kinds with extra info per block type.
-- For blocks involving types, we reuse stdlib types from `mexpr/ast.mc` and their utilities.
lang ObjectKinds = MExprAst

    -- All possible object kinds
    syn ObjectKind = 
    | ObjProgram {}
    | ObjInclude { pathInFile: String }
    | ObjLet { rec : Bool, args : [String], ty: Option Type }
    | ObjLang { parents : [String] }
    | ObjType { t: Option String }
    | ObjUse {}
    | ObjSem { langName: String, variants: [String], ty: Option Type } -- Variants are the names of each alternative.
    | ObjSyn { langName: String, variants: [String] }
    | ObjCon { t: String }
    | ObjMexpr {}
    | ObjUtest {}
    | ObjRecursiveBloc {}

    -- Converts an ObjectKind to a readable string (for logs/debugging).
    sem objKindToString : ObjectKind -> String
    sem objKindToString =
    | ObjLet { rec = rec, args = args, ty = ty} -> join ["ObjLet, recursive: ", bool2string rec, ", args: [", strJoin ", " args, "]"]
    | ObjLang { parents = parents } -> join ["ObjLang, parents: ", strJoin ", " parents]
    | ObjType { t = t } -> join ["ObjType", match t with Some t then concat ", " t else ""]
    | ObjUse {} -> "ObjUse"
    | ObjSem { langName =  langName } ->  join ["ObjSem, langName = ", langName]
    | ObjSyn { langName = langName } -> join ["ObjSyn, langName = ", langName]
    | ObjCon { t = t } -> join ["ObjCon: ", t]
    | ObjMexpr {} -> "ObjMexpr"
    | ObjInclude { pathInFile = p } -> join ["ObjInclude, path = ", p]
    | ObjUtest {} -> "ObjUtest"
    | ObjRecursiveBloc {} -> "ObjRecursiveBloc"
    | ObjProgram {} -> "ObjProgram"
    | _ -> warn "All object kinds are not supported in objKindToString sementic"; ""
         
    -- First keyword for this kind (used for printing/links/extension).
    sem getFirstWord =
    | ObjLet {} -> "let"
    | ObjLang {} -> "lang"
    | ObjType {} -> "type"
    | ObjUse {} -> "use"
    | ObjSem {} -> "sem"
    | ObjSyn {} -> "syn"
    | ObjCon {} -> "con"
    | ObjMexpr {} -> "mexpr"
    | ObjInclude {} -> "include"
    | ObjUtest {} -> "utest"
    | ObjRecursiveBloc {} -> "recursive"
    | ObjProgram {} -> ""
    | _ -> warn "All object kinds are not supported in getFirstWord sementic"; ""
  
end

-- The object type is designed to represent the documentation-side structure of the code.
-- Its fields are:
-- - `name`: The name of the object. For a `let`, it corresponds to the variable name.  
-- - `doc`: All comments above the beginning of the block.  
-- - `namespace`: The namespace reflects the current position of the node in the tree and is used
--   to build its documentation path.  
-- - `kind`: Specific to the object’s type (see ObjectKind).  
-- - `sourceCode`: An **absolute** representation of the object’s source code.
--   It is not just a plain string, but a structured value defined in `source-code-word.mc` and `source-code-builder.mc`.  
-- - `prefix`: The part of the namespace removed because it is redundant.  
--   Example: if we have `src/foo.mc` and `src/bar.mc`, we can drop `src/`.  
--   `objWithPrefix` both removes the given prefix (warning if the namespace does not start with it)
--   and stores it so we can recover the original namespace later.  
-- - `isStdlib`: Marks whether the object belongs to the stdlib.
-- - `renderIt` : Indicates if the object should be rendered during rendering stage.
type Object = use ObjectKinds in { name: String, doc : String, namespace: String, kind: ObjectKind, sourceCode: SourceCode, prefix: String, isStdlib: Bool, renderIt: Bool }

-- Absolute filesystem position of the current program start.
let basePosition : String = concat (sysGetCwd ()) "/"

-- Simple field accessors.
let objName : Object -> String = lam obj. obj.name
let objKind : Object -> use ObjectKinds in ObjectKind = lam obj. obj.kind
let objDoc : Object -> String = lam obj. obj.doc
let objSourceCode : Object -> SourceCode = lam obj. obj.sourceCode    
let objNamespace : Object -> String = use ObjectKinds in lam obj. obj.namespace
let objPrefix : Object -> String = lam obj. obj.prefix
let objIsStdlib : Object -> Bool = lam obj. obj.isStdlib
let objRenderIt : Object -> Bool = lam obj. obj.renderIt

-- Object updaters (immutable setters).
let objWithName : Object -> String -> Object = lam obj. lam name. { obj with name = name }
let objWithKind : Object -> use ObjectKinds in ObjectKind -> Object = lam obj. lam kind. { obj with kind = kind }
let objWithDoc : Object -> String -> Object = lam obj. lam doc. { obj with doc = doc }
let objWithIsStdlib : Object -> Bool -> Object = lam obj. lam isStdlib. { obj with isStdlib = isStdlib }    
let objWithSourceCode : Object -> SourceCode -> Object = lam obj. lam sourceCode. { obj with sourceCode = sourceCode }
let objWithRenderIt : Object -> Bool -> Object = lam obj. lam renderIt. { obj with renderIt = renderIt }    

-- Sets a shorter namespace by removing `prefix`; stores the prefix for recovery.
-- Warns if the namespace does not start with the given prefix.
let objWithPrefix: Object -> String -> Object = lam obj. lam prefix.
    let process = lam.
        let basePrefix: String = normalizePath (concat basePosition obj.namespace) in
        let lengthBasePrefix = length basePrefix in
        let lengthPrefix = length prefix in
        if strStartsWith prefix basePrefix then subsequence basePrefix lengthPrefix lengthBasePrefix
        else
            extractingWarn (join ["The namespace ", basePrefix, "does not start with the prefix ", prefix, "."]);
            basePrefix
    in
    let namespace = match prefix with "" then obj.namespace else process () in
    let namespace = if strStartsWith "/" namespace then namespace else cons '/' namespace in
    { obj with namespace = namespace, prefix = prefix }
    
-- Replaces namespace; strips stdlib prefix if present; re-applies stored `prefix`.
let objWithNamespace : Object -> String -> Object = lam obj. lam namespace.
    let namespace =
    if strStartsWith stdlibLoc namespace then
        subsequence namespace (length stdlibLoc) (length namespace)
    else
        namespace
    in
    let obj = { obj with namespace = namespace } in
    objWithPrefix obj obj.prefix

-- Returns absolute path = prefix + namespace.
let objAbsolutePath : Object -> String = lam obj.
    concat obj.prefix obj.namespace

-- Empty default object (neutral values).
let defaultObject : Object = use ObjectKinds in { name = "", doc = "", namespace = "", renderIt = false, isStdlib = false, kind = ObjProgram {}, sourceCode = sourceCodeEmpty (), prefix = "" }

-- Extracts the language name from a Sem/Syn object; else empty string.
let objGetLangName : Object -> String = use ObjectKinds in lam obj.
    match obj.kind with ObjSem { langName = langName } | ObjSyn { langName = langName } then langName else ""


-- Renders a short textual representation of an object (for printing).
let objToString = use ObjectKinds in lam kind. lam name.
    switch kind
    case ObjLet { rec = rec, args = args } then join [if rec then "recursive " else "", "let ", name, " ", strJoin " " args]
    case ObjType { t = t } then join ["type ", name, match t with Some t then concat " : " t else ""]
    case ObjCon { t = t } then join ["con ", name, " : ", t]
    case ObjMexpr {} then "mexpr"
    case ObjProgram {} then ""
    case kind then join [getFirstWord kind, " ", name]
    end

-- Sets the (optional) type of a Let/Sem object, keeping other fields the same.
let objSetType = use ObjectKinds in lam obj. lam ty.
    { obj with kind = switch obj.kind
    case ObjLet d then ObjLet { d with ty = ty }
    case ObjSem d then ObjSem { d with ty = ty }    
    case _ then obj.kind end }
    
    
-- Object tree (hierarchy). Wraps Object to allow recursive nesting.
type ObjectTree
con ObjectNode : { obj: Object, children: [ObjectTree] } -> ObjectTree

-- Convenience helpers for ObjectTree.
let objTreeToString : ObjectTree -> String = lam tree. match tree with ObjectNode { obj = obj } in objToString obj.kind obj.name
let objTreeObj : ObjectTree -> Object = lam tree. match tree with ObjectNode { obj = obj } in obj
let objTreeChildren : ObjectTree -> [ObjectTree] = lam tree. match tree with ObjectNode { children = children } in children
let objTreeDoc : ObjectTree -> String = lam tree. objDoc (objTreeObj tree)
let objTreeSourceCode : ObjectTree -> SourceCode = lam tree. objSourceCode (objTreeObj tree)
let objTreeWithDoc : ObjectTree -> String -> ObjectTree = lam tree. lam doc.
    match tree with ObjectNode { obj = obj, children = children } in ObjectNode { obj = { obj with doc = doc}, children = children }
let objTreeWithSourceCode : ObjectTree -> SourceCode -> ObjectTree = lam tree. lam code.
    match tree with ObjectNode { obj = obj, children = children } in ObjectNode { obj = { obj with sourceCode = code}, children = children }
