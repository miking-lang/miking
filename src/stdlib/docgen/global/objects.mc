include "mexpr/ast.mc"
include "./logger.mc"
include "./source-code.mc"
include "bool.mc"
include "basic-types.mc"
include "seq.mc"
include "docgen/global/util.mc"
include "stdlib.mc"
include "string.mc"
include "hashmap.mc"

-- Interface declaring all semantics for Objects
-- NOTE: Object does not represent the syntax AST.
-- It represents documentation entities derived from the AST
-- after parsing/naming.
lang ObjectInterface = MExprAst

    type ObjectDatas = {
        name: String,
        doc : String,
        -- namespace is a logical path used for URLs, hierarchy, and file layout.
        namespace: String, 
        sourceCode: SourceCode,
        isStdlib: Bool,
        id: Int,
        isArtificial: Bool -- If true, it means the node have been added by docgen.
    }

    -- By default, objects are leaf nodes.
    -- Only specific object kinds override child semantics.
    type ObjectChildren = [Object]

    syn Object =

    sem objDatas : Object -> ObjectDatas

    sem objChildren : Object -> ObjectChildren
    sem objChildren =
    | obj -> []

    -- Returns true if the object currently has children,
    -- if the object can't have children, it returns false.
    sem objHasChildren : Object -> Bool
    sem objHasChildren =
    | obj -> not (null (objChildren obj))

    sem objSetDatas : Object -> ObjectDatas -> Object

    sem objSetChildren : Object -> ObjectChildren -> Object
    sem objSetChildren =
    | obj -> lam.
        obj

    sem objMapChildren : Object -> (ObjectChildren -> ObjectChildren) -> Object
    sem objMapChildren =
    | obj -> lam f.
      let children = objChildren obj in
      let children = f children in
      objSetChildren obj children

    sem objWithoutChildren =
    | obj -> objMapChildren obj (lam. [])

    sem objAddChild =
    | obj -> lam child. objMapChildren obj (cons child)

    sem objAddChildren =
    | obj -> lam children. objMapChildren obj (concat children)    

    sem objReverseChildren =
    | obj -> objMapChildren obj reverse

    sem objToString : Object -> String
    sem objGetFirstWord : Object -> String
    
    -- Returns true if the object can represents an URL
    sem objHasUrl  : Object -> Bool
    
    -- Returns true if the object can represents a link.
    -- Objects such as Includes represent a link without having an URL.
    sem objHasLink : Object -> Bool

    sem objHasTests : Object -> Bool
    sem objHasTests =
    | _ -> false

    sem objLangName : Object -> String
    sem objLangName =
    | _ -> ""

    sem objSetType : Object -> Option Type -> Object
    sem objSetType =
    | obj -> lam. obj

    sem objMergeFailed : Object -> Object -> Object
    sem objMergeFailed =
    | obj1 -> lam obj2.
            warn (join ["Cannot merge ", objToString obj1, " and ", objToString obj2, "(incompatibles kinds)."]);
            obj1

    sem objMerge : Object -> Object -> Object
    sem objMerge =
    | obj1 -> lam obj2. objMergeFailed obj1 obj2

    sem objSetField : Object -> (ObjectDatas -> ObjectDatas) -> Object
    sem objSetField =
    | obj -> lam setter. objSetDatas obj (setter (objDatas obj))

    -- Simple field accessors.
    sem objName = | obj -> (objDatas obj).name
    sem objDoc = | obj -> (objDatas obj).doc
    sem objSourceCode = | obj -> (objDatas obj).sourceCode
    sem objNamespace = | obj -> (objDatas obj).namespace
    sem objIsStdlib = | obj -> (objDatas obj).isStdlib
    sem objId = | obj -> (objDatas obj).id
    sem objIsArtificial = | obj -> (objDatas obj).isArtificial

    sem objWithName =
    | obj -> lam name. objSetField obj (lam d. { d with name = name })

    sem objWithDoc =
    | obj -> lam doc.
        let doc = strFullTrim doc in
        objSetField obj (lam d. { d with doc = doc })

    sem objWithIsStdlib =
    | obj -> lam isStdlib. objSetField obj (lam d. { d with isStdlib = isStdlib })

    sem objWithSourceCode =
    | obj -> lam sourceCode. objSetField obj (lam d. { d with sourceCode = sourceCode })

    sem objWithId =
    | obj -> lam id. objSetField obj (lam d. { d with id = id })

    -- Shortens the namespace by removing the given prefix.
    -- This transformation is destructive and not reversible.
    -- This is used to remove the common prefix of all objects.
    sem objWithPrefix =
    | obj -> lam prefix.
        let namespace = objNamespace obj in
        let lengthNamespace = length namespace in
        let lengthPrefix = length prefix in

        let prefixSize = 
            if null namespace then
                warn (join ["The object", objName obj, " does not have a namespace yet. "]);
                lengthNamespace
            else if pathIsInStdlib prefix then
                lengthPrefix
            else if objIsStdlib obj then
                length stdlibLoc
            else if strStartsWith prefix namespace then
                lengthPrefix
            else
                warn (join ["Namespace ", namespace, " does not start with expected prefix ", prefix, "."]);
                lengthNamespace
        in

        let newNamespace = subsequence namespace prefixSize lengthNamespace in
        let newNamespace = if strStartsWith "/" newNamespace then newNamespace else cons '/' newNamespace in

        objWithNamespace obj newNamespace


    -- Replaces namespace; strips stdlib prefix if present; re-applies stored `prefix`.
    sem objWithNamespace =
    | obj -> lam namespace.
        objSetField obj (lam d. { d with namespace = namespace })

    -- Replaces namespace; strips stdlib prefix if present; re-applies stored `prefix`.
    sem objWithIsArtificial =
    | obj -> lam isArtificial.
        objSetField obj (lam d. { d with isArtificial = isArtificial })

    -- Returns true if the object has a meaningful id.
    sem objHasId =
    | obj -> neqi (objId obj) 0

    -- Returns true if the object has a code source (otherwise it has probably been added during naming)
    sem objHasSourceCode =
    | obj -> not (sourceCodeIsEmpty (objSourceCode obj))

    -- Returns absolute path = prefix + namespace.
    sem objAbsolutePath =
    | obj -> lam prefix.
        concat prefix (objNamespace obj)

    sem objDefaultDoc : () -> String
    sem objDefaultDoc =
    | _ -> "No documentation available here."

    -- Empty default object (neutral values).
    sem objDefaultDatas : () -> ObjectDatas
    sem objDefaultDatas =
    | () -> {
        name = "",
        doc = objDefaultDoc (),
        namespace = "",
        isStdlib = false,
        sourceCode = sourceCodeEmpty (),
        id = 0,
        isArtificial = false
    }

    sem objTryGetDoc : Object -> String
    sem objTryGetDoc =
    | obj ->
        let doc = objDoc obj in
        if eqString doc (objDefaultDoc ()) then "" else doc


    sem objNameIfHas : Object -> Option String
    sem objNameIfHas =
    | obj -> if objHasName obj then
              Some (objName obj)
           else None {}

    sem objHasName : Object -> Bool
    sem objHasName =
    | _ -> true

    sem objCountChildren : Object -> Int
    sem objCountChildren =
    | obj -> foldl addi 0 (map (lam obj. if objHasChildren obj then objCountChildren obj else 1) (objChildren obj))
    
    sem objMergeIsRelevant : (Object, Object) -> Bool
    sem objMergeIsRelevant =
    | _ -> false

    sem objVariantsAreCoveredBy : (Object, Object) -> Bool
    sem objVariantsAreCoveredBy =
    | _ -> false


end

----------------------------------------------------------------------
-- ObjProgram
----------------------------------------------------------------------
lang ObjProgram = ObjectInterface

    syn Object +=
    | ObjProgram { children: ObjectChildren, datas: ObjectDatas}

    sem objDatas +=
    | ObjProgram { datas = datas } -> datas

    sem objChildren +=
    | ObjProgram { children = children } -> children

    sem objSetDatas +=
    | ObjProgram f -> lam datas. ObjProgram { f with datas = datas }

    sem objSetChildren +=
    | ObjProgram f -> lam children. ObjProgram{ f with children = children }

    sem objToString +=
    | ObjProgram {} -> "ObjProgram"

    sem objGetFirstWord +=
    | ObjProgram {} -> ""

    sem objHasUrl +=
    | ObjProgram {} -> true

    sem objHasLink +=
    | ObjProgram {} -> true

    sem objHasName +=
    | ObjProgram {} -> false

end

----------------------------------------------------------------------
-- ObjInclude
----------------------------------------------------------------------
lang ObjInclude = ObjectInterface

    syn Object +=
    | ObjInclude { pathInFile: String, datas: ObjectDatas, child: Option Object }

    sem objSetDatas +=
    | ObjInclude f -> lam datas. ObjInclude { f with datas = datas}

    sem objSetChildren +=
    | ObjInclude f & obj -> lam children.
      let l = length children in
      switch l
      case 0 then ObjInclude { f with child = None {} }
      case 1 then ObjInclude { f with child = Some (head children) }
      case _ then warn (join ["Include nodes must have zero or one child; received ", int2string l, "."]) ; obj
      end

    sem objChildren +=
    | ObjInclude { child = Some child } -> [child]
    | ObjInclude { child = None {} } -> []    

    sem objDatas +=
    | ObjInclude { datas = datas } -> datas

    sem objToString +=
    | ObjInclude { pathInFile = p } -> join ["ObjInclude, path = ", p]
    
    sem objGetFirstWord +=
    | ObjInclude {} -> ""

    sem objHasUrl +=
    | ObjInclude {} -> false

    sem objHasName +=
    | ObjInclude {} -> false

    sem objHasLink +=
    | ObjInclude {} -> true

end

----------------------------------------------------------------------
-- ObjLet
----------------------------------------------------------------------
lang ObjLet = ObjectInterface

    syn Object +=
    | ObjLet { ty: Option Type, datas: ObjectDatas }

    sem objDatas +=
    | ObjLet { datas = datas } -> datas

    sem objSetDatas +=
    | ObjLet f -> lam datas. ObjLet { f with datas = datas}

    sem objToString +=
    | ObjLet { ty = ty } -> "ObjLet"

    sem objGetFirstWord +=
    | ObjLet {} -> "let"

    sem objHasUrl +=
    | ObjLet {} -> true

    sem objHasLink +=
    | ObjLet {} -> true

    sem objSetType +=
    | ObjLet d -> lam ty. ObjLet { d with ty = ty }

    sem objHasTests +=
    | ObjLet {} -> true

end

----------------------------------------------------------------------
-- ObjLang
----------------------------------------------------------------------
lang ObjLang = ObjectInterface

    syn Object +=
    | ObjLang { parents : [String], datas : ObjectDatas, children: ObjectChildren }

    sem objSetDatas +=
    | ObjLang f -> lam datas. ObjLang { f with datas = datas}

    sem objSetChildren +=
    | ObjLang f -> lam children. ObjLang { f with children = children }

    sem objDatas +=
    | ObjLang { datas = datas } -> datas

    sem objChildren +=
    | ObjLang { children = children } -> children

    sem objToString +=
    | ObjLang { parents = parents } ->
            join ["ObjLang, parents: ", strJoin ", " parents]

    sem objGetFirstWord +=
    | ObjLang {} -> "lang"

    sem objHasUrl +=
    | ObjLang {} -> true

    sem objHasLink +=
    | ObjLang {} -> true

end

----------------------------------------------------------------------
-- ObjType
----------------------------------------------------------------------
lang ObjType = ObjectInterface

    syn Object +=
    | ObjType { t: Option Type, datas: ObjectDatas }

    sem objDatas +=
    | ObjType { datas = datas } -> datas

    sem objSetDatas +=
    | ObjType f -> lam datas. ObjType { f with datas = datas }

    sem objToString +=
    | ObjType {} ->
        "ObjType"

    sem objGetFirstWord +=
    | ObjType {} -> "type"

    sem objHasUrl +=
    | ObjType {} -> true

    sem objHasLink +=
    | ObjType {} -> true

    sem objMerge +=
    | ObjType {} & obj1 -> lam obj2.
            match obj2 with ObjType {} then obj1
            else objMergeFailed obj1 obj2

end

----------------------------------------------------------------------
-- ObjSem
----------------------------------------------------------------------
lang ObjSem = ObjectInterface

    -- This is the string of the expression of the pattern.
    type SemVariant = String 

    syn Object +=
    | ObjSem { langName: String, ty: Option Type, variants: [SemVariant], datas: ObjectDatas }

    sem objMergeIsRelevant +=
    | (ObjSem { variants = v1 } & o1, ObjSem { variants = v2 } & o2) ->
        let v = if lti (length v1) (length v2) then v2 else v1 in
        match objMerge o1 o2 with ObjSem { variants = v3 } in
        gti (length v3) (length v)

    sem objVariantsAreCoveredBy +=
    | (ObjSem { variants = v1 } & o1, ObjSem { variants = v2 } & o2) ->
        if lti (length v2) (length v1) then false else
        match objMerge o1 o2 with ObjSem { variants = v3 } in
        lti (length v3) (length v2)

    sem objToString +=
    | ObjSem { langName = langName } ->
            join ["ObjSem, langName = ", langName]

    sem objDatas +=
    | ObjSem { datas = datas } -> datas

    sem objSetDatas +=
    | ObjSem f -> lam datas. ObjSem { f with datas = datas }

    sem objGetFirstWord +=
    | ObjSem {} -> "sem"

    sem objHasUrl +=
    | ObjSem {} -> true

    sem objHasLink +=
    | ObjSem {} -> true

    sem objLangName +=
    | ObjSem { langName = langName } -> langName

    sem objSetType +=
    | ObjSem d -> lam ty. ObjSem { d with ty = ty }    

    sem objMerge +=
    | (ObjSem d1) & obj1 -> lam obj2.
            match obj2 with ObjSem d2 then
                let variants = foldl
                    (lam acc. lam v. hmInsert v () acc)
                    (hashmapEmpty ())
                    (concat d1.variants d2.variants)
                in
                ObjSem { d1 with variants = hmKeys variants }
            else objMergeFailed obj1 obj2

end

----------------------------------------------------------------------
-- ObjSyn
----------------------------------------------------------------------
lang ObjSyn = ObjectInterface

    type SynVariant = {
        name: String,
        vtype: String,
        doc: String
    }

    syn Object +=
    | ObjSyn { langName: String, variants: [SynVariant], datas: ObjectDatas }    

    sem objMergeIsRelevant +=
    | (ObjSyn { variants = v1 } & o1, ObjSyn { variants = v2 } & o2) ->
        let v = if lti (length v1) (length v2) then v2 else v1 in
        match objMerge o1 o2 with ObjSyn { variants = v3 } in
        gti (length v3) (length v)

    sem objVariantsAreCoveredBy +=
    | (ObjSyn { variants = v1 } & o1, ObjSyn { variants = v2 } & o2) ->
        if lti (length v2) (length v1) then false else
        match objMerge o1 o2 with ObjSyn { variants = v3 } in
        lti (length v3) (length v2)


    sem objDatas +=
    | ObjSyn { datas = datas } -> datas

    sem objSetDatas +=
    | ObjSyn f -> lam datas. ObjSyn { f with datas = datas }

    sem objToString +=
    | ObjSyn { langName = langName } ->
            join ["ObjSyn, langName = ", langName]

    sem objGetFirstWord +=
    | ObjSyn {} -> "syn"

    sem objHasUrl +=
    | ObjSyn {} -> true

    sem objLangName +=
    | ObjSyn { langName = langName } -> langName

    sem objHasLink +=
    | ObjSyn {} -> true

    sem objMerge +=
    | (ObjSyn d1) & obj1 -> lam obj2.
            match obj2 with ObjSyn d2 then
                let variants = foldl
                    (lam acc. lam v. hmInsert v.name v acc)
                    (hashmapEmpty ())
                    (concat d1.variants d2.variants)
                in
                ObjSyn { d1 with variants = hmValues variants }
            else objMergeFailed obj1 obj2

end

----------------------------------------------------------------------
-- ObjCon
----------------------------------------------------------------------
lang ObjCon = ObjectInterface

    syn Object +=
    | ObjCon { t: Type, parentType: String, datas: ObjectDatas }

    sem objDatas +=
    | ObjCon { datas = datas } -> datas

    sem objSetDatas +=
    | ObjCon f -> lam datas. ObjCon { f with datas = datas }

    sem objToString +=
    | ObjCon { t = t, parentType = parentType } -> join ["ObjCon with parent: ", parentType]

    sem objGetFirstWord +=
    | ObjCon {} -> "con"

    sem objHasUrl +=
    | ObjCon {} -> true

    sem objHasLink +=
    | ObjCon {} -> true

    sem objMerge +=
    | ObjCon {} & obj1 -> lam obj2.
            match obj2 with ObjCon {} then obj1
            else objMergeFailed obj1 obj2

end

----------------------------------------------------------------------
-- ObjMexpr
----------------------------------------------------------------------
lang ObjMexpr = ObjectInterface

    syn Object +=
    | ObjMexpr ObjectDatas

    sem objDatas +=
    | ObjMexpr datas -> datas

    sem objSetDatas +=
    | ObjMexpr _ -> lam datas. ObjMexpr datas

    sem objToString +=
    | ObjMexpr {} -> "ObjMexpr"

    sem objGetFirstWord +=
    | ObjMexpr {} -> "mexpr"

    sem objHasUrl +=
    | ObjMexpr {} -> false

    sem objHasLink +=
    | ObjMexpr {} -> false

    sem objHasName +=
    | ObjMexpr {} -> false

end

----------------------------------------------------------------------
-- ObjUtest
----------------------------------------------------------------------
lang ObjUtest = ObjectInterface

    syn Object +=
    | ObjUtest ObjectDatas

    sem objDatas +=
    | ObjUtest datas -> datas

    sem objSetDatas +=
    | ObjUtest _ -> lam datas. ObjUtest datas

    sem objToString +=
    | ObjUtest {} -> "ObjUtest"

    sem objGetFirstWord +=
    | ObjUtest {} -> "utest"

    sem objHasUrl +=
    | ObjUtest {} -> false

    sem objHasLink +=
    | ObjUtest {} -> false

    sem objHasName +=
    | ObjUtest {} -> false

end

----------------------------------------------------------------------
-- Combine all object languages
----------------------------------------------------------------------
lang Objects =
    ObjProgram +
    ObjInclude +
    ObjLet +
    ObjLang +
    ObjType +
    ObjSem +
    ObjSyn +
    ObjCon +
    ObjMexpr +
    ObjUtest
end
