-- Translates variables containing the result of applying the length constant
-- on a function parameter into a size parameter. This helps the Futhark
-- compiler with inference of array sizes.

include "map.mc"
include "name.mc"
include "union-find.mc"
include "futhark/ast.mc"
include "futhark/pprint.mc"

-- A size parameter represents the size of one dimension of an array. As an
-- array may be multi-dimensional, we distinguish the size parameters using a
-- dimension index.
lang FutharkSizeType = FutharkAst
  type SizeParam = {
    id : Name,
    dim : Int
  }

  sem cmpSizeParam : SizeParam -> SizeParam -> Int
  sem cmpSizeParam l =
  | r ->
    let c = nameCmp l.id r.id in
    if eqi c 0 then subi l.dim r.dim else c

  type SizeParamMap = {
    sizeToIndex : Map SizeParam Int,
    indexToIdent : Map Int Name
  }

  type SizeParameterizeEnv = {
    paramMap : Map Name FutType,
    typeParams : Map Name FutTypeParam,
    retType : FutType,
    equalSizes : UnionFind
  }

  type LengthParameterizeEnv = {
    paramMap : Map Name Name,
    replaceMap : Map Name Name
  }
end

lang FutharkSizeTypeEliminate = FutharkAst + FutharkSizeType
  sem _incrementUseCount : Map Name Int -> Name -> Map Name Int
  sem _incrementUseCount typeParamUseCount =
  | typeParamId ->
    optionGetOrElse
      (lam. typeParamUseCount)
      (optionMap
        (lam count. mapInsert typeParamId (addi count 1) typeParamUseCount)
        (mapLookup typeParamId typeParamUseCount))

  sem countSizeTypeParamUsesType : Map Name Int -> FutType -> Map Name Int
  sem countSizeTypeParamUsesType typeParamUseCount =
  | FTyArray {elem = elem, dim = Some (NamedDim dimId)} ->
    let typeParamUseCount =
      let count =
        match mapLookup dimId typeParamUseCount with Some count then
          addi count 1
        else 1 in
      mapInsert dimId count typeParamUseCount in
    countSizeTypeParamUsesType typeParamUseCount elem
  | t -> sfold_FType_FType countSizeTypeParamUsesType typeParamUseCount t

  sem countSizeTypeParamUsesExpr : Map Name Int -> FutExpr -> Map Name Int
  sem countSizeTypeParamUsesExpr typeParamUseCount =
  | FEVar t -> _incrementUseCount typeParamUseCount t.ident
  | FESizeCoercion {ty = FTyArray {dim = Some (NamedDim dimId)}} ->
    _incrementUseCount typeParamUseCount dimId
  | t -> sfold_FExpr_FExpr countSizeTypeParamUsesExpr typeParamUseCount t

  sem collectUnnecessarySizeTypes : FutDecl -> Set Name
  sem collectUnnecessarySizeTypes =
  | FDeclFun t ->
    let typeParamUseCount : Map Name Int =
      mapFromSeq nameCmp
        (foldl
          (lam acc. lam p : FutTypeParam.
            match p with FPSize {val = id} then snoc acc (id, 0)
            else acc)
          [] t.typeParams) in
    let typeParamUseCount = countSizeTypeParamUsesType typeParamUseCount t.ret in
    let paramTypes = map (lam p : (Name, FutType). p.1) t.params in
    let typeParamUseCount =
      countSizeTypeParamUsesExpr
        (foldl countSizeTypeParamUsesType typeParamUseCount paramTypes)
        t.body in
    mapFoldWithKey
      (lam acc : Set Name. lam k : Name. lam v : Int.
        if leqi v 1 then setInsert k acc else acc)
      (setEmpty nameCmp) typeParamUseCount

  sem stripUndefSizeParamsExpr : Set Name -> FutExpr -> (Set Name, FutExpr)
  sem stripUndefSizeParamsExpr vars =
  | FELet t ->
    let tyBody = stripUndefSizeParamsType vars t.tyBody in
    match stripUndefSizeParamsExpr vars t.body with (vars, body) in
    let vars = setInsert t.ident vars in
    match stripUndefSizeParamsExpr vars t.inexpr with (vars, inexpr) in
    let ty = stripUndefSizeParamsType vars t.ty in
    ( vars
    , FELet {t with tyBody = tyBody, body = body, inexpr = inexpr, ty = ty} )
  | FESizeCoercion t ->
    match stripUndefSizeParamsExpr vars t.e with (vars, e) in
    let ty = stripUndefSizeParamsType vars t.ty in
    ( vars
    , FESizeCoercion {t with e = e, ty = ty} )
  | t -> smapAccumL_FExpr_FExpr stripUndefSizeParamsExpr vars t

  sem stripUndefSizeParamsType : Set Name -> FutType -> FutType
  sem stripUndefSizeParamsType vars =
  | FTyArray (t & {dim = Some (NamedDim dimId)}) ->
    let elem = stripUndefSizeParamsType vars t.elem in
    let dim =
      if setMem dimId vars then Some (NamedDim dimId)
      else None () in
    FTyArray {t with elem = elem, dim = dim}
  | ty -> smap_FType_FType (stripUndefSizeParamsType vars) ty

  sem sizeTypeParamId : FutTypeParam -> [Name]
  sem sizeTypeParamId =
  | FPSize t -> [t.val]
  | FPType _ -> []

  sem removeUnnecessarySizeTypes : Set Name -> FutDecl -> FutDecl
  sem removeUnnecessarySizeTypes unnecessaryTypeParams =
  | FDeclFun t ->
    let stripTypeParams = lam vars. lam ty : FutType.
      stripUndefSizeParamsType vars ty in
    let typeParams =
      foldl
        (lam acc. lam p : FutTypeParam.
          match p with FPSize t then
            if setMem t.val unnecessaryTypeParams then acc else snoc acc p
          else snoc acc p)
        [] t.typeParams in
    let vars =
      setUnion
        (setOfSeq nameCmp (join (map sizeTypeParamId typeParams)))
        (setOfSeq nameCmp (map (lam param. param.0) t.params)) in
    let params =
      foldl
        (lam acc. lam param : (Name, FutType).
          let paramType = stripTypeParams vars param.1 in
          snoc acc (param.0, paramType))
        [] t.params in
    let ret = stripTypeParams vars t.ret in
    match stripUndefSizeParamsExpr vars t.body with (_, body) in
    FDeclFun {t with typeParams = typeParams, params = params,
                     ret = ret, body = body}

  sem eliminateUnnecessarySizeTypes : FutDecl -> FutDecl
  sem eliminateUnnecessarySizeTypes =
  | (FDeclFun t) & decl ->
    let unnecessaryTypeParameters = collectUnnecessarySizeTypes decl in
    removeUnnecessarySizeTypes unnecessaryTypeParameters decl
  | FDeclType t ->
    let definedVars = setOfSeq nameCmp (join (map sizeTypeParamId t.typeParams)) in
    let ty = stripUndefSizeParamsType definedVars t.ty in
    FDeclType {t with ty = ty}
  | t -> t
end

lang FutharkSizeParameterize = FutharkSizeTypeEliminate
  -- Transforms a length expression applied on a function parameter to make it
  -- instead use a size type variable of the parameter.
  sem parameterizeLengthExprs : SizeParameterizeEnv -> FutExpr
                             -> (SizeParameterizeEnv, FutExpr)
  sem parameterizeLengthExprs env =
  | FEApp ({lhs = FEConst {val = FCLength ()},
            rhs = FEVar {ident = s}} & t) ->
    let lengthParamVar = lam ident. lam info.
      FEVar {ident = ident, ty = FTyInt {info = info, sz = I64 ()}, info = info}
    in
    match mapLookup s env.paramMap with Some (FTyArray tyArray) then
      match tyArray.dim with Some (NamedDim n) then
        (env, lengthParamVar n tyArray.info)
      else
        let n = nameSym "n" in
        let newParamType = FTyArray {tyArray with dim = Some (NamedDim n)} in
        let typeParam = FPSize {val = n} in
        let typeParams = mapInsert n typeParam env.typeParams in
        let env = {{env with paramMap = mapInsert s newParamType env.paramMap}
                        with typeParams = typeParams} in
        (env, lengthParamVar n tyArray.info)
    else smapAccumL_FExpr_FExpr parameterizeLengthExprs env (FEApp t)
  | t -> smapAccumL_FExpr_FExpr parameterizeLengthExprs env t

  sem lookupReplacement : Name -> Map Name Name -> Name
  sem lookupReplacement id =
  | replacements ->
    match mapLookup id replacements with Some newId then
      lookupReplacement newId replacements
    else id

  sem eliminateParamAliases : SizeParameterizeEnv -> Map Name Name -> FutExpr
                           -> FutExpr
  sem eliminateParamAliases env replacements =
  | FEVar t ->
    let paramId = lookupReplacement t.ident replacements in
    FEVar {t with ident = paramId}
  | FELet ({body = FEVar {ident = id}} & t) ->
    match mapLookup id env.typeParams with Some param then
      let paramId = futTypeParamIdent param in
      let replacements = mapInsert t.ident paramId replacements in
      eliminateParamAliases env replacements t.inexpr
    else
      FELet {t with inexpr = eliminateParamAliases env replacements t.inexpr}
  | FESizeCoercion (t & {ty = FTyArray (array & {dim = Some (NamedDim dimId)})}) ->
    let newDimId = lookupReplacement dimId replacements in
    FESizeCoercion {t with ty = FTyArray {array with dim = Some (NamedDim newDimId)}}
  | t -> smap_FExpr_FExpr (eliminateParamAliases env replacements) t

  -- Collects all size parameters by constructing a map from each distinct size
  -- parameter, where multi-dimensional array sizes are distinguished by the
  -- dimension. These size parameters are mapped to a unique index and a name
  -- representing this size type.
  sem collectSizeParameters : SizeParamMap -> (Name, FutType) -> SizeParamMap
  sem collectSizeParameters acc =
  | (id, ty) ->
    recursive let work = lam acc. lam dimIdx. lam ty.
      match ty with FTyArray {elem = elem, dim = Some (NamedDim dimId)} then
        let sizeParam = {id = id, dim = dimIdx} in
        let posIdx = mapSize acc.sizeToIndex in
        let acc =
          { sizeToIndex = mapInsert sizeParam posIdx acc.sizeToIndex
          , indexToIdent = mapInsert posIdx dimId acc.indexToIdent } in
        work acc (addi dimIdx 1) elem
      else acc
    in work acc 1 ty

  sem parameterizeSizeEqualities : SizeParamMap -> SizeParameterizeEnv
                                -> FutExpr -> (SizeParameterizeEnv, FutExpr)
  sem parameterizeSizeEqualities sizeParams env =
  | FELet {body = FESizeEquality t, inexpr = inexpr} ->
    let p1 : SizeParam = {id = t.x1, dim = t.d1} in
    let p2 : SizeParam = {id = t.x2, dim = t.d2} in
    match mapLookup p1 sizeParams.sizeToIndex with Some idx1 then
      match mapLookup p2 sizeParams.sizeToIndex with Some idx2 then
        let env = {env with equalSizes = unionFindUnion env.equalSizes idx1 idx2} in
        parameterizeSizeEqualities sizeParams env inexpr
      else error "Invalid size equality constraint"
    else error "Invalid size equality constraint"
  | t -> smapAccumL_FExpr_FExpr (parameterizeSizeEqualities sizeParams) env t

  sem includeSizeEqualityConstraints : SizeParamMap -> SizeParameterizeEnv
                                    -> SizeParameterizeEnv
  sem includeSizeEqualityConstraints sizeParams =
  | env ->
    recursive let work = lam dimIdx. lam id. lam ty.
      match ty with FTyArray (t & {dim = Some (NamedDim dimId)}) then
        let sizeParam = {id = id, dim = dimIdx} in
        let newDimId =
          match mapLookup sizeParam sizeParams.sizeToIndex with Some idx then
            let parent = unionFindFind env.equalSizes idx in
            if neqi idx parent then
              optionMap
                (lam v. NamedDim v)
                (mapLookup parent sizeParams.indexToIdent)
            else Some (NamedDim dimId)
          else Some (NamedDim dimId) in
        let elem = work (addi dimIdx 1) id t.elem in
        FTyArray {{t with elem = elem} with dim = newDimId}
      else ty in
    {{env with paramMap = mapMapWithKey (work 1) env.paramMap}
          with retType = work 1 (nameNoSym "") env.retType}

  sem identifySizeTypeReplacements : SizeParamMap -> SizeParameterizeEnv
                                  -> Map Name Name
  sem identifySizeTypeReplacements sizeParams =
  | env ->
    let uf = env.equalSizes in
    let insertId = lam fromIdx. lam toIdx. lam acc.
      match mapLookup fromIdx sizeParams.indexToIdent with Some fromId then
        match mapLookup toIdx sizeParams.indexToIdent with Some toId then
          mapInsert fromId toId acc
        else acc
      else acc in
    recursive let work = lam acc. lam idx.
      if eqi idx uf.size then acc
      else
        let parent = unionFindFind uf idx in
        let acc =
          if eqi parent idx then acc
          else insertId idx parent acc in
        work acc (addi idx 1)
    in
    work (mapEmpty nameCmp) 0

  sem parameterizeSizesDecl : FutDecl -> FutDecl
  sem parameterizeSizesDecl =
  | FDeclFun t ->
    let nameAndType : FutTypeParam -> (Name, FutTypeParam) = lam typeParam.
      let typeParamName =
        match typeParam with FPSize {val = id} then id
        else match typeParam with FPType {val = id} then id
        else never in
      (typeParamName, typeParam)
    in
    let emptyBiMap = { sizeToIndex = mapEmpty cmpSizeParam
                     , indexToIdent = mapEmpty subi } in
    let sizeParams : SizeParamMap =
      collectSizeParameters
        (foldl collectSizeParameters emptyBiMap t.params)
        (nameNoSym "", t.ret) in
    let env = {
      paramMap = mapFromSeq nameCmp t.params,
      typeParams = mapFromSeq nameCmp (map nameAndType t.typeParams),
      retType = t.ret,
      equalSizes = unionFindInit (mapSize sizeParams.sizeToIndex)} in
    match parameterizeLengthExprs env t.body with (env, body) in
    match parameterizeSizeEqualities sizeParams env body with (env, body) in
    let replacements = identifySizeTypeReplacements sizeParams env in
    let env = includeSizeEqualityConstraints sizeParams env in
    let body = eliminateParamAliases env replacements body in
    let params =
      map
        (lam param : (Name, FutType).
          let ty = mapFindOrElse (lam. param.1) param.0 env.paramMap in
          (param.0, ty))
        t.params in
    FDeclFun {{{{t with typeParams = mapValues env.typeParams}
                   with params = params}
                   with ret = env.retType}
                   with body = body}
  | t -> t

  sem parameterizeSizes : FutProg -> FutProg
  sem parameterizeSizes =
  | FProg t ->
    let f = lam decl. eliminateUnnecessarySizeTypes decl in
    let decls = map parameterizeSizesDecl t.decls in
--    printLn (use FutharkPrettyPrint in printFutProg (FProg {decls = decls}));
    FProg {t with decls = map f decls}
end

lang TestLang = FutharkSizeParameterize + FutharkPrettyPrint end

mexpr

use TestLang in

let f = nameSym "f" in
let s = nameSym "s" in
let x = nameSym "x" in
let y = nameSym "y" in
let n = nameSym "n" in
let t = FProg {decls = [
  FDeclFun {
    ident = f, entry = true, typeParams = [FPSize {val = n}],
    params = [(s, futSizedArrayTy_ futIntTy_ n)],
    ret = futIntTy_,
    body = futBindall_ [
      nuFutLet_ x (futApp_ (futConst_ (FCLength ())) (nFutVar_ s)),
      futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, futInt_ 1]
    ],
    info = NoInfo ()}]} in
let result = parameterizeSizes t in
let expected = FProg {decls = [
  FDeclFun {
    ident = f, entry = true, typeParams = [FPSize {val = n}],
    params = [(s, futSizedArrayTy_ futIntTy_ n)],
    ret = futIntTy_,
    body = futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ n, futInt_ 1],
    info = NoInfo ()}]} in

-- NOTE(larshum, 2021-08-11): We compare the pretty-printed strings as equality
-- has not been implemented for Futhark AST nodes.
utest printFutProg result with printFutProg expected using eqString in

let t = FProg {decls = [
  FDeclConst {
    ident = x, ty = futIntTy_, val = futInt_ 0, info = NoInfo ()},
  FDeclFun {
    ident = f, entry = true, typeParams = [FPSize {val = x}],
    params = [(s, futSizedArrayTy_ futIntTy_ x)],
    ret = futIntTy_,
    body = futBindall_ [
      nuFutLet_ y (futApp_ (futConst_ (FCLength ())) (nFutVar_ s)),
      futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, futInt_ 1]],
    info = NoInfo ()}]} in
let expected = FProg {decls = [
  FDeclConst {
    ident = x, ty = futIntTy_, val = futInt_ 0, info = NoInfo ()},
  FDeclFun {
    ident = f, entry = true, typeParams = [FPSize {val = x}],
    params = [(s, futSizedArrayTy_ futIntTy_ x)],
    ret = futIntTy_,
    body = futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, futInt_ 1],
    info = NoInfo ()}]} in
utest printFutProg (parameterizeSizes t) with printFutProg expected using eqString in

let t = FProg {decls = [
  FDeclFun {
    ident = f, entry = false, typeParams = [FPType {val = y}],
    params = [(s, futUnsizedArrayTy_ (nFutIdentTy_ y))],
    ret = futIntTy_,
    body = futBindall_ [
      nuFutLet_ x (futApp_ (futConst_ (FCLength ())) (nFutVar_ s)),
      futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, futInt_ 1]],
    info = NoInfo ()}]} in
let n = nameSym "n" in
let expected = FProg {decls = [
  FDeclFun {
    ident = f, entry = false, typeParams = [FPType {val = y}, FPSize {val = n}],
    params = [(s, futSizedArrayTy_ (nFutIdentTy_ y) n)],
    ret = futIntTy_,
    body = futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ n, futInt_ 1],
    info = NoInfo ()}]} in
utest printFutProg (parameterizeSizes t) with printFutProg expected using eqString in

let s2 = nameSym "s2" in
let n1 = nameSym "n1" in
let n2 = nameSym "n2" in
let n3 = nameSym "n3" in
let n4 = nameSym "n4" in
let n5 = nameSym "n5" in
let t = FProg {decls = [
  FDeclFun {
    ident = f, entry = false,
    typeParams = [FPSize {val = n1}, FPSize {val = n2}, FPSize {val = n3},
                  FPSize {val = n4}, FPSize {val = n5}],
    params = [
      (s, futSizedArrayTy_ (futSizedArrayTy_ (futSizedArrayTy_ futIntTy_ n3) n2) n1),
      (s2, futSizedArrayTy_ (futSizedArrayTy_ futIntTy_ n5) n4)],
    ret = futIntTy_,
    body = futBindall_ [
      nuFutLet_ x (futSizeEquality_ s 3 s2 2),
      futInt_ 0],
    info = NoInfo ()}]} in
let expected = FProg {decls = [
  FDeclFun {
    ident = f, entry = false, typeParams = [FPSize {val = n3}],
    params = [
      (s, futUnsizedArrayTy_ (futUnsizedArrayTy_ (futSizedArrayTy_ futIntTy_ n3))),
      (s2, futUnsizedArrayTy_ (futSizedArrayTy_ futIntTy_ n3))],
    ret = futIntTy_, body = futInt_ 0, info = NoInfo ()}]} in
utest printFutProg (parameterizeSizes t) with printFutProg expected using eqString in

let g = nameSym "g" in
let t = FProg {decls = [
  FDeclFun {
    ident = g, entry = false, typeParams = [FPSize {val = n}],
    params = [(s, futSizedArrayTy_ futIntTy_ n)],
    ret = futIntTy_,
    body = futReduce_ (futConst_ (FCAdd ())) (futInt_ 0) (nFutVar_ s),
    info = NoInfo ()},
  FDeclFun {
    ident = f, entry = false,
    typeParams = [FPSize {val = n1}, FPSize {val = n2}, FPSize {val = n3}],
    params = [(s, futSizedArrayTy_ (futSizedArrayTy_ futIntTy_ n2) n1)],
    ret = futSizedArrayTy_ futIntTy_ n3,
    body = futBindall_ [
      uFutLet_ "" (futSizeEquality_ s 1 (nameNoSym "") 1),
      futMap_ (nFutVar_ g) (nFutVar_ s)],
    info = NoInfo ()}]} in
let expected = FProg {decls = [
  FDeclFun {
    ident = g, entry = false, typeParams = [],
    params = [(s, futUnsizedArrayTy_ futIntTy_)],
    ret = futIntTy_,
    body = futReduce_ (futConst_ (FCAdd ())) (futInt_ 0) (nFutVar_ s),
    info = NoInfo ()},
  FDeclFun {
    ident = f, entry = false,
    typeParams = [FPSize {val = n1}],
    params = [(s, futSizedArrayTy_ (futUnsizedArrayTy_ futIntTy_) n1)],
    ret = futSizedArrayTy_ futIntTy_ n1,
    body = futMap_ (nFutVar_ g) (nFutVar_ s),
    info = NoInfo ()}]} in
utest printFutProg (parameterizeSizes t) with printFutProg expected using eqString in

()
