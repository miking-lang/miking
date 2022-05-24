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
type SizeParam = {
  id : Name,
  dim : Int
}

let cmpSizeParam : SizeParam -> SizeParam -> Int = lam l. lam r.
  let c = nameCmp l.id r.id in
  if eqi c 0 then subi l.dim r.dim
  else c

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

lang FutharkSizeTypeEliminate = FutharkAst
  sem _incrementUseCount (typeParamUseCount : Map FutTypeParam Int) =
  | typeParam /- : FutTypeParam -/ ->
    optionGetOrElse
      (lam. typeParamUseCount)
      (optionMap
        (lam count. mapInsert typeParam (addi count 1) typeParamUseCount)
        (mapLookup typeParam typeParamUseCount))

  sem countSizeTypeParamUsesType (typeParamUseCount : Map FutTypeParam Int) =
  | FTyArray {elem = elem, dim = Some dimId} ->
    let typeParamUseCount =
      let tp = FPSize {val = dimId} in
      let count =
        match mapLookup tp typeParamUseCount with Some count then
          addi count 1
        else 1 in
      mapInsert tp count typeParamUseCount in
    countSizeTypeParamUsesType typeParamUseCount elem
  | t -> sfold_FType_FType countSizeTypeParamUsesType typeParamUseCount t

  sem countSizeTypeParamUsesExpr (typeParamUseCount : Map FutTypeParam Int) =
  | FEVar t ->
    let tp = FPSize {val = t.ident} in
    _incrementUseCount typeParamUseCount tp
  | t -> sfold_FExpr_FExpr countSizeTypeParamUsesExpr typeParamUseCount t

  sem collectUnnecessarySizeTypeParams =
  | FDeclFun t ->
    let typeParamCmp = lam tp1 : FutTypeParam. lam tp2 : FutTypeParam.
      let t : (FutTypeParam, FutTypeParam) = (tp1, tp2) in
      match t with (FPSize {val = v1}, FPSize {val = v2}) then
        nameCmp v1 v2
      else match t with (FPType {val = v1}, FPType {val = v2}) then
        nameCmp v1 v2
      else subi (constructorTag tp1) (constructorTag tp2) in
    let typeParamUseCount : Map FutTypeParam Int =
      mapFromSeq typeParamCmp
        (foldl
          (lam acc. lam p : FutTypeParam.
            match p with FPSize _ then snoc acc (p, 0)
            else acc)
          [] t.typeParams) in
    let typeParamUseCount = countSizeTypeParamUsesType typeParamUseCount t.ret in
    let paramTypes = map (lam p : (Name, FutType). p.1) t.params in
    let typeParamUseCount =
      countSizeTypeParamUsesExpr
        (foldl countSizeTypeParamUsesType typeParamUseCount paramTypes)
        t.body in
    mapFoldWithKey
      (lam acc : Set FutTypeParam. lam k : FutTypeParam. lam v : Int.
        if leqi v 1 then setInsert k acc else acc)
      (setEmpty typeParamCmp) typeParamUseCount
  sem eliminateTypeParamsType (unnecessaryTypeParams : Set FutTypeParam) =
  | FTyArray (t & {dim = Some dimId}) ->
    let elem = eliminateTypeParamsType unnecessaryTypeParams t.elem in
    let typeParam = FPSize {val = dimId} in
    let dim =
      if setMem typeParam unnecessaryTypeParams then None ()
      else Some dimId in
    FTyArray {{t with elem = elem} with dim = dim}
  | t -> smap_FType_FType (eliminateTypeParamsType unnecessaryTypeParams) t

  sem eliminateTypeParamsExpr (unnecessaryTypeParams : Set FutTypeParam) =
  | FELet t ->
    let tyBody = eliminateTypeParamsType unnecessaryTypeParams t.tyBody in
    let body = eliminateTypeParamsExpr unnecessaryTypeParams t.body in
    let inexpr = eliminateTypeParamsExpr unnecessaryTypeParams t.inexpr in
    let ty = eliminateTypeParamsType unnecessaryTypeParams t.ty in
    FELet {{{{t with tyBody = tyBody}
                with body = body}
                with inexpr = inexpr}
                with ty = ty}
  | t ->
    let ty = eliminateTypeParamsType unnecessaryTypeParams (tyFutTm t) in
    let t = withTypeFutTm ty t in
    smap_FExpr_FExpr (eliminateTypeParamsExpr unnecessaryTypeParams) t

  sem removeUnnecessarySizeTypeParams (unnecessaryTypeParams : Set FutTypeParam) =
  | FDeclFun t ->
    let eliminateTypeParams = lam ty : FutType.
      eliminateTypeParamsType unnecessaryTypeParams ty in
    let typeParams =
      foldl
        (lam acc. lam p : FutTypeParam.
          if setMem p unnecessaryTypeParams then acc else snoc acc p)
        [] t.typeParams in
    let params =
      foldl
        (lam acc. lam param : (Name, FutType).
          match eliminateTypeParams param.1 with paramType in
          snoc acc (param.0, paramType))
        [] t.params in
    let ret = eliminateTypeParams t.ret in
    let body = eliminateTypeParamsExpr unnecessaryTypeParams t.body in
    FDeclFun {{{{t with typeParams = typeParams}
                   with params = params}
                   with ret = ret}
                   with body = body}

  -- We eliminate all size type parameters that are unnecessary. A size type
  -- that is only used once within the type declaration of a function, and
  -- never within its body, is considered to be unnecessary because it might as
  -- well be replaced by an anonymous type.
  sem eliminateUnnecessarySizeParameters =
  | FDeclFun t ->
    let unnecessaryTypeParams : Set FutTypeParam =
      collectUnnecessarySizeTypeParams (FDeclFun t) in
    removeUnnecessarySizeTypeParams unnecessaryTypeParams (FDeclFun t)
  | t -> t
end

lang FutharkSizeParameterize = FutharkSizeTypeEliminate
  -- Transforms a length expression applied on a function parameter to make it
  -- instead use a size type variable of the parameter.
  sem parameterizeLengthExprs (env : SizeParameterizeEnv) =
  | FEApp ({lhs = FEConst {val = FCLength ()},
            rhs = FEVar {ident = s}} & t) ->
    let lengthParamVar = lam ident. lam info.
      FEVar {ident = ident, ty = FTyInt {info = info}, info = info}
    in
    match mapLookup s env.paramMap with Some (FTyArray tyArray) then
      match tyArray.dim with Some n then
        (env, lengthParamVar n tyArray.info)
      else
        let n = nameSym "n" in
        let newParamType = FTyArray {tyArray with dim = Some n} in
        let typeParam = FPSize {val = n} in
        let typeParams = mapInsert n typeParam env.typeParams in
        let env = {{env with paramMap = mapInsert s newParamType env.paramMap}
                        with typeParams = typeParams} in
        (env, lengthParamVar n tyArray.info)
    else smapAccumL_FExpr_FExpr parameterizeLengthExprs env (FEApp t)
  | t -> smapAccumL_FExpr_FExpr parameterizeLengthExprs env t

  sem eliminateParamAliases (env : SizeParameterizeEnv)
                            (replacements : Map Name Name) =
  | FEVar t ->
    match mapLookup t.ident replacements with Some paramId then
      FEVar {t with ident = paramId}
    else FEVar t
  | FELet ({body = FEVar {ident = id}} & t) ->
    match mapLookup id env.typeParams with Some param then
      let paramId = futTypeParamIdent param in
      let replacements = mapInsert t.ident paramId replacements in
      eliminateParamAliases env replacements t.inexpr
    else
      FELet {t with inexpr = eliminateParamAliases env replacements t.inexpr}
  | t -> smap_FExpr_FExpr (eliminateParamAliases env replacements) t

  -- Collects all size parameters by constructing a map from each distinct size
  -- parameter, where multi-dimensional array sizes are distinguished by the
  -- dimension. These size parameters are mapped to a unique index and a name
  -- representing this size type.
  sem collectSizeParameters (acc : SizeParamMap) =
  | (id, ty) /- : (Name, FutType) -/ ->
    recursive let work = lam acc : SizeParamMap. lam dimIdx. lam ty.
      match ty with FTyArray {elem = elem, dim = Some dimId} then
        let sizeParam = {id = id, dim = dimIdx} in
        let posIdx = mapSize acc.sizeToIndex in
        let acc =
          { sizeToIndex = mapInsert sizeParam posIdx acc.sizeToIndex
          , indexToIdent = mapInsert posIdx dimId acc.indexToIdent } in
        work acc (addi dimIdx 1) elem
      else acc
    in work acc 1 ty

  sem parameterizeSizeEqualities (sizeParams : SizeParamMap)
                                 (env : SizeParameterizeEnv) =
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

  sem includeSizeEqualityConstraints (sizeParams : SizeParamMap) =
  | env ->
    let env : SizeParameterizeEnv = env in
    recursive let work =
      lam dimIdx : Int. lam id : Name. lam ty : FutType.
      match ty with FTyArray (t & {dim = Some dimId}) then
        let sizeParam = {id = id, dim = dimIdx} in
        let newDimId =
          match mapLookup sizeParam sizeParams.sizeToIndex with Some idx then
            let parent = unionFindFind env.equalSizes idx in
            if neqi idx parent then
              mapLookup parent sizeParams.indexToIdent
            else Some dimId
          else Some dimId in
        let elem = work (addi dimIdx 1) id t.elem in
        FTyArray {{t with elem = elem} with dim = newDimId}
      else ty in
    {{env with paramMap = mapMapWithKey (work 1) env.paramMap}
          with retType = work 1 (nameNoSym "") env.retType}

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
    let env = includeSizeEqualityConstraints sizeParams env in
    let body = eliminateParamAliases env (mapEmpty nameCmp) body in
    let env : SizeParameterizeEnv = env in
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

  sem parameterizeSizes =
  | FProg t ->
    let decls = map parameterizeSizesDecl t.decls in
    FProg {t with decls = map eliminateUnnecessarySizeParameters decls}
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
