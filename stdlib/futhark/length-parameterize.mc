-- Translates variables containing the result of applying the length constant
-- on a function parameter into a size parameter. This helps the Futhark
-- compiler with inference of array sizes.

include "map.mc"
include "name.mc"
include "futhark/ast.mc"
include "futhark/pprint.mc"

type LengthParameterizeEnv = {
  paramMap : Map Name FutType,
  typeParams : Map Name FutTypeParam
}

lang FutharkLengthParameterize = FutharkAst
  sem parameterizeLengthExpr (env : LengthParameterizeEnv) =
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
    else smapAccumL_FExpr_FExpr parameterizeLengthExpr env (FEApp t)
  | t -> smapAccumL_FExpr_FExpr parameterizeLengthExpr env t

  sem eliminateParamAliases (env : LengthParameterizeEnv)
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

  sem parameterizeLengthDecl =
  | FDeclFun t ->
    let nameAndType : FutTypeParam -> (Name, FutTypeParam) = lam typeParam.
      let typeParamName =
        match typeParam with FPSize {val = id} then id
        else match typeParam with FPType {val = id} then id
        else never in
      (typeParamName, typeParam)
    in
    let env = {
      paramMap = mapFromSeq nameCmp t.params,
      typeParams = mapFromSeq nameCmp (map nameAndType t.typeParams)} in
    match parameterizeLengthExpr env t.body with (env, body) then
      let body = eliminateParamAliases env (mapEmpty nameCmp) body in
      let env : LengthParameterizeEnv = env in
      let params =
        map
          (lam param : (Name, FutType).
            let ty = mapFindOrElse (lam. param.1) param.0 env.paramMap in
            (param.0, ty))
          t.params in
      FDeclFun {{{t with body = body}
                    with params = params}
                    with typeParams = mapValues env.typeParams}
    else never
  | t -> t

  sem parameterizeLength =
  | FProg t -> FProg {t with decls = map parameterizeLengthDecl t.decls}
end

lang TestLang = FutharkLengthParameterize + FutharkPrettyPrint

mexpr

use TestLang in

let f = nameSym "f" in
let s = nameSym "s" in
let x = nameSym "x" in
let y = nameSym "y" in
let n = nameSym "n" in
let t = FProg {decls = [
  FDeclFun {
    ident = f, entry = true, typeParams = [],
    params = [(s, futUnsizedArrayTy_ futIntTy_)],
    ret = futIntTy_,
    body = futBindall_ [
      nuFutLet_ x (futApp_ (futConst_ (FCLength ())) (nFutVar_ s)),
      futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, futInt_ 1]
    ],
    info = NoInfo ()}]} in
let result = parameterizeLength t in
let expected = FProg {decls = [
  FDeclFun {
    ident = f, entry = true, typeParams = [FPSize {val = n}],
    params = [(s, futSizedArrayTy_ futIntTy_ n)],
    ret = futIntTy_,
    body = futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ n, futInt_ 1],
    info = NoInfo ()}]} in

-- NOTE(larshum, 2021-08-11): We compare the pretty-printed strings as equality
-- has not been implemented for Futhark AST nodes.
utest printFutProg (parameterizeLength t) with printFutProg expected using eqString in

let t = FProg {decls = [
  FDeclFun {
    ident = f, entry = true, typeParams = [FPSize {val = x}],
    params = [(s, futSizedArrayTy_ futIntTy_ x)],
    ret = futIntTy_,
    body = futBindall_ [
      nuFutLet_ y (futApp_ (futConst_ (FCLength ())) (nFutVar_ s)),
      futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, futInt_ 1]],
    info = NoInfo ()}]} in
let expected = FProg {decls = [
  FDeclFun {
    ident = f, entry = true, typeParams = [FPSize {val = x}],
    params = [(s, futSizedArrayTy_ futIntTy_ x)],
    ret = futIntTy_,
    body = futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, futInt_ 1],
    info = NoInfo ()}]} in
utest printFutProg (parameterizeLength t) with printFutProg expected using eqString in

()
