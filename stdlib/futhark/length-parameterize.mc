-- Translates variables containing the result of applying the length constant
-- on a function parameter into a size parameter. This helps the Futhark
-- compiler with inference of array sizes.

include "map.mc"
include "name.mc"
include "futhark/ast.mc"
include "futhark/pprint.mc"

type LengthParameterizeEnv = {
  params : Map Name FutType,
  typeParams : Map Name FutTypeParam
}

lang FutharkLengthParameterize = FutharkAst
  sem parameterizeLengthExpr (env : LengthParameterizeEnv) =
  | FEApp ({lhs = FEConst {val = FCLength ()},
            rhs = FEVar {ident = s}} & t) ->
    let lengthParamVar = lam ident. lam info.
      FEVar {ident = ident, ty = FTyInt {info = info}, info = info}
    in
    match mapLookup s env.params with Some (FTyArray tyArray) then
      match tyArray.dim with Some n then
        (env, lengthParamVar n tyArray.info)
      else
        let n = nameSym "n" in
        let newParamType = FTyArray {tyArray with dim = Some n} in
        let typeParam = FPSize {val = n} in
        let typeParams = mapInsert n typeParam env.typeParams in
        let env = {{env with params = mapInsert s newParamType env.params}
                        with typeParams = typeParams} in
        (env, lengthParamVar n tyArray.info)
    else smapAccumL_FExpr_FExpr parameterizeLengthExpr env (FEApp t)
  | t -> smapAccumL_FExpr_FExpr parameterizeLengthExpr env t

  sem parameterizeLengthDecl =
  | FDeclFun t ->
    let nameAndType : FutTypeParam -> (Name, FutTypeParam) = lam typeParam.
      let typeParamName =
        match typeParam with FPSize {val = id} then id
        else match typeParam with FPType {val = id} then id
        else never in
      (typeParamName, typeParam)
    in
    let env = {params = mapFromSeq nameCmp t.params,
               typeParams = mapFromSeq nameCmp (map nameAndType t.typeParams)} in
    match parameterizeLengthExpr env t.body with (env, body) then
      let env : LengthParameterizeEnv = env in
      FDeclFun {{{t with body = body}
                    with params = mapBindings env.params}
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
    body = futBindall_ [
      nuFutLet_ x (nFutVar_ n),
      futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, futInt_ 1]
    ],
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
    body = futBindall_ [
      nuFutLet_ y (nFutVar_ x),
      futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, futInt_ 1]],
    info = NoInfo ()}]} in
utest printFutProg (parameterizeLength t) with printFutProg expected using eqString in

()
