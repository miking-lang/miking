include "ast.mc"
include "ast-builder.mc"
include "pprint.mc"

include "set.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/cmp.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "pmexpr/ast.mc"
include "pmexpr/utils.mc"

let extMap = mapFromSeq cmpString
  [("externalSin", "f64.sin"), ("externalCos", "f64.cos")]

type FutharkGenerateEnv = use Ast in {
  entryPoints : Set Name,
  boundNames : Map Name Expr
}

lang FutharkConstGenerate = MExprAst + FutharkAst
  sem generateConst (info : Info) =
  | CInt n -> FCInt {val = n.val, sz = Some (I64 ())}
  | CFloat f -> FCFloat {val = f.val, sz = Some (F64 ())}
  | CBool b -> FCBool {val = b.val}
  | CChar c -> FCInt {val = char2int c.val, sz = Some (I64 ())}
  | CAddi _ | CAddf _ -> FCAdd ()
  | CSubi _ | CSubf _ -> FCSub ()
  | CMuli _ | CMulf _ -> FCMul ()
  | CDivi _ | CDivf _ -> FCDiv ()
  | CNegi _ -> FCNegi ()
  | CNegf _ -> FCNegf ()
  | CModi _ -> FCRem ()
  | CInt2float _ -> FCInt2Float ()
  | CEqi _ | CEqf _ | CEqc _ -> FCEq ()
  | CNeqi _ | CNeqf _ -> FCNeq ()
  | CGti _ | CGtf _ -> FCGt ()
  | CLti _ | CLtf _ -> FCLt ()
  | CGeqi _ | CGeqf _ -> FCGeq ()
  | CLeqi _ | CLeqf _ -> FCLeq ()
  | CCreate _ -> FCTabulate ()
  | CLength _ -> FCLength ()
  | CReverse _ -> FCReverse ()
  | CConcat _ -> FCConcat ()
  | CHead _ -> FCHead ()
  | CTail _ -> FCTail ()
  | CNull _ -> FCNull ()
  | CMap _ -> FCMap ()
  | CFoldl _ -> FCFoldl ()
  | c -> errorSingle [info] "Constant is not supported by the Futhark backend"
end

lang FutharkTypeGenerate = MExprAst + FutharkAst
  sem generateType : FutharkGenerateEnv -> Type -> FutType
  sem generateType env =
  | TyInt t -> FTyInt {info = t.info, sz = I64 ()}
  | TyFloat t -> FTyFloat {info = t.info, sz = F64 ()}
  | TyBool t -> FTyBool {info = t.info}
  | TyChar t -> FTyInt {info = t.info, sz = I64 ()}
  | TySeq t ->
    -- NOTE(larshum, 2021-12-01): We generate an identifier for the size type
    -- of every array type. These identifiers are extracted at a later stage to
    -- declare the size type parameters.
    let dimId = nameSym "n" in
    FTyArray {elem = generateType env t.ty, dim = Some (NamedDim dimId), info = t.info}
  | TyRecord t ->
    FTyRecord {fields = mapMap (generateType env) t.fields, info = t.info}
  | TyArrow t ->
    FTyArrow {from = generateType env t.from, to = generateType env t.to,
              info = t.info}
  | TyVar t ->
    FTyIdent {ident = t.ident, info = t.info}
  | TyAll t ->
    FTyAll {ident = t.ident, ty = generateType env t.ty, info = t.info}
  | TyAlias t ->
    generateType env t.content
  | TyUnknown t ->
    errorSingle [t.info] "Unknown types are not supported by the Futhark backend"
  | TyVariant t ->
    errorSingle [t.info] "Variant types are not supported by the Futhark backend"
  | t ->
    let tyStr = use MExprPrettyPrint in type2str t in
    errorSingle [infoTy t]
      (join ["Terms of type '", tyStr, "' are not supported by the Futhark backend"])
end

lang FutharkPatternGenerate = MExprAst + FutharkAst + FutharkTypeGenerate
  sem generatePattern (env : FutharkGenerateEnv) (targetTy : Type) =
  | PatNamed t ->
    FPNamed {ident = t.ident, ty = generateType env t.ty, info = t.info}
  | PatInt t ->
    FPInt {val = t.val, ty = generateType env t.ty, info = t.info}
  | PatBool t ->
    FPBool {val = t.val, ty = generateType env t.ty, info = t.info}
  | PatChar t ->
    FPInt {val = char2int t.val, ty = generateType env t.ty, info = t.info}
  | PatRecord t ->
    let mergeBindings = lam bindings : Map SID Pat. lam fields : Map SID Type.
      mapMapWithKey
        (lam k. lam ty : Type.
          match mapLookup k bindings with Some pat then
            generatePattern env ty pat
          else futPvarw_ ())
        fields
    in
    match unwrapType targetTy with TyRecord {fields = fields} then
      FPRecord {bindings = mergeBindings t.bindings fields,
                ty = generateType env t.ty, info = t.info}
    else
      let tyStr = use MExprPrettyPrint in type2str targetTy in
      errorSingle [t.info] (join ["Term of non-record type '", tyStr,
                                  "' cannot be matched with record pattern"])
  | p ->
    errorSingle [infoPat p] "Pattern is not supported by Futhark backend"
end

lang FutharkGenerate = Ast + FutharkExprAst
  sem generateExpr : FutharkGenerateEnv -> Expr -> FutExpr
end

lang FutharkMatchGenerate = MExprAst + FutharkAst + FutharkPatternGenerate +
                            FutharkTypeGenerate + FutharkTypePrettyPrint +
                            FutharkGenerate
  sem defaultGenerateMatch (env : FutharkGenerateEnv) =
  | TmMatch t ->
    errorSingle [t.info] (join ["Match expression not supported by the Futhark backend"])

  sem generateExpr (env : FutharkGenerateEnv) =
  | TmMatch ({pat = PatBool {val = true}} & t) ->
    FEIf {cond = generateExpr env t.target, thn = generateExpr env t.thn,
          els = generateExpr env t.els, ty = generateType env t.ty,
          info = t.info}
  | TmMatch ({pat = PatBool {val = false}} & t) ->
    FEIf {cond = generateExpr env t.target, thn = generateExpr env t.els,
          els = generateExpr env t.thn, ty = generateType env t.ty,
          info = t.info}
  | TmMatch ({pat = PatInt _ | PatChar _} & t) ->
    let condInfo = mergeInfo (infoTm t.target) (infoPat t.pat) in
    let resultTy = FTyBool {info = condInfo} in
    let eqiAppTy = FTyArrow {
      from = FTyInt {info = condInfo, sz = I64 ()}, to = resultTy, info = condInfo} in
    let eqiTy = FTyArrow {
      from = FTyInt {info = condInfo, sz = I64 ()}, to = eqiAppTy, info = condInfo} in
    let lhsConstVal =
      match t.pat with PatInt {val = i} then
        FCInt {val = i, sz = Some (I64 ())}
      else match t.pat with PatChar {val = c} then
        FCInt {val = char2int c, sz = Some (I64 ())}
      else never in
    let condExpr = FEApp {
      lhs = FEApp {
        lhs = FEConst {val = FCEq (), ty = eqiTy, info = condInfo},
        rhs = FEConst {val = lhsConstVal, ty = FTyInt {info = condInfo, sz = I64 ()},
                       info = condInfo},
        ty = eqiAppTy, info = condInfo},
      rhs = generateExpr env t.target,
      ty = resultTy, info = condInfo} in
    FEIf {cond = condExpr, thn = generateExpr env t.thn,
          els = generateExpr env t.els, ty = generateType env t.ty,
          info = t.info}
  | TmMatch ({pat = PatNamed {ident = PWildcard _}} & t) -> generateExpr env t.thn
  | TmMatch ({pat = PatNamed {ident = PName n}} & t) ->
    FELet {ident = n, tyBody = generateType env (tyTm t.target),
           body = generateExpr env t.target, inexpr = generateExpr env t.thn,
           ty = generateType env (tyTm t.thn), info = infoTm t.target}
  | TmMatch ({pat = PatRecord {bindings = bindings} & pat, els = TmNever _} & t) ->
    let defaultGenerateRecordMatch = lam.
      FEMatch {
        target = generateExpr env t.target,
        cases = [(generatePattern env (tyTm t.target) pat, generateExpr env t.thn)],
        ty = generateType env t.ty,
        info = t.info} in
    let binds : [(SID, Pat)] = mapBindings bindings in
    match t.thn with TmVar {ident = exprName} then
      match binds with [(fieldLabel, PatNamed {ident = PName patName})] then
        if nameEq patName exprName then
          FEProj {target = generateExpr env t.target, label = fieldLabel,
                  ty = generateType env t.ty, info = t.info}
        else defaultGenerateRecordMatch ()
      else defaultGenerateRecordMatch ()
    else defaultGenerateRecordMatch ()
  | TmMatch ({pat = PatSeqEdge {prefix = [PatNamed {ident = PName head}],
                                middle = PName tail, postfix = []},
              els = TmNever _} & t) ->
    let target = generateExpr env t.target in
    let targetTy = generateType env (tyTm t.target) in
    match targetTy with FTyArray {elem = elemTy} then
      FELet {
        ident = head,
        tyBody = elemTy,
        body = FEApp {
          lhs = FEConst {
            val = FCHead (),
            ty = FTyArrow {from = elemTy, to = targetTy, info = t.info},
            info = t.info},
          rhs = target, ty = elemTy, info = t.info},
        inexpr = FELet {
          ident = tail,
          tyBody = targetTy,
          body = FEApp {
            lhs = FEConst {
              val = FCTail (),
              ty = FTyArrow {from = targetTy, to = targetTy, info = t.info},
              info = t.info},
            rhs = target, ty = targetTy, info = t.info},
          inexpr = generateExpr env t.thn,
          ty = generateType env (tyTm t.thn),
          info = t.info},
        ty = generateType env (tyTm t.thn),
        info = t.info}
    else
      use FutharkTypePrettyPrint in
      match pprintType 0 pprintEnvEmpty targetTy with (_, tyStr) in
      errorSingle [t.info] (join ["Term of non-sequence type '", tyStr,
                                  "' cannot be matched on sequence pattern"])
  | (TmMatch _) & t -> defaultGenerateMatch env t
end

lang FutharkAppGenerate = MExprAst + FutharkAst + FutharkTypeGenerate +
                          PMExprVariableSub + FutharkGenerate
  sem defaultGenerateApp (env : FutharkGenerateEnv) =
  | TmApp t -> FEApp {lhs = generateExpr env t.lhs, rhs = generateExpr env t.rhs,
                      ty = generateType env t.ty, info = t.info}

  sem generateExpr (env : FutharkGenerateEnv) =
  | TmApp ({lhs = TmApp {lhs = TmConst {val = CGet _}, rhs = arg1}, rhs = arg2} & t) ->
    FEArrayAccess {
      array = generateExpr env arg1, index = generateExpr env arg2,
      ty = generateType env t.ty, info = t.info}
  | TmApp ({lhs = TmApp {lhs = TmApp {lhs = TmConst {val = CSet _},
                                      rhs = arg1},
                         rhs = arg2},
            rhs = arg3} & t) ->
    let arrayTy = generateType env t.ty in
    -- NOTE(larshum, 2021-09-27): In-place updates in Futhark require that the
    -- array is not aliased. As MExpr performs no alias analysis, we instead
    -- add an explicit copy of the target array.
    let arrayCopy = FEApp {
      lhs = FEConst {
        val = FCCopy (),
        ty = FTyArrow {from = arrayTy, to = arrayTy, info = t.info},
        info = t.info},
      rhs = generateExpr env arg1,
      ty = arrayTy,
      info = t.info} in
    FEArrayUpdate {
      array = arrayCopy, index = generateExpr env arg2,
      value = generateExpr env arg3, ty = arrayTy, info = t.info}
  | TmApp ({lhs = TmApp {lhs = TmConst {val = CCreate _}, rhs = arg1},
            rhs = arg2} & t) ->
    let tryLookupExpr = lam e.
      match e with TmVar t then
        optionGetOrElse
          (lam. e)
          (mapLookup t.ident env.boundNames)
      else e
    in
    let argx1 = tryLookupExpr arg1 in
    let argx2 = tryLookupExpr arg2 in
    let result =
      match argx2 with TmLam {ident = i, body = body} then
        match body with TmVar {ident = id} then
          if nameEq i id then
            match argx1 with TmApp {lhs = TmConst {val = CLength _}, rhs = seq} then
              futIndices_ (generateExpr env seq)
            else futIota_ (generateExpr env arg1)
          else futReplicate_ (generateExpr env arg1) (generateExpr env body)
        else match body with TmConst _ then
          futReplicate_ (generateExpr env arg1) (generateExpr env body)
        else defaultGenerateApp env (TmApp t)
      else defaultGenerateApp env (TmApp t)
    in
    let resultType = generateType env t.ty in
    withTypeFutTm resultType (withInfoFutTm t.info result)
  | TmApp ({lhs = TmApp {lhs = TmApp {lhs = TmConst {val = CSubsequence _},
                                      rhs = arg1},
                         rhs = arg2},
            rhs = arg3} & t) ->
    let startIdx = generateExpr env arg2 in
    let offset = generateExpr env arg3 in
    let info = mergeInfo (infoFutTm startIdx) (infoFutTm offset) in
    let endIdx =
      match startIdx with FEConst {val = FCInt {val = 0}} then offset
      else
        FEApp {
          lhs = FEApp {
            lhs = FEConst {val = FCAdd (), ty = futUnknownTy_, info = info},
            rhs = startIdx,
            ty = FTyArrow {
              from = FTyInt {info = info, sz = I64 ()},
              to = FTyInt {info = info, sz = I64 ()}, info = info},
            info = info
          },
          rhs = offset,
          ty = FTyInt {info = info, sz = I64 ()},
          info = info} in
    FEArraySlice {
      array = generateExpr env arg1, startIdx = startIdx, endIdx = endIdx,
      ty = generateType env t.ty, info = t.info}
  | TmApp {lhs = TmConst {val = CFloorfi _}, rhs = arg, info = info} ->
    FEApp {
      lhs = FEConst {
        val = FCFloat2Int (),
        ty = FTyArrow {from = FTyFloat {info = info, sz = F64 ()},
                       to = FTyInt {info = info, sz = I64 ()}, info = info},
        info = info},
      rhs = FEApp {
        lhs = FEConst {
          val = FCFloatFloor (),
          ty = FTyArrow {from = FTyFloat {info = info, sz = F64 ()},
                         to = FTyFloat {info = info, sz = F64 ()}, info = info},
          info = info},
        rhs = generateExpr env arg,
        ty = FTyFloat {info = info, sz = F64 ()},
        info = info},
      ty = FTyInt {info = info, sz = I64 ()},
      info = info}
  | TmApp ({
      lhs = TmApp {
        lhs = TmApp {
          lhs = TmConst {val = CFoldl _},
          rhs = f},
        rhs = ne},
      rhs = s} & t) ->
    let acc = nameSym "acc" in
    let x = nameSym "x" in
    let funcTy = generateType env (tyTm f) in
    let accTy = generateType env t.ty in
    let seqTy = generateType env (tyTm s) in
    let elemTy =
      match funcTy with FTyArrow {to = FTyArrow {to = elemTy}} then
        elemTy
      else errorSingle [t.info] "Invalid type of function passed to foldl" in
    let param : (FutPat, FutExpr) =
      ( FPNamed {ident = PName acc, ty = accTy, info = t.info},
        generateExpr env ne ) in
    let constructForEach : FutExpr -> Name -> FutExpr = lam body. lam x.
      FEForEach {
        param = param, loopVar = x, seq = generateExpr env s, body = body,
        ty = accTy, info = t.info}
    in
    -- NOTE(larshum, 2021-09-29): If the body consists of lambdas, eliminate
    -- them by substitution. This can only happen because of a pattern
    -- transformation, as lambda lifting would have eliminated it otherwise.
    match f with TmLam {ident = accLam, body = TmLam {ident = x, body = body}} then
      -- Substitute 'acc' with 'ne' in the function body, and use the 'x' bound
      -- in the lambda.
      let subMap = mapFromSeq nameCmp [
        (accLam, lam info. TmVar {ident = acc, ty = t.ty, info = info,
                                  frozen = false})] in
      let body = substituteVariables subMap body in
      let futBody = generateExpr env body in
      constructForEach futBody x
    else
      let forBody =
        FEApp {
          lhs = FEApp {
            lhs = generateExpr env f,
            rhs = FEVar {ident = acc, ty = accTy, info = t.info},
            ty = FTyArrow {from = elemTy, to = accTy, info = t.info},
            info = t.info},
          rhs = FEVar {ident = x, ty = elemTy, info = t.info},
          ty = accTy, info = t.info} in
      constructForEach forBody x
  | (TmApp _) & t -> defaultGenerateApp env t
end

lang FutharkExprGenerate = FutharkConstGenerate + FutharkTypeGenerate +
                           FutharkMatchGenerate + FutharkAppGenerate +
                           PMExprAst + FutharkGenerate
  sem generateExpr (env : FutharkGenerateEnv) =
  | TmVar t ->
    -- NOTE(larshum, 2022-08-15): Special-case handling of external functions.
    match mapLookup (nameGetStr t.ident) extMap with Some str then
      FEVarExt {ident = str, ty = generateType env t.ty, info = t.info}
    else FEVar {ident = t.ident, ty = generateType env t.ty, info = t.info}
  | TmRecord t ->
    FERecord {fields = mapMap (generateExpr env) t.bindings,
              ty = generateType env t.ty, info = t.info}
  | TmRecordUpdate t ->
    FERecordUpdate {rec = generateExpr env t.rec, key = t.key,
                    value = generateExpr env t.value,
                    ty = generateType env t.ty, info = t.info}
  | TmSeq t ->
    FEArray {tms = map (generateExpr env) t.tms, ty = generateType env t.ty,
             info = t.info}
  | TmConst t ->
    FEConst {val = generateConst t.info t.val, ty = generateType env t.ty,
             info = t.info}
  | TmLam t ->
    FELam {ident = t.ident, body = generateExpr env t.body,
           ty = generateType env t.ty, info = t.info}
  | TmLet t ->
    let boundNames = mapInsert t.ident t.body env.boundNames in
    let inexprEnv = {env with boundNames = boundNames} in
    FELet {ident = t.ident, tyBody = generateType env t.tyBody,
           body = generateExpr env t.body,
           inexpr = generateExpr inexprEnv t.inexpr,
           ty = generateType env t.ty, info = t.info}
  | TmFlatten t ->
    withTypeFutTm
      (generateType env t.ty)
      (withInfoFutTm t.info (futFlatten_ (generateExpr env t.e)))
  | TmMap2 t ->
    withTypeFutTm
      (generateType env t.ty)
      (withInfoFutTm t.info (futMap2_ (generateExpr env t.f)
                                      (generateExpr env t.as)
                                      (generateExpr env t.bs)))
  | TmParallelReduce t ->
    withTypeFutTm
      (generateType env t.ty)
      (withInfoFutTm t.info (futReduce_ (generateExpr env t.f)
                                        (generateExpr env t.ne)
                                        (generateExpr env t.as)))
  | TmParallelSizeCoercion t ->
    let ty = generateType env t.ty in
    match ty with FTyArray aty then
      FESizeCoercion {
        e = generateExpr env t.e, ty = FTyArray {aty with dim = Some (NamedDim t.size)},
        info = t.info}
    else errorSingle [t.info] (join ["Size coercion could not be generated ",
                                     "due to unexpected type of sequence"])
  | TmParallelSizeEquality t ->
    FESizeEquality {x1 = t.x1, d1 = t.d1, x2 = t.x2, d2 = t.d2,
                    ty = generateType env t.ty, info = t.info}
  | TmRecLets t ->
    errorSingle [t.info] "Recursive functions are not supported by the Futhark backend"
  | t ->
    errorSingle [infoTm t] "Term is not supported by the Futhark backend"
end

lang FutharkToplevelGenerate = FutharkExprGenerate + FutharkConstGenerate +
                               FutharkTypeGenerate
  sem collectTypeParams : [FutTypeParam] -> FutType -> [FutTypeParam]
  sem collectTypeParams acc =
  | FTyArray {elem = elem, dim = Some (NamedDim id)} ->
    let acc = cons (FPSize {val = id}) acc in
    sfold_FType_FType collectTypeParams acc elem
  | ty ->
    sfold_FType_FType collectTypeParams acc ty

  sem _collectParams : FutharkGenerateEnv -> (FutExpr, FutType) -> ([(Name, FutType)], [FutTypeParam])
  sem _collectParams env =
  | (body, ty) ->
    recursive let collectParamIds = lam acc. lam body.
      match body with FELam t then collectParamIds (snoc acc t.ident) t.body
      else acc
    in
    recursive let collectParamTypes = lam ty.
      recursive let work = lam acc. lam ty.
        match ty with FTyArrow {from = from, to = to} then
          work (cons from acc) to
        else cons ty acc
      in
      match ty with FTyAll t then
        collectParamTypes t.ty
      else
        reverse (tail (work [] ty))
    in
    recursive let collectTyAllParams = lam acc. lam ty.
      match ty with FTyAll t then
        collectTyAllParams (cons (FPType {val = t.ident}) acc) t.ty
      else acc
    in
    let paramIds = collectParamIds [] body in
    let paramTypes = collectParamTypes ty in
    let typeParams =
      foldl collectTypeParams (collectTyAllParams [] ty) paramTypes
    in
    (zip paramIds paramTypes, typeParams)

  sem generateToplevel : FutharkGenerateEnv -> Expr -> [FutDecl]
  sem generateToplevel env =
  | TmType t ->
    generateToplevel env t.inexpr
  | TmLet t ->
    recursive let findReturnType = lam params. lam ty.
      if null params then ty
      else
        match ty with TyArrow {to = to} then
          findReturnType (tail params) to
        else
          errorSingle [t.info] (join ["Function takes more parameters than ",
                                      "specified in return type"])
    in
    recursive let stripLambdas = lam e.
      match e with FELam t then stripLambdas t.body else e
    in
    let decl =
      let body = generateExpr env t.body in
      let tyBody = generateType env t.tyBody in
      match _collectParams env (body, tyBody) with (params, typeParams) in
      if null params then
        -- NOTE(larshum, 2021-12-01): The generation currently does not support
        -- type parameters in constant declarations.
        FDeclConst {ident = t.ident, ty = tyBody, val = body, info = t.info}
      else
        let retTy = generateType env (findReturnType params (inspectType t.tyBody)) in
        let entry = setMem t.ident env.entryPoints in
        let typeParams = collectTypeParams typeParams retTy in
        FDeclFun {ident = t.ident, entry = entry, typeParams = typeParams,
                  params = params, ret = retTy,
                  body = stripLambdas body, info = t.info}
    in
    cons decl (generateToplevel env t.inexpr)
  | TmRecLets t ->
    errorSingle [t.info] "Recursive functions are not supported by the Futhark backend"
  | TmExt t ->
    match mapLookup (nameGetStr t.ident) extMap with Some str then
      generateToplevel env t.inexpr
    else
      errorSingle [t.info] "External functions are not supported by the Futhark backend"
  | TmUtest t ->
    -- NOTE(larshum, 2021-11-25): This case should never be reached, as utests
    -- are removed/replaced in earlier stages of the compilation.
    errorSingle [t.info] "Utests are not supported by the Futhark backend"
  | TmConDef t ->
    errorSingle [t.info] "Constructor definitions are not supported by the Futhark backend"
  | _ -> []
end

lang FutharkGenerate = FutharkToplevelGenerate + MExprCmp
  sem generateProgram (entryPoints : Set Name) =
  | prog ->
    let emptyEnv = {
      entryPoints = entryPoints,
      boundNames = mapEmpty nameCmp
    } in
    FProg {decls = generateToplevel emptyEnv prog}
end

lang TestLang =
  FutharkGenerate + FutharkPrettyPrint + MExprSym + MExprTypeCheck
end

mexpr

use TestLang in

let f = nameSym "f" in
let c = nameSym "c" in
let chars = typeCheck (bindall_ [
  nlet_ f (tyarrows_ [tychar_, tybool_]) (nlam_ c tychar_ (
    match_ (nvar_ c) (pchar_ 'a')
      true_
      false_)),
  app_ (nvar_ f) (char_ 'x')]) in

let charsExpected = FProg {decls = [
  FDeclFun {
    ident = f, entry = false, typeParams = [],
    params = [(c, futIntTy_)], ret = futBoolTy_,
    body =
      futIf_
        (futAppSeq_ (futConst_ (FCEq ())) [futInt_ (char2int 'a'), nFutVar_ c])
        (futConst_ (FCBool {val = true}))
        (futConst_ (FCBool {val = false})),
    info = NoInfo ()}]} in

let entryPoints = setOfSeq nameCmp [] in
utest printFutProg (generateProgram entryPoints chars)
with printFutProg charsExpected using eqSeq eqc in

let intseq = nameSym "intseq" in
let n = nameSym "n" in
let floatseq = nameSym "floatseq" in
let n2 = nameSym "n" in
let a = nameSym "a" in
let b = nameSym "b" in
let c = nameSym "c" in
let f = nameSym "f" in
let a2 = nameSym "a" in
let b2 = nameSym "b" in
let g = nameSym "g" in
let r = nameSym "r" in
let f2 = nameSym "f" in
let min = nameSym "min" in
let a3 = nameSym "a" in
let b3 = nameSym "b" in
let map = nameSym "map" in
let f3 = nameSym "f" in
let s = nameSym "s" in

let t = typeCheck (bindall_ [
  ntype_ intseq [] (tyseq_ tyint_),
  ntype_ floatseq [] (tyseq_ tyfloat_),
  nlet_ a (ntycon_ intseq) (seq_ [int_ 1, int_ 2, int_ 3]),
  nlet_ b (ntycon_ floatseq) (seq_ [float_ 2.718, float_ 3.14]),
  nlet_ c (tyrecord_ [("a", tyint_), ("b", tyfloat_)])
           (record_ (tyrecord_ [("a", tyint_), ("b", tyfloat_)])
                    [("a", int_ 3), ("b", float_ 2.0)]),
  nlet_ f (tyarrows_ [tyint_, tyint_, tyint_])
           (nlam_ a2 tyint_ (nlam_ b2 tyint_ (addi_ (nvar_ a2) (nvar_ b2)))),
  nlet_ g (tyarrows_ [ntycon_ floatseq, tyfloat_, tyfloat_])
            (nlam_ r (ntycon_ floatseq)
              (nlam_ f2 tyfloat_ (addf_ (nvar_ f2) (get_ (nvar_ r) (int_ 0))))),
  nlet_ min (tyarrows_ [tyint_, tyint_, tyint_])
             (nlam_ a3 tyint_ (nlam_ b3 tyint_ (
               if_ (geqi_ (nvar_ a3) (nvar_ b3)) (nvar_ b3) (nvar_ a3)))),
  nlet_ map (tyarrows_ [tyarrow_ tyint_ tyint_, ntycon_ intseq, ntycon_ intseq])
             (nlam_ f3 (tyarrow_ tyint_ tyint_) (nlam_ s (ntycon_ intseq)
               (map_ (nvar_ f3) (nvar_ s)))),
  unit_]) in

let intSeqType = lam n. FTyArray {
  elem = FTyInt {info = NoInfo (), sz = I64 ()}, dim = Some (NamedDim n), info = NoInfo ()
} in
let floatSeqType = lam n. FTyArray {
  elem = FTyFloat {info = NoInfo (), sz = F64 ()}, dim = Some (NamedDim n), info = NoInfo ()
} in
let ns = create 5 (lam. nameSym "n") in
let expected = FProg {decls = [
  FDeclConst {
    ident = a, ty = intSeqType (get ns 0),
    val = futArray_ [futInt_ 1, futInt_ 2, futInt_ 3], info = NoInfo ()},
  FDeclConst {
    ident = b, ty = floatSeqType (get ns 1),
    val = futArray_ [futFloat_ 2.718, futFloat_ 3.14], info = NoInfo ()},
  FDeclConst {
    ident = c, ty = futRecordTy_ [("a", futIntTy_), ("b", futFloatTy_)],
    val = futRecord_ [("a", futInt_ 3), ("b", futFloat_ 2.0)],
    info = NoInfo ()},
  FDeclFun {
    ident = f, entry = true, typeParams = [],
    params = [(a2, futIntTy_), (b2, futIntTy_)], ret = futIntTy_,
    body = futAdd_ (nFutVar_ a2) (nFutVar_ b2),
    info = NoInfo ()},
  FDeclFun {
    ident = g, entry = true, typeParams = [FPSize {val = get ns 2}],
    params = [(r, floatSeqType (get ns 2)), (f2, futFloatTy_)], ret = futFloatTy_,
    body =
      futAdd_ (nFutVar_ f2) (futArrayAccess_ (nFutVar_ r) (futInt_ 0)),
    info = NoInfo ()},
  FDeclFun {
    ident = min, entry = true, typeParams = [],
    params = [(a3, futIntTy_), (b3, futIntTy_)], ret = futIntTy_,
    body =
      futIf_ (futAppSeq_ (futConst_ (FCGeq ())) [nFutVar_ a3, nFutVar_ b3])
        (nFutVar_ b3)
        (nFutVar_ a3),
    info = NoInfo ()},
  FDeclFun {
    ident = map, entry = false, typeParams = [FPSize {val = get ns 3}, FPSize {val = get ns 4}],
    params = [(f3, futArrowTy_ futIntTy_ futIntTy_), (s, intSeqType (get ns 4))],
    ret = intSeqType (get ns 3),
    body = futAppSeq_ (futConst_ (FCMap ())) [nFutVar_ f3, nFutVar_ s],
    info = NoInfo ()}
]} in
let entryPoints = setOfSeq nameCmp [f, g, min] in
utest printFutProg (generateProgram entryPoints t) with printFutProg expected
using eqSeq eqc in

let acc = nameSym "acc" in
let x = nameSym "x" in
let y = nameSym "y" in
let n = nameSym "n" in
let foldlToFor = typeCheck
  (nlet_ f (tyarrows_ [tyseq_ tyint_, tyint_]) (
    nlam_ s (tyseq_ tyint_) (
      foldl_
        (nlam_ acc tyint_ (nlam_ y tyint_ (
          addi_ (nvar_ acc) (nvar_ y))))
        (int_ 0) (nvar_ s)))) in
let expected = FProg {decls = [
  FDeclFun {
    ident = f, entry = true, typeParams = [FPSize {val = n}],
    params = [(s, futSizedArrayTy_ futIntTy_ n)], ret = futIntTy_,
    body =
      futForEach_
        (nFutPvar_ acc, futInt_ 0)
        y (nFutVar_ s) (futAdd_ (nFutVar_ acc) (nFutVar_ y)),
    info = NoInfo ()}]} in
let entryPoints = setOfSeq nameCmp [f] in
utest printFutProg (generateProgram entryPoints foldlToFor)
with printFutProg expected using eqSeq eqc in

let negation = typeCheck
  (nlet_ f (tyarrows_ [tyint_, tyfloat_, tyrecord_ [("a", tyint_), ("b", tyfloat_)]])
    (nlam_ a tyint_ (nlam_ b tyfloat_ (
      urecord_ [("a", negi_ (nvar_ a)), ("b", negf_ (nvar_ b))])))) in
let expected = FProg {decls = [
  FDeclFun {
    ident = f, entry = false, typeParams = [],
    params = [(a, futIntTy_), (b, futFloatTy_)],
    ret = futRecordTy_ [("a", futIntTy_), ("b", futFloatTy_)],
    body = futRecord_ [
      ("a", futApp_ (futConst_ (FCNegi ())) (nFutVar_ a)),
      ("b", futApp_ (futConst_ (FCNegf ())) (nFutVar_ b))],
    info = NoInfo ()}]} in
let entryPoints = setEmpty nameCmp in
utest printFutProg (generateProgram entryPoints negation)
with printFutProg expected using eqSeq eqc in

let recordTy = tyrecord_ [("a", tyint_), ("b", tyfloat_)] in
let recordPat = prec_ [("a", npvar_ a), ("b", npvar_ b)] in
let recordMatchNotProj = typeCheck
  (nlet_ f (tyarrows_ [recordTy, tyint_])
    (nlam_ x recordTy
      (match_ (nvar_ x) recordPat
        (nvar_ a)
        never_))) in
let expected = FProg {decls = [
  FDeclFun {
    ident = f, entry = false, typeParams = [],
    params = [(x, futRecordTy_ [("a", futIntTy_), ("b", futFloatTy_)])],
    ret = futIntTy_,
    body =
      futMatch_
        (nFutVar_ x)
        [(futPrecord_ [("a", nFutPvar_ a), ("b", nFutPvar_ b)], nFutVar_ a)],
    info = NoInfo ()}]} in
utest printFutProg (generateProgram (setEmpty nameCmp) recordMatchNotProj)
with printFutProg expected using eqString in

let extSinId = nameSym "externalSin" in
let sinId = nameSym "sin" in
let x = nameSym "x" in
let extDefn = typeCheck (bindall_ [
  next_ extSinId false (tyarrow_ tyfloat_ tyfloat_),
  nulet_ sinId (nlam_ x tyfloat_ (app_ (nvar_ extSinId) (nvar_ x)))]) in
let expected = FProg {decls = [
  FDeclFun {
    ident = sinId, entry = false, typeParams = [],
    params = [(x, futFloatTy_)], ret = futFloatTy_,
    body = futApp_ (futVarExt_ "f64.sin") (nFutVar_ x),
    info = NoInfo ()}]} in
utest printFutProg (generateProgram (setEmpty nameCmp) extDefn)
with printFutProg expected using eqString in

()
