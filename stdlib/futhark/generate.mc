include "ast.mc"
include "ast-builder.mc"
include "digraph.mc"
include "pprint.mc"

include "set.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/cmp.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/rewrite/parallel-keywords.mc"
include "mexpr/rewrite/utils.mc"

type FutharkGenerateEnv = {
  entryPoints : Set Name,
  typeAliases : Map Type Name,
  typeParams : Map Name [FutTypeParam],
  boundNames : Map Name Expr
}

recursive let _isHigherOrderFunction = use FutharkAst in
  lam params : [(Name, FutType)].
  match params with [] then
    false
  else match params with [(_, ty)] ++ t then
    match ty with FTyArrow _ then
      true
    else _isHigherOrderFunction t
  else never
end

recursive let _getTrailingSelfRecursiveCallParams = use MExprAst in
  lam funcIdent : Name. lam body : Expr.
  match body with TmLet {inexpr = inexpr} then
    _getTrailingSelfRecursiveCallParams funcIdent inexpr
  else match body with TmRecLets {inexpr = inexpr} then
    _getTrailingSelfRecursiveCallParams funcIdent inexpr
  else
    recursive let collectAppArgs = lam args : [Expr]. lam e : Expr.
      match e with TmApp {lhs = lhs, rhs = rhs} then
        let args = cons rhs args in
        match lhs with TmVar {ident = id} then
          if nameEq funcIdent id then Some args
          else None ()
        else
          collectAppArgs args lhs
      else None ()
    in
    collectAppArgs [] body
end

let _constructLoopResult = use MExprAst in
  lam functionParams : [(Name, a)].
  lam recursiveCallParams : [Expr].
  lam baseCase : Expr.
  let updatedParams : Map Name Expr =
    mapFromSeq
      nameCmp
      (mapi
        (lam i. lam p : (Name, a).
          (p.0, get recursiveCallParams i)) functionParams) in
  recursive let work = lam e : Expr.
    match e with TmVar t then
      optionGetOrElse (lam. e) (mapLookup t.ident updatedParams)
    else smap_Expr_Expr work e
  in
  work baseCase

let _usePassedParameters = use MExprAst in
  lam functionParams : [(Name, a)].
  lam passedParams : [Expr].
  lam body : Expr.
  let paramMap : Map Name Expr =
    mapFromSeq
      nameCmp
      (mapi
        (lam i. lam p : (Name, a).
          (p.0, get passedParams i))
        (subsequence functionParams 0 (length passedParams))) in
  recursive let work = lam e : Expr.
    match e with TmVar t then
      optionGetOrElse (lam. e) (mapLookup t.ident paramMap)
    else smap_Expr_Expr work e
  in
  work body

lang FutharkConstGenerate = MExprAst + FutharkAst
  sem generateConst =
  | CInt n -> FCInt {val = n.val}
  | CFloat f -> FCFloat {val = f.val}
  | CAddi _ | CAddf _ -> FCAdd ()
  | CSubi _ | CSubf _ -> FCSub ()
  | CMuli _ | CMulf _ -> FCMul ()
  | CDivi _ | CDivf _ -> FCDiv ()
  | CModi _ -> FCRem ()
  | CEqi _ | CEqf _ -> FCEq ()
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
end

lang FutharkTypeGenerate = MExprAst + FutharkAst
  sem generateType (env : FutharkGenerateEnv) =
  | t ->
    let aliasIdent =
      match t with TyVar {ident = ident} then
        Some ident
      else match mapLookup t env.typeAliases with Some ident then
        Some ident
      else None ()
    in
    match aliasIdent with Some id then
      match mapLookup id env.typeParams with Some typeParams then
        let info = infoTy t in
        FTyParamsApp {ty = FTyIdent {ident = id, info = info},
                      params = typeParams, info = info}
      else generateTypeNoAlias env t
    else generateTypeNoAlias env t

  sem generateTypeNoAlias (env : FutharkGenerateEnv) =
  | TyUnknown t -> FTyUnknown {info = t.info}
  | TyInt t -> FTyInt {info = t.info}
  | TyFloat t -> FTyFloat {info = t.info}
  | TyBool t -> FTyBool {info = t.info}
  | TySeq t ->
    FTyArray {elem = generateType env t.ty, dim = None (), info = t.info}
  | TyRecord t ->
    FTyRecord {fields = mapMap (generateType env) t.fields, info = t.info}
  | TyArrow t ->
    FTyArrow {from = generateType env t.from, to = generateType env t.to,
              info = t.info}
  | TyVar t -> FTyIdent {ident = t.ident, info = t.info}
  | t -> infoErrorExit (infoTy t) "Unsupported type"
end

lang FutharkPatternGenerate = MExprAst + FutharkAst + FutharkTypeGenerate
  sem generatePattern (env : FutharkGenerateEnv) (targetTy : Type) =
  | PatNamed t ->
    FPNamed {ident = t.ident, ty = generateType env t.ty, info = t.info}
  | PatInt t ->
    FPInt {val = t.val, ty = generateType env t.ty, info = t.info}
  | PatBool t ->
    FPBool {val = t.val, ty = generateType env t.ty, info = t.info}
  | PatRecord t ->
    let mergeBindings = lam bindings : Map SID Pat. lam fields : Map SID Type.
      mapMapWithKey
        (lam k. lam ty : Type.
          match mapLookup k bindings with Some pat then
            generatePattern env ty pat
          else futPvarw_ ())
        fields
    in
    match targetTy with TyRecord {fields = fields} then
      FPRecord {bindings = mergeBindings t.bindings fields,
                ty = generateType env t.ty, info = t.info}
    else infoErrorExit t.info "Cannot match non-record type on record pattern"
end

let _collectParams = use FutharkTypeGenerate in
  lam env : FutharkGenerateEnv. lam body : Expr.
  recursive let work = lam params : [(Name, FutType)]. lam body : Expr.
    match body with TmLam t then
      let params = snoc params (t.ident, generateType env t.tyIdent) in
      work params t.body
    else (params, body)
  in
  work [] body

lang FutharkMatchGenerate = MExprAst + FutharkAst + FutharkPatternGenerate +
                            FutharkTypeGenerate + FutharkTypePrettyPrint
  sem defaultGenerateMatch (env : FutharkGenerateEnv) =
  | TmMatch t -> infoErrorExit t.info "Unsupported match expression"

  sem generateExpr (env : FutharkGenerateEnv) =
  | TmMatch ({pat = PatBool {val = true}} & t) ->
    FEIf {cond = generateExpr env t.target, thn = generateExpr env t.thn,
          els = generateExpr env t.els, ty = generateType env t.ty,
          info = t.info}
  | TmMatch ({pat = PatBool {val = false}} & t) ->
    FEIf {cond = generateExpr env t.target, thn = generateExpr env t.els,
          els = generateExpr env t.thn, ty = generateType env t.ty,
          info = t.info}
  | TmMatch ({pat = PatInt {val = i}} & t) ->
    let cond = generateExpr env (withInfo (infoTm t.target) (eqi_ (int_ i) t.target)) in
    FEIf {cond = cond, thn = generateExpr env t.thn,
          els = generateExpr env t.els, ty = generateType env t.ty,
          info = t.info}
  | TmMatch ({pat = PatNamed {ident = PWildcard _}} & t) -> generateExpr env t.thn
  | TmMatch ({pat = PatNamed {ident = PName n}} & t) ->
    FELet {ident = n, tyBody = ty t.target, body = generateExpr env t.target,
           inexpr = generateExpr env t.thn, ty = generateType env (ty t.thn),
           info = infoTm t.target}
  | TmMatch ({pat = PatRecord {bindings = bindings},
              thn = TmVar {ident = exprName}, els = TmNever _} & t) ->
    let binds : [(SID, Pat)] = mapBindings bindings in
    match binds with [(fieldLabel, PatNamed {ident = PName patName})] then
      if nameEq patName exprName then
        FERecordProj {rec = generateExpr env t.target, key = fieldLabel,
                      ty = t.ty, info = t.info}
      else defaultGenerateMatch env (TmMatch t)
    else defaultGenerateMatch env (TmMatch t)
  | TmMatch ({pat = PatSeqEdge {prefix = [PatNamed {ident = PName head}],
                                middle = PName tail, postfix = []},
              els = TmNever _} & t) ->
    let target = generateExpr env t.target in
    let targetTy = generateType env (ty t.target) in
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
          ty = generateType env (ty t.thn),
          info = t.info},
        ty = generateType env (ty t.thn),
        info = t.info}
    else infoErrorExit t.info "Cannot match non-sequence type on sequence pattern"
  | TmMatch ({pat = PatRecord {bindings = bindings} & pat, els = TmNever _} & t) ->
    FEMatch {
      target = generateExpr env t.target,
      cases = [(generatePattern env (ty t.target) pat, generateExpr env t.thn)],
      ty = generateType env t.ty,
      info = t.info}
  | (TmMatch _) & t -> defaultGenerateMatch env t
end

lang FutharkAppGenerate = MExprAst + FutharkAst + FutharkTypeGenerate
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
    FEArrayUpdate {
      array = generateExpr env arg1, index = generateExpr env arg2,
      value = generateExpr env arg3, ty = generateType env t.ty, info = t.info}
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
                         rhs = TmConst {val = CInt {val = 0}}},
            rhs = arg3} & t) ->
    let arrayType = generateType env (ty arg1) in
    let takeConst = FEConst {
      val = FCTake (),
      ty = FTyArrow {
        from = FTyInt {info = t.info},
        to = FTyArrow {from = arrayType, to = arrayType, info = t.info},
        info = t.info},
      info = t.info} in
    withTypeFutTm arrayType
      (withInfoFutTm t.info
        (futAppSeq_ takeConst [generateExpr env arg3, generateExpr env arg1]))
  | TmApp ({lhs = TmApp {lhs = TmApp {lhs = TmConst {val = CSubsequence _},
                                      rhs = arg1},
                         rhs = arg2},
            rhs = arg3} & t) ->
    -- NOTE(larshum, 2021-06-16): The generated code constructs a slice, which
    -- is a reference rather than a copy. This could result in compilation
    -- errors on Futhark's side.
    let startIdx = generateExpr env arg2 in
    let offset = generateExpr env arg3 in
    let info = mergeInfo (infoFutTm startIdx) (infoFutTm offset) in
    let endIdx = FEApp {
      lhs = FEApp {
        lhs = FEConst {val = FCAdd (), ty = tyunknown_, info = info},
        rhs = startIdx,
        ty = FTyArrow {
          from = FTyInt {info = info}, to = FTyInt {info = info}, info = info},
        info = info
      },
      rhs = offset,
      ty = FTyInt {info = info},
      info = info
    } in
    FEArraySlice {
      array = generateExpr env arg1, startIdx = startIdx, endIdx = endIdx,
      ty = generateType env t.ty, info = t.info}
  | TmApp {lhs = TmConst {val = CFloorfi _}, rhs = arg, info = info} ->
    FEApp {
      lhs = FEConst {
        val = FCFloat2Int (),
        ty = FTyArrow {from = FTyFloat {info = info},
                       to = FTyInt {info = info}, info = info},
        info = info},
      rhs = FEApp {
        lhs = FEConst {
          val = FCFloatFloor (),
          ty = FTyArrow {from = FTyFloat {info = info},
                         to = FTyFloat {info = info}, info = info},
          info = info},
        rhs = generateExpr env arg,
        ty = FTyFloat {info = info},
        info = info},
      ty = FTyInt {info = info},
      info = info}
  | TmApp ({
      rhs = s,
      lhs = TmApp {
        rhs = ne,
        lhs = TmApp {
          lhs = TmConst {val = CFoldl _},
          rhs = TmLam {ident = acc, body = TmLam {ident = x, body = body}}}}
    } & t) ->
    let subMap = mapFromSeq nameCmp [(acc, lam info. ne)] in
    let body = substituteVariables body subMap in
    FEForEach {
      param = generateExpr env ne, loopVar = x, seq = generateExpr env s,
      body = generateExpr env body, ty = generateType env t.ty, info = t.info}
  | (TmApp _) & t -> defaultGenerateApp env t
end

lang FutharkExprGenerate = FutharkConstGenerate + FutharkTypeGenerate +
                           FutharkMatchGenerate + FutharkAppGenerate +
                           MExprParallelKeywordMaker
  sem generateExpr (env : FutharkGenerateEnv) =
  | TmVar t ->
    FEVar {ident = t.ident, ty = generateType env t.ty, info = t.info}
  | TmRecord t ->
    FERecord {fields = mapMap (generateExpr env) t.bindings,
              ty = generateType env t.ty, info = t.info}
  | TmSeq t ->
    FEArray {tms = map (generateExpr env) t.tms, ty = generateType env t.ty,
             info = t.info}
  | TmConst t ->
    FEConst {val = generateConst t.val, ty = generateType env t.ty,
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
  | TmParallelMap t ->
    withTypeFutTm
      (generateType env t.ty)
      (withInfoFutTm t.info (futMap_ (generateExpr env t.f) (generateExpr env t.as)))
  | TmParallelMap2 t ->
    withTypeFutTm
      (generateType env t.ty)
      (withInfoFutTm t.info (futMap2_ (generateExpr env t.f)
                                      (generateExpr env t.as)
                                      (generateExpr env t.bs)))
  | TmParallelFlatMap t ->
    -- TODO(larshum, 2021-07-08): Compile differently depending on the possible
    -- sizes of sequences.
    -- * If size is either 0 or 1, we should use 'filter' on the map results.
    -- * Otherwise we use 'flatten' on the map results. This requires that the
    --   size is a constant 'n' for all elements, and that the Futhark compiler
    --   can figure this out.
    withTypeFutTm
      (generateType env t.ty)
      (withInfoFutTm t.info (futFlatten_ (futMap_ (generateExpr env t.f)
                                                  (generateExpr env t.as))))
  | TmParallelReduce t ->
    withTypeFutTm
      (generateType env t.ty)
      (withInfoFutTm t.info (futReduce_ (generateExpr env t.f)
                                        (generateExpr env t.ne)
                                        (generateExpr env t.as)))
  | TmRecLets t ->
    infoErrorExit t.info "Recursive functions cannot be translated into Futhark"
end

lang FutharkToplevelGenerate = FutharkExprGenerate + FutharkConstGenerate +
                               FutharkTypeGenerate
  sem generateToplevel (env : FutharkGenerateEnv) =
  | TmType t ->
    recursive let parameterizeType =
      lam params : [FutTypeParam]. lam ty : FutType.
      match ty with FTyArray t then
        match parameterizeType params t.elem with (params, elem) then
          let n = nameSym "n" in
          let params = cons (FPSize {val = n}) params in
          (params, FTyArray {{t with elem = elem} with dim = Some n})
        else never
      else match ty with FTyRecord t then
        let paramField = lam params. lam. lam ty. parameterizeType params ty in
        match mapMapAccum paramField params t.fields with (params, fields) then
          (params, FTyRecord {t with fields = fields})
        else never
      else match ty with FTyArrow t then
        match parameterizeType params t.from with (params, from) then
          match parameterizeType params t.to with (params, to) then
            (params, FTyArrow {{t with from = from} with to = to})
          else never
        else never
      else (params, ty)
    in
    let futType = generateType env t.tyIdent in
    match parameterizeType [] futType with (typeParams, ty) then
      let env = {{env with typeAliases = mapInsert t.tyIdent t.ident env.typeAliases}
                      with typeParams = mapInsert t.ident typeParams env.typeParams} in
      let decl = FDeclType {
        ident = t.ident,
        typeParams = typeParams,
        ty = ty,
        info = t.info
      } in
      cons decl (generateToplevel env t.inexpr)
    else never
  | TmLet t ->
    recursive let findReturnType = lam ty : Type.
      match ty with TyArrow t then
        findReturnType t.to
      else ty
    in
    let decl =
      match _collectParams env t.body with (params, body) then
        if null params then
          FDeclConst {ident = t.ident, ty = generateType env t.tyBody,
                      val = generateExpr env body, info = t.info}
        else
          let retTy = findReturnType t.tyBody in
          let entry = setMem t.ident env.entryPoints in
          FDeclFun {ident = t.ident, entry = entry, typeParams = [],
                    params = params, ret = generateType env retTy,
                    body = generateExpr env body, info = t.info}
      else never
    in
    cons decl (generateToplevel env t.inexpr)
  | TmRecLets t ->
    infoErrorExit t.info "Recursive functions are not supported in Futhark"
  | TmExt t ->
    infoErrorExit t.info "External functions are not supported in Futhark"
  | TmUtest t ->
    infoErrorExit t.info "Utests are not supported in Futhark"
  | TmConDef t ->
    infoErrorExit t.info "Constructor definitions are not supported in Futhark"
  | _ -> []
end

lang FutharkGenerate = FutharkToplevelGenerate + MExprCmp
  sem generateProgram (entryPoints : Set Name) =
  | prog ->
    let emptyEnv = {
      entryPoints = entryPoints,
      typeAliases = mapEmpty cmpType,
      typeParams = mapEmpty nameCmp,
      boundNames = mapEmpty nameCmp
    } in
    FProg {decls = generateToplevel emptyEnv prog}
end

lang TestLang =
  FutharkGenerate + FutharkPrettyPrint + MExprSym + MExprTypeAnnot
end

mexpr

use TestLang in

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

let t = bindall_ [
  ntype_ intseq (tyseq_ tyint_),
  ntype_ floatseq (tyseq_ tyfloat_),
  nlet_ a (ntyvar_ intseq) (seq_ [int_ 1, int_ 2, int_ 3]),
  nlet_ b (ntyvar_ floatseq) (seq_ [float_ 2.718, float_ 3.14]),
  nlet_ c (tyrecord_ [("a", tyint_), ("b", tyfloat_)])
           (record_ (tyrecord_ [("a", tyint_), ("b", tyfloat_)])
                    [("a", int_ 3), ("b", float_ 2.0)]),
  nlet_ f (tyarrows_ [tyint_, tyint_, tyint_])
           (nlam_ a2 tyint_ (nlam_ b2 tyint_ (addi_ (nvar_ a2) (nvar_ b2)))),
  nlet_ g (tyarrows_ [ntyvar_ floatseq, tyfloat_, tyfloat_])
            (nlam_ r (ntyvar_ floatseq)
              (nlam_ f2 tyfloat_ (addf_ (nvar_ f2) (get_ (nvar_ r) (int_ 0))))),
  nlet_ min (tyarrows_ [tyint_, tyint_, tyint_])
             (nlam_ a3 tyint_ (nlam_ b3 tyint_ (
               if_ (geqi_ (nvar_ a3) (nvar_ b3)) (nvar_ b3) (nvar_ a3)))),
  nlet_ map (tyarrows_ [tyarrow_ tyint_ tyint_, ntyvar_ intseq, ntyvar_ intseq])
             (nlam_ f3 (tyarrow_ tyint_ tyint_) (nlam_ s (ntyvar_ intseq)
               (parallelMap_ (nvar_ f3) (nvar_ s)))),
  unit_
] in

let intSeqType = FTyParamsApp {
  ty = nFutIdentTy_ intseq, params = [FPSize {val = n}], info = NoInfo ()} in
let floatSeqType = FTyParamsApp {
  ty = nFutIdentTy_ floatseq, params = [FPSize {val = n2}], info = NoInfo ()} in
let expected = FProg {decls = [
  FDeclType {ident = intseq, typeParams = [FPSize {val = n}],
             ty = futSizedArrayTy_ futIntTy_ n, info = NoInfo ()},
  FDeclType {ident = floatseq, typeParams = [FPSize {val = n2}],
             ty = futSizedArrayTy_ futFloatTy_ n2, info = NoInfo ()},
  FDeclConst {
    ident = a, ty = intSeqType,
    val = futArray_ [futInt_ 1, futInt_ 2, futInt_ 3], info = NoInfo ()},
  FDeclConst {
    ident = b, ty = floatSeqType,
    val = futArray_ [futFloat_ 2.718, futFloat_ 3.14], info = NoInfo ()},
  FDeclConst {
    ident = c, ty = futRecordTy_ [("a", futIntTy_), ("b", futFloatTy_)],
    val = futRecord_ [("a", futInt_ 3), ("b", futFloat_ 2.0)],
    info = NoInfo ()},
  FDeclFun {
    ident = f, entry = true, typeParams = [],
    params = [(a2, futIntTy_), (b2, futIntTy_)], ret = futIntTy_,
    body = futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ a2, nFutVar_ b2],
    info = NoInfo ()},
  FDeclFun {
    ident = g, entry = true, typeParams = [],
    params = [(r, floatSeqType), (f2, futFloatTy_)], ret = futFloatTy_,
    body =
      futAppSeq_ (futConst_ (FCAdd ()))
        [nFutVar_ f2, futArrayAccess_ (nFutVar_ r) (futInt_ 0)],
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
    ident = map, entry = false, typeParams = [],
    params = [(f3, futArrowTy_ futIntTy_ futIntTy_), (s, intSeqType)],
    ret = intSeqType,
    body = futAppSeq_ (futConst_ (FCMap ())) [nFutVar_ f3, nFutVar_ s],
    info = NoInfo ()}
]} in
let entryPoints = setOfSeq nameCmp [f, g, min] in
utest printFutProg (generateProgram entryPoints t) with printFutProg expected
using eqSeq eqc in

()
