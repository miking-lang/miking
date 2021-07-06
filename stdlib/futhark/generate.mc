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
  | CInt n -> futInt_ n.val
  | CFloat f -> futFloat_ f.val
  | CAddi _ | CAddf _ -> futConst_ (FCAdd ())
  | CSubi _ | CSubf _ -> futConst_ (FCSub ())
  | CMuli _ | CMulf _ -> futConst_ (FCMul ())
  | CDivi _ | CDivf _ -> futConst_ (FCDiv ())
  | CModi _ -> futConst_ (FCRem ())
  | CEqi _ | CEqf _ -> futConst_ (FCEq ())
  | CNeqi _ | CNeqf _ -> futConst_ (FCNeq ())
  | CGti _ | CGtf _ -> futConst_ (FCGt ())
  | CLti _ | CLtf _ -> futConst_ (FCLt ())
  | CGeqi _ | CGeqf _ -> futConst_ (FCGeq ())
  | CLeqi _ | CLeqf _ -> futConst_ (FCLeq ())
  | CLength _ -> FEBuiltIn {str = "length"}
  | CReverse _ -> FEBuiltIn {str = "reverse"}
  | CConcat _ -> FEBuiltIn {str = "concat"}
  | CHead _ -> FEBuiltIn {str = "head"}
  | CTail _ -> FEBuiltIn {str = "tail"}
  | CNull _ -> FEBuiltIn {str = "null"}
  | CMap _ -> futConst_ (FCMap ())
end

lang FutharkPatternGenerate = MExprAst + FutharkAst
  sem generatePattern (targetTy : Type) =
  | PatNamed t -> FPNamed {ident = t.ident}
  | PatInt t -> FPInt {val = t.val}
  | PatBool t -> FPBool {val = t.val}
  | PatRecord t ->
    let mergeBindings = lam bindings : Map SID Pat. lam fields : Map SID Type.
      mapMapWithKey
        (lam k. lam ty : Type.
          match mapLookup k bindings with Some pat then
            generatePattern ty pat
          else futPvarw_ ())
        fields
    in
    match targetTy with TyRecord {fields = fields} then
      FPRecord {bindings = mergeBindings t.bindings fields}
    else infoErrorExit t.info "Cannot match non-record type on record pattern"
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
        FTyParamsApp {ty = FTyIdent {ident = id}, params = typeParams}
      else generateTypeNoAlias env t
    else generateTypeNoAlias env t

  sem generateTypeNoAlias (env : FutharkGenerateEnv) =
  | TyInt _ -> futIntTy_
  | TyFloat _ -> futFloatTy_
  | TyBool _ -> futBoolTy_
  | TySeq {ty = elemTy} -> futUnsizedArrayTy_ (generateType env elemTy)
  | TyRecord {fields = fields} ->
    FTyRecord {fields = mapMap (generateType env) fields}
  | TyArrow {from = from, to = to} ->
    FTyArrow {from = generateType env from, to = generateType env to}
  | TyVar t ->
    FTyIdent {ident = t.ident}
  | TyUnknown t ->
    FTyUnknown ()
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
  | TmMatch t ->
    infoErrorExit t.info "Unsupported match expression"

  sem generateExpr (env : FutharkGenerateEnv) =
  | TmMatch ({pat = PatBool {val = true}} & t) ->
    futIf_ (generateExpr env t.target) (generateExpr env t.thn) (generateExpr env t.els)
  | TmMatch ({pat = PatBool {val = false}} & t) ->
    futIf_ (generateExpr env t.target) (generateExpr env t.els) (generateExpr env t.thn)
  | TmMatch ({pat = PatInt {val = i}} & t) ->
    let cond = generateExpr env (eqi_ (int_ i) t.target) in
    futIf_ cond (generateExpr env t.thn) (generateExpr env t.els)
  | TmMatch ({pat = PatNamed {ident = PWildcard _}} & t) ->
    generateExpr env t.thn
  | TmMatch ({pat = PatNamed {ident = PName n}} & t) ->
    generateExpr env (bind_ (nulet_ n t.target) t.thn)
  | TmMatch ({pat = PatRecord {bindings = bindings},
              thn = TmVar {ident = exprName}, els = TmNever _} & t) ->
    let binds : [(SID, Pat)] = mapBindings bindings in
    match binds with [(fieldLabel, PatNamed {ident = PName patName})] then
      if nameEq patName exprName then
        FERecordProj {rec = generateExpr env t.target, key = fieldLabel}
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
        body = FEApp {lhs = FEBuiltIn {str = "head"}, rhs = target},
        inexpr = FELet {
          ident = tail,
          tyBody = targetTy,
          body = FEApp {lhs = FEBuiltIn {str = "tail"}, rhs = target},
          inexpr = generateExpr env t.thn}}
    else infoErrorExit t.info "Cannot match non-sequence type on sequence pattern"
  | TmMatch ({pat = PatRecord {bindings = bindings} & pat, els = TmNever _} & t) ->
    FEMatch {
      target = generateExpr env t.target,
      cases = [(generatePattern (ty t.target) pat, generateExpr env t.thn)]
    }
  | (TmMatch _) & t -> defaultGenerateMatch env t
end

lang FutharkExprGenerate = FutharkConstGenerate + FutharkTypeGenerate +
                           FutharkMatchGenerate + MExprParallelKeywordMaker
  sem generateExpr (env : FutharkGenerateEnv) =
  | TmVar t -> FEVar {ident = t.ident}
  | TmRecord t -> FERecord {fields = mapMap (generateExpr env) t.bindings}
  | TmSeq {tms = tms} -> futArray_ (map (generateExpr env) tms)
  | TmConst c -> generateConst c.val
  | TmLam t -> nFutLam_ t.ident (generateExpr env t.body)
  | TmApp {lhs = TmApp {lhs = TmConst {val = CGet _}, rhs = arg1}, rhs = arg2} ->
    futArrayAccess_ (generateExpr env arg1) (generateExpr env arg2)
  | TmApp {lhs = TmApp {lhs = TmApp {lhs = TmConst {val = CSet _}, rhs = arg1},
                        rhs = arg2},
           rhs = arg3} ->
    futArrayUpdate_ (generateExpr env arg1) (generateExpr env arg2)
                    (generateExpr env arg3)
  | TmApp {lhs = TmApp {lhs = TmConst {val = CCreate _}, rhs = arg1},
           rhs = arg2} ->
    let tryLookupExpr = lam e.
      match e with TmVar t then
        optionGetOrElse
          (lam. e)
          (mapLookup t.ident env.boundNames)
      else e
    in
    let argx1 = tryLookupExpr arg1 in
    let argx2 = tryLookupExpr arg2 in
    match argx2 with TmLam {ident = i, body = body} then
      match body with TmVar {ident = id} then
        if nameEq i id then
          match argx1 with TmApp {lhs = TmConst {val = CLength _}, rhs = seq} then
            futIndices_ (generateExpr env seq)
          else
            futIota_ (generateExpr env arg1)
        else
          futReplicate_ (generateExpr env arg1) (generateExpr env body)
      else match body with TmConst _ then
        futReplicate_ (generateExpr env arg1) (generateExpr env body)
      else futTabulate_ (generateExpr env arg1) (generateExpr env arg2)
    else futTabulate_ (generateExpr env arg1) (generateExpr env arg2)
  | TmApp {lhs = TmApp {lhs = TmApp {lhs = TmConst {val = CSubsequence _},
                                     rhs = arg1},
                        rhs = TmConst {val = CInt {val = 0}}},
           rhs = arg3} ->
    futAppSeq_
      (FEBuiltIn {str = "take"})
      [generateExpr env arg3, generateExpr env arg1]
  | TmApp {lhs = TmApp {lhs = TmApp {lhs = TmConst {val = CSubsequence _},
                                     rhs = arg1},
                        rhs = arg2},
           rhs = arg3} ->
    -- NOTE(larshum, 2021-06-16): The generated code constructs a slice, which
    -- is a reference rather than a copy. This could result in compilation
    -- errors on Futhark's side.
    futArraySlice_ (generateExpr env arg1) (generateExpr env arg2)
                   (generateExpr env (addi_ arg2 arg3))
  | TmApp {lhs = TmConst {val = CFloorfi _}, rhs = arg} ->
    FEApp {
      lhs = FEBuiltIn {str = "i64.f64"},
      rhs = FEApp {
        lhs = FEBuiltIn {str = "f64.floor"},
        rhs = generateExpr env arg}}
  | TmApp t -> FEApp {lhs = generateExpr env t.lhs, rhs = generateExpr env t.rhs}
  | TmLet t ->
    let boundNames = mapInsert t.ident t.body env.boundNames in
    let inexprEnv = {env with boundNames = boundNames} in
    FELet {ident = t.ident, tyBody = generateType env t.tyBody,
           body = generateExpr env t.body,
           inexpr = generateExpr inexprEnv t.inexpr}
  | TmParallelMap t -> futMap_ (generateExpr env t.f) (generateExpr env t.as)
  | TmParallelMap2 t ->
    futMap2_ (generateExpr env t.f) (generateExpr env t.as) (generateExpr env t.bs)
  | TmParallelReduce t ->
    futReduce_ (generateExpr env t.f) (generateExpr env t.ne) (generateExpr env t.as)
  | TmParallelScan t ->
    futScan_ (generateExpr env t.f) (generateExpr env t.ne) (generateExpr env t.as)
  | TmParallelFilter t -> futFilter_ (generateExpr env t.p) (generateExpr env t.as)
  | TmParallelPartition t ->
    futPartition_ (generateExpr env t.p) (generateExpr env t.as)
  | TmParallelAll t -> futAll_ (generateExpr env t.p) (generateExpr env t.as)
  | TmParallelAny t -> futAny_ (generateExpr env t.p) (generateExpr env t.as)
  | TmFlatten t -> futFlatten_ (generateExpr env t.s)
  | TmSequentialFor t ->
    match t.body with TmLam {ident = i, body = body} then
      FEFor {param = generateExpr env t.init, loopVar = i,
             boundExpr = generateExpr env t.n,
             thn = generateExpr env body}
    else never
end

lang FutharkRecLetGenerate = FutharkTypeGenerate + FutharkExprGenerate +
                             MExprParallelKeywordMaker
  sem _addCallsToGraph (bindingIndex : Int) (bindingNameToIndex : Map Name Int)
                       (g : Digraph Int Int) =
  | TmApp t ->
    match collectAppArguments (TmApp t) with (func, args) then
      match func with TmVar {ident = id} then
        match mapLookup id bindingNameToIndex with Some callIndex then
          digraphMaybeAddEdge bindingIndex callIndex 0 g
        else g
      else g
    else never
  | t -> sfold_Expr_Expr (_addCallsToGraph bindingIndex bindingNameToIndex) g t

  sem _reverseTopologicallySortedBindings (bindings : [RecLetBinding]) =
  | _ ->
    let bindingIndices = mapi (lam i. lam. i) bindings in
    let bindingNameToIndex =
      mapFromSeq nameCmp
        (mapi (lam i. lam binding : RecLetBinding. (binding.ident, i)) bindings) in
    let g =
      foldl
        (lam g. lam index. digraphAddVertex index g)
        (digraphEmpty eqi eqi)
        bindingIndices in
    let g =
      foldl
        (lam g. lam p : (Int, RecLetBinding).
          let idx = p.0 in
          let binding = p.1 in
          _addCallsToGraph idx bindingNameToIndex g binding.body)
        g
        (zip bindingIndices bindings) in
    let s = digraphTarjan g in
    if all (lam scc. eqi (length scc) 1) s then
      Some (join s)
    else None ()

  sem defaultGenerateRecLets (env : FutharkGenerateEnv) =
  | TmRecLets t ->
    let generateNextBinding = lam acc : FutExpr. lam binding : RecLetBinding.
      FELet {ident = binding.ident, tyBody = generateType env binding.tyBody,
             body = generateExpr env binding.body,
             inexpr = acc}
    in
    match _reverseTopologicallySortedBindings t.bindings () with Some permutation then
      let sortedBindings = permute t.bindings permutation in
      foldl generateNextBinding (generateExpr env t.inexpr) sortedBindings
    else
      infoErrorExit t.info "Could not translate recursive bindings to Futhark"

  sem generateExpr (env : FutharkGenerateEnv) =
  | (TmRecLets _) & t -> defaultGenerateRecLets env t
end

lang FutharkToplevelGenerate = FutharkExprGenerate + FutharkConstGenerate +
                               FutharkTypeGenerate + FutharkRecLetGenerate
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
        ty = ty
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
                      val = generateExpr env body}
        else
          let retTy = findReturnType t.tyBody in
          let entry = not (_isHigherOrderFunction params) in
          FDeclFun {ident = t.ident, entry = entry, typeParams = [],
                    params = params, ret = generateType env retTy,
                    body = generateExpr env body}
      else never
    in
    cons decl (generateToplevel env t.inexpr)
  | _ -> []
end

lang FutharkGenerate = FutharkToplevelGenerate + MExprCmpClosed
  sem generateProgram =
  | prog ->
    let emptyEnv = {
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

let fName = nameSym "f" in
let gName = nameSym "g" in
let minName = nameSym "min" in
let mapFunc = nameSym "mapFunc" in
let intseq = nameSym "intseq" in
let floatseq = nameSym "floatseq" in
let t = symbolize (bindall_ [
  ntype_ intseq (tyseq_ tyint_),
  ntype_ floatseq (tyseq_ tyfloat_),
  let_ "a" (ntyvar_ intseq) (seq_ [int_ 1, int_ 2, int_ 3]),
  let_ "b" (ntyvar_ floatseq) (seq_ [float_ 2.718, float_ 3.14]),
  let_ "c" (tyrecord_ [("a", tyint_), ("b", tyfloat_)])
           (record_ (tyrecord_ [("a", tyint_), ("b", tyfloat_)])
                    [("a", int_ 3), ("b", float_ 2.0)]),
  nlet_ fName (tyarrows_ [tyint_, tyint_, tyint_])
              (lam_ "a" tyint_ (lam_ "b" tyint_ (addi_ (var_ "a") (var_ "b")))),
  nlet_ gName (tyarrows_ [ntyvar_ floatseq, tyfloat_, tyfloat_])
              (lam_ "r" (ntyvar_ floatseq)
                (lam_ "f" tyfloat_ (addf_ (var_ "f") (get_ (var_ "r") (int_ 0))))),
  nlet_ minName (tyarrows_ [tyint_, tyint_, tyint_])
                (lam_ "a" tyint_ (lam_ "b" tyint_ (
                  if_ (geqi_ (var_ "a") (var_ "b")) (var_ "b") (var_ "a")))),
  nlet_ mapFunc (tyarrows_ [tyarrow_ tyint_ tyint_, ntyvar_ intseq, ntyvar_ intseq])
                (lam_ "f" (tyarrow_ tyint_ tyint_) (lam_ "s" (ntyvar_ intseq)
                  (parallelMap_ (var_ "f") (var_ "s")))),
  unit_
]) in
let p = generateProgram t in
-- print (expr2str p);
()
