include "ast.mc"
include "ast-builder.mc"
include "pprint.mc"

include "set.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/patterns.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"

type FutharkGenerateEnv = {
  typeEnv : Map Name FutType
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

recursive let _getTrailingSelfRecursiveCall = use MExprAst in
  lam funcIdent : Name. lam body : Expr.
  match body with TmLet {inexpr = inexpr} then
    _getTrailingSelfRecursiveCall funcIdent inexpr
  else match body with TmRecLets {inexpr = inexpr} then
    _getTrailingSelfRecursiveCall funcIdent inexpr
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

lang FutharkConstGenerate = MExprPatternKeywordMaker + FutharkAst
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
  | CFloorfi _ -> error "Wrong number of arguments"
  | CGet _ -> error "Wrong number of arguments"
  | CSet _ -> error "Wrong number of arguments"
  | CLength _ -> FEBuiltIn {str = "length"}
  | CCreate _ -> FEBuiltIn {str = "tabulate"}
  | CReverse _ -> FEBuiltIn {str = "reverse"}
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
      FPRecord {fields = mergeBindings t.bindings fields}
    else infoErrorExit t.info "Cannot match non-record type on record pattern"
end

lang FutharkTypeGenerate = MExprAst + FutharkAst
  sem generateType (env : FutharkGenerateEnv) =
  | TyInt _ -> futIntTy_
  | TyFloat _ -> futFloatTy_
  | TySeq {ty = elemTy} -> futUnsizedArrayTy_ (generateType env elemTy)
  | TyRecord {fields = fields} ->
    FTyRecord {fields = mapMap (generateType env) fields}
  | TyArrow {from = from, to = to} ->
    FTyArrow {from = generateType env from, to = generateType env to}
  | TyVar t ->
    match mapLookup t.ident env.typeEnv with Some futType then
      futType
    else infoErrorExit t.info (join ["Undefined type identifier ",
                                     nameGetStr t.ident])
  | TyUnknown t ->
    infoErrorExit t.info "Cannot translate unknown type to Futhark"
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
  | TmMatch ({pat = PatRecord {bindings = bindings}, els = TmNever _} & t) ->
    let pat = generatePattern (ty t.target) in
    FEMatch {
      target = generateExpr env t.target,
      cases = [pat, generateExpr env t.thn]
    }
  | (TmMatch _) & t -> defaultGenerateMatch env t
end

lang FutharkExprGenerate = FutharkConstGenerate + FutharkTypeGenerate +
                           FutharkMatchGenerate
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
  | TmApp {lhs = TmConst {val = CFloorfi _}, rhs = arg} ->
    FEApp {
      lhs = FEBuiltIn {str = "i64.f64"},
      rhs = FEApp {
        lhs = FEBuiltIn {str = "f64.floor"},
        rhs = generateExpr env arg}}
  | TmApp t -> FEApp {lhs = generateExpr env t.lhs, rhs = generateExpr env t.rhs}
  | TmLet t ->
    FELet {ident = t.ident, tyBody = Some (generateType env t.tyBody),
           body = generateExpr env t.body,
           inexpr = generateExpr env t.inexpr}
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
end

lang FutharkToplevelGenerate = FutharkExprGenerate + FutharkConstGenerate +
                               FutharkTypeGenerate
  sem generateToplevel (env : FutharkGenerateEnv) =
  | TmType t ->
    let futType = generateType env t.tyIdent in
    let env = {env with typeEnv = mapInsert t.ident futType env.typeEnv} in
    generateToplevel env t.inexpr
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
  | TmRecLets t ->
    -- NOTE: currently makes the following assumptions on each binding:
    -- * The body of the binding has the shape
    --   let <id> = <args> lam <i> : Int. lam <n> : Int.
    --     if lti <i> <n> then ... <id> <args> (addi <i> 1) <n> else <base case>
    -- * The base case variable is one of the argument variables
    -- * The final call of the recursive case is the self-recursive call
    let unsupportedTranslationError = lam id : Int. lam info : Info.
      infoErrorExit info (join ["Cannot translate recursive binding to Futhark",
                                ", error code: ", int2string id])
    in
    let generateBinding = lam binding : RecLetBinding.
      recursive let findReturnType = lam ty : Type.
        match ty with TyArrow t then
          findReturnType t.to
        else ty
      in
      match _collectParams env binding.body
      with (funcParams ++ [(i, FTyInt _), (n, FTyInt _)], body) then
        match body with TmMatch {
          target = TmApp {lhs = TmApp {lhs = TmConst {val = CLti _},
                                       rhs = TmVar {ident = iarg}},
                          rhs = TmVar {ident = narg}},
          pat = PatBool {val = true},
          thn = recursiveCase,
          els = TmVar {ident = baseCaseVar}} then
          if and (nameEq i iarg) (nameEq n narg) then
            match _getTrailingSelfRecursiveCall binding.ident recursiveCase
            with Some callParams then
              match index (lam p : (Name, FutType). nameEq p.0 baseCaseVar) funcParams
              with Some idx then
                let retTy = generateType env (ty recursiveCase) in
                let forLoopBody = generateExpr env recursiveCase in
                let forLoopBodyWithPrealloc =
                  match retTy with FTyArray {elem = elemTy} then
                    let alloc =
                      FELet {
                        ident = baseCaseVar,
                        tyBody = None (),
                        body = FEApp {
                          lhs = FEApp {
                            lhs = FEBuiltIn {str = "replicate"},
                            rhs = FEVar {ident = n}
                          },
                          rhs =
                            match elemTy with FTyInt _ then
                              FEConst {val = FCInt {val = 0}}
                            else match elemTy with FTyFloat _ then
                              FEConst {val = FCFloat {val = 0.0}}
                            else unsupportedTranslationError 7 binding.info -- unsupported return type
                        },
                        inexpr = futUnit_ ()
                      }
                    in
                    futBind_ alloc forLoopBody
                  else match retTy with FTyInt _ | FTyFloat _ then
                    forLoopBody
                  else unsupportedTranslationError 6 binding.info -- unsupported return type
                in
                let funcBody =
                  futBindall_ [
                    forLoopBodyWithPrealloc,
                    FEFor {
                      param = FEVar {ident = baseCaseVar},
                      loopVar = i,
                      boundVar = n,
                      thn = generateExpr env (get callParams idx)
                    }]
                in
                let params = snoc (snoc funcParams (i, FTyInt ())) (n, FTyInt ()) in
                FDeclFun {ident = binding.ident, entry = false, typeParams = [],
                          params = params, ret = retTy,
                          body = funcBody}
              else unsupportedTranslationError 5 binding.info -- base case variable not among parameters
            else unsupportedTranslationError 4 binding.info -- not ending with trailing self-recursion
          else unsupportedTranslationError 3 binding.info -- does not loop on final two arguments
        else unsupportedTranslationError 2 binding.info -- body structure (+ assumption on base case)
      else unsupportedTranslationError 1 binding.info -- parameters
    in
    foldr
      (lam binding. lam acc. cons (generateBinding binding) acc)
      (generateToplevel env t.inexpr) t.bindings
  | _ -> []
end

lang FutharkGenerate = FutharkToplevelGenerate
  sem generateProgram =
  | prog ->
    let emptyEnv = {typeEnv = mapEmpty nameCmp} in
    FProg {decls = generateToplevel emptyEnv prog}
end

lang TestLang =
  FutharkGenerate + FutharkPrettyPrint + MExprPatternKeywordMaker + MExprSym +
  MExprTypeAnnot
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
print (expr2str p);
()
