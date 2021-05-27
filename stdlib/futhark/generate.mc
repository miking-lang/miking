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

let getDef = use FutharkAst in
  lam.
  let a = nameSym "a" in
  let seq = nameSym "seq" in
  let i = nameSym "i" in
  FDeclFun {
    ident = nameSym "get",
    entry = false,
    typeParams = [FPType {val = a}],
    params = [(seq, futUnsizedArrayTy_ (nFutIdentTy_ a)), (i, futIntTy_)],
    ret = nFutIdentTy_ a,
    body = futArrayAccess_ (nFutVar_ seq) (nFutVar_ i)
  }

let _preamble = ref (mapEmpty cmpString)
let _getPreamble = lam.
  let m = deref _preamble in
  if mapIsEmpty m then
    let m = mapFromList cmpString [
      ("get", getDef ())
    ] in
    modref _preamble m;
    deref _preamble
  else
    m

let _lookupPreamble = use FutharkAst in
  lam s : String.
  let m = _getPreamble () in
  match mapLookup s m with Some (FDeclFun {ident = id}) then
    id
  else
    error (join ["Could not find definition of function ", s, " in preamble"])

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
  | CGet _ -> nFutVar_ (_lookupPreamble "get")
  | CLength _ -> FEBuiltIn {str = "length"}
  | CCreate _ -> FEBuiltIn {str = "tabulate"}
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
  | TyUnknown t -> infoErrorExit t.info "Cannot translate unknown type to Futhark"
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

lang FutharkMatchGenerate = MExprAst + FutharkAst + FutharkTypeGenerate
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
  | TmMatch ({pat = PatSeqEdge {prefix = [PatNamed {ident = PName pre}],
                                middle = PName mid, postfix = []},
              els = TmNever _} & t) ->
    let targetName = nameSym "_target" in
    let lengthCond = geqi_ (length_ (nvar_ targetName)) (int_ 1) in
    FELet {ident = targetName, tyBody = generateType env (ty t.target),
           body = generateExpr env t.target, inexpr = generateExpr env t.thn}
  | TmMatch ({pat = PatSeqEdge {prefix = [], middle = PName mid,
                                postfix = [PatNamed {ident = PName post}]},
              els = TmNever _} & t) ->
    let targetName = nameSym "_target" in
    let lengthCond = geqi_ (length_ (nvar_ targetName)) (int_ 1) in
    FELet {ident = targetName, tyBody = generateType env (ty t.target),
           body = generateExpr env t.target, inexpr = generateExpr env t.thn}
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
  | TmApp t -> FEApp {lhs = generateExpr env t.lhs, rhs = generateExpr env t.rhs}
  | TmLet t ->
    FELet {ident = t.ident, tyBody = generateType env t.tyBody,
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
  -- Super special-cased translation of self-recursive functions to get
  -- compilation to work without complete support for recursion -> loop
  -- translation. This code makes a lot of assumptions about the structure of
  -- the recursive binding and how it makes its recursive calls. In general it
  -- will not produce the correct code.
  | TmRecLets t ->
    let unsupportedTranslationError = lam info : Info.
      infoErrorExit info "Cannot translate recursive binding to Futhark"
    in
    let generateBinding = lam binding : RecLetBinding.
      match _collectParams env binding.body with
        (params,
         TmMatch {target = TmVar v1, pat = PatSeqTot {pats = []}, thn = base,
                  els = TmMatch {target = TmVar v2, pat = PatSeqEdge p,
                                 thn = recur, els = TmNever _}})
      then
        if nameEq v1.ident v2.ident then
          match p with {prefix = [], middle = PName mid,
                        postfix = [PatNamed {ident = PName post}]} then
            () --TODO
          else match p with {prefix = [PatNamed {ident = PName pre}],
                             middle = PName mid, postfix = []} then
            () --TODO
          else unsupportedTranslationError binding.info
        else unsupportedTranslationError binding.info
      else unsupportedTranslationError binding.info
    in
    map generateBinding t.bindings
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
  | _ -> []
end

lang FutharkGenerate = FutharkToplevelGenerate
  sem generateProgram =
  | prog ->
    let preamble = mapValues (_getPreamble ()) in
    let emptyEnv = {typeEnv = mapEmpty nameCmp} in
    FProg {decls = concat preamble (generateToplevel emptyEnv prog)}
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
           (record_ [("a", int_ 3), ("b", float_ 2.0)]),
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
