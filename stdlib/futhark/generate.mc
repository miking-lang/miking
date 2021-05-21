include "ast.mc"
include "ast-builder.mc"
include "pprint.mc"

include "set.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/patterns.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"

let getRef = ref (nameNoSym "")
let getFn = lam.
  let n = deref getRef in
  if nameHasSym n then
    n
  else
    modref getRef (nameSym "get");
    deref getRef
let getDef = use FutharkAst in
  lam.
  let a = nameSym "a" in
  let seq = nameSym "seq" in
  let i = nameSym "i" in
  FDeclFun {
    ident = getFn (),
    entry = false,
    typeParams = [FPType {val = a}],
    params = [(seq, futUnsizedArrayTy_ (nFutIdentTy_ a)), (i, futIntTy_)],
    ret = nFutIdentTy_ a,
    body = futArrayAccess_ (nFutVar_ seq) (nFutVar_ i)
  }

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
  | CGet () -> nFutVar_ (getFn ())
end

lang FutharkTypeGenerate = MExprAst + FutharkAst
  sem generateType =
  | TyInt _ -> futIntTy_
  | TyFloat _ -> futFloatTy_
  | TySeq {ty = elemTy} -> futUnsizedArrayTy_ (generateType elemTy)
  | TyRecord {fields = fields} ->
    FTyRecord {fields = mapMap generateType fields}
  | TyArrow {from = from, to = to} ->
    FTyArrow {from = generateType from, to = generateType to}
  | TyUnknown _ -> error "Cannot translate unknown type to Futhark"
end

lang FutharkMatchGenerate = MExprAst + FutharkAst
  sem generateExpr =
  | TmMatch ({pat = PatBool {val = true}} & t) ->
    futIf_ (generateExpr t.target) (generateExpr t.thn) (generateExpr t.els)
  | TmMatch ({pat = PatBool {val = false}} & t) ->
    futIf_ (generateExpr t.target) (generateExpr t.els) (generateExpr t.thn)
  | TmMatch ({pat = PatInt {val = i}} & t) ->
    let cond = generateExpr (eqi_ (int_ i) t.target) in
    futIf_ cond (generateExpr t.thn) (generateExpr t.els)
  | TmMatch ({pat = PatNamed {ident = PWildcard _}} & t) ->
    generateExpr t.thn
  | TmMatch ({pat = PatNamed {ident = PName n}} & t) ->
    generateExpr (bind_ (nulet_ n t.target) t.thn)
  | TmMatch t ->
    infoErrorExit t.info "Unsupported match expression"
end

lang FutharkExprGenerate = FutharkConstGenerate + FutharkTypeGenerate +
                           FutharkMatchGenerate
  sem generateExpr =
  | TmVar t -> FEVar {ident = t.ident}
  | TmRecord t -> FERecord {fields = mapMap generateExpr t.bindings}
  | TmSeq {tms = tms} -> futArray_ (map generateExpr tms)
  | TmConst c -> generateConst c.val
  | TmLam t -> nFutLam_ t.ident (generateExpr t.body)
  | TmApp t -> FEApp {lhs = generateExpr t.lhs, rhs = generateExpr t.rhs}
  | TmLet t ->
    FELet {ident = t.ident, ty = generateType t.ty,
           body = generateExpr t.body,
           inexpr = generateExpr t.inexpr}
  | TmParallelMap t -> futMap_ (generateExpr t.f) (generateExpr t.as)
  | TmParallelMap2 t ->
    futMap2_ (generateExpr t.f) (generateExpr t.as) (generateExpr t.bs)
  | TmParallelReduce t ->
    futReduce_ (generateExpr t.f) (generateExpr t.ne) (generateExpr t.as)
  | TmParallelScan t ->
    futScan_ (generateExpr t.f) (generateExpr t.ne) (generateExpr t.as)
  | TmParallelFilter t -> futFilter_ (generateExpr t.p) (generateExpr t.as)
  | TmParallelPartition t ->
    futPartition_ (generateExpr t.p) (generateExpr t.as)
  | TmParallelAll t -> futAll_ (generateExpr t.p) (generateExpr t.as)
  | TmParallelAny t -> futAny_ (generateExpr t.p) (generateExpr t.as)
end

lang FutharkToplevelGenerate = FutharkExprGenerate + FutharkConstGenerate +
                               FutharkTypeGenerate
  sem generateToplevel =
  | TmLet t ->
    let collectParams = lam body : Expr.
      recursive let work = lam params : [(Name, FutType)]. lam body : Expr.
        match body with TmLam t then
          let params = snoc params (t.ident, generateType t.tyIdent) in
          work params t.body
        else (params, body)
      in
      work [] body
    in
    recursive let findReturnType = lam ty : Type.
      match ty with TyArrow t then
        findReturnType t.to
      else ty
    in
    let decl =
      match collectParams t.body with (params, body) then
        if null params then
          FDeclConst {ident = t.ident, ty = generateType t.tyBody,
                      val = generateExpr body}
        else
          let retTy = findReturnType t.tyBody in
          FDeclFun {ident = t.ident, entry = true, typeParams = [],
                    params = params, ret = generateType retTy,
                    body = generateExpr body}
      else never
    in
    cons decl (generateToplevel t.inexpr)
  | _ -> []
end

lang FutharkGenerate = FutharkToplevelGenerate
  sem generateProgram =
  | prog ->
    let preamble = [getDef ()] in
    FProg {decls = concat preamble (generateToplevel prog)}
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
let t = typeAnnot (symbolize (bindall_ [
  let_ "a" (tyseq_ tyint_) (seq_ [int_ 1, int_ 2, int_ 3]),
  let_ "b" (tyseq_ tyfloat_) (seq_ [float_ 2.718, float_ 3.14]),
  let_ "c" (tyrecord_ [("a", tyint_), ("b", tyfloat_)])
           (record_ [("a", int_ 3), ("b", float_ 2.0)]),
  nlet_ fName (tyarrows_ [tyint_, tyint_, tyint_])
              (lam_ "a" tyint_ (lam_ "b" tyint_ (addi_ (var_ "a") (var_ "b")))),
  nlet_ gName (tyarrows_ [tyseq_ tyfloat_, tyfloat_, tyfloat_])
              (lam_ "r" (tyseq_ tyfloat_)
                (lam_ "f" tyfloat_ (addf_ (var_ "f") (get_ (var_ "r") (int_ 0))))),
  nlet_ minName (tyarrows_ [tyint_, tyint_, tyint_])
                (lam_ "a" tyint_ (lam_ "b" tyint_ (
                  if_ (geqi_ (var_ "a") (var_ "b")) (var_ "b") (var_ "a")))),
  nlet_ mapFunc (tyarrows_ [tyarrow_ tyint_ tyint_, tyseq_ tyint_, tyseq_ tyint_])
                (lam_ "f" (tyarrow_ tyint_ tyint_) (lam_ "s" (tyseq_ tyint_)
                  (parallelMap_ (var_ "f") (var_ "s")))),
  unit_
])) in
let entryPoints = setInsert fName (setEmpty nameCmp) in
let p = generateProgram entryPoints t in
print (expr2str p);
()
