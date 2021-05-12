include "ast.mc"
include "ast-builder.mc"
include "pprint.mc"

include "set.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"

let get = ref (nameNoSym "")
let getFn = lam.
  let n = deref get in
  if nameHasSym n then
    n
  else
    modref get (nameSym "get");
    deref get
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

lang FutharkGenerate = MExprAst + FutharkAst
  sem generateProgram (entryPoints : Set Name) =
  | prog ->
    let preamble = [getDef ()] in
    FProg {decls = concat preamble (generateToplevel entryPoints prog)}

  sem generateToplevel (entryPoints : Set Name) =
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
                      val = generate body}
        else
          let isEntry = setMem t.ident entryPoints in
          let retTy = findReturnType t.tyBody in
          FDeclFun {ident = t.ident, entry = isEntry, typeParams = [],
                    params = params, ret = generateType retTy,
                    body = generate body}
      else never
    in
    cons decl (generateToplevel entryPoints t.inexpr)
  | _ -> []

  sem generate =
  | TmVar t -> FEVar {ident = t.ident}
  | TmRecord t -> FERecord {fields = mapMap generate t.bindings}
  | TmSeq {tms = tms} -> futArray_ (map generate tms)
  | TmConst c -> generateConst c.val
  | TmLam t -> nFutLam_ t.ident (generate t.body)
  | TmApp t -> FEApp {lhs = generate t.lhs, rhs = generate t.rhs}
  | TmLet t ->
    FELet {ident = t.ident, ty = generateType t.ty,
           body = generate t.body,
           inexpr = generate t.inexpr}

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
  | CGet () -> nFutVar_ (getFn ())

  sem generateType =
  | TyInt _ -> futIntTy_
  | TyFloat _ -> futFloatTy_
  | TySeq {ty = elemTy} -> futUnsizedArrayTy_ (generateType elemTy)
  | TyRecord {fields = fields} ->
    FTyRecord {fields = mapMap generateType fields}
  | TyUnknown _ -> error "Cannot translate unknown type to Futhark"
end

lang TestLang = FutharkGenerate + FutharkPrettyPrint + MExprSym + MExprTypeAnnot

mexpr

use TestLang in

let fName = nameSym "f" in
let gName = nameSym "g" in
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
  unit_
])) in
let entryPoints = setInsert fName (setEmpty nameCmp) in
let p = generateProgram entryPoints t in
print (expr2str p)
