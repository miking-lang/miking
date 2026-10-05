-- Comparison functions for the MLang-level extensions to the MExpr AST

include "ast.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/cmp.mc"
include "mexpr/info.mc"

include "basic-types.mc"
include "name.mc"
include "option.mc"
include "seq.mc"
include "string.mc"

lang UseDeclCmp = Cmp + UseDeclAst
  sem cmpDeclH +=
  | (DeclUse l, DeclUse r) -> nameCmp l.ident r.ident
end

lang TyUseCmp = Cmp + TyUseAst
  sem cmpTypeH +=
  | (TyUse l, TyUse r) ->
    let identDiff = nameCmp l.ident r.ident in
    if eqi identDiff 0 then cmpType l.inty r.inty
    else identDiff
end

lang IncludeDeclCmp = Cmp + IncludeDeclAst
  sem cmpDeclH +=
  | (DeclInclude l, DeclInclude r) -> cmpString l.path r.path
end

lang SynDeclCmp = Cmp + SynDeclAst
  -- `syn Foo =` and `syn Foo +=` differ only in this kind.
  sem cmpSynDeclKind : (SynDeclKind, SynDeclKind) -> Int
  sem cmpSynDeclKind =
  | (SynBase _, SynBase _) -> 0
  | (SynSum l, SynSum r) -> nameCmp l.base r.base
  | (lhs, rhs) -> subi (constructorTag lhs) (constructorTag rhs)

  sem cmpSynDef
    : {ident : Name, tyIdent : Type, info : Info}
    -> {ident : Name, tyIdent : Type, info : Info}
    -> Int
  sem cmpSynDef lhs =
  | rhs ->
    let identDiff = nameCmp lhs.ident rhs.ident in
    if eqi identDiff 0 then cmpType lhs.tyIdent rhs.tyIdent
    else identDiff

  sem cmpDeclH +=
  | (DeclSyn l, DeclSyn r) ->
    let identDiff = nameCmp l.ident r.ident in
    if neqi identDiff 0 then identDiff else
    let paramsDiff = seqCmp nameCmp l.params r.params in
    if neqi paramsDiff 0 then paramsDiff else
    let defsDiff = seqCmp cmpSynDef l.defs r.defs in
    if neqi defsDiff 0 then defsDiff else
    cmpSynDeclKind (l.kind, r.kind)
end

lang SemDeclCmp = Cmp + SemDeclAst
  -- `sem foo =` and `sem foo +=` differ only in this kind.
  sem cmpSemDeclKind : (SemDeclKind, SemDeclKind) -> Int
  sem cmpSemDeclKind =
  | (SemBase _, SemBase _) -> 0
  | (SemSum l, SemSum r) -> nameCmp l.base r.base
  | (lhs, rhs) -> subi (constructorTag lhs) (constructorTag rhs)

  sem cmpSemParam
    : {ident : Name, tyAnnot : Type, tyParam : Type, info : Info}
    -> {ident : Name, tyAnnot : Type, tyParam : Type, info : Info}
    -> Int
  sem cmpSemParam lhs =
  | rhs ->
    let identDiff = nameCmp lhs.ident rhs.ident in
    if eqi identDiff 0 then cmpType lhs.tyAnnot rhs.tyAnnot
    else identDiff

  sem cmpSemCase
    : {pat : Pat, body : Expr, info : Info}
    -> {pat : Pat, body : Expr, info : Info}
    -> Int
  sem cmpSemCase lhs =
  | rhs ->
    let patDiff = cmpPat lhs.pat rhs.pat in
    if eqi patDiff 0 then cmpExpr lhs.body rhs.body
    else patDiff

  sem cmpSemImpl
    : {params : [{ident : Name, tyAnnot : Type, tyParam : Type, info : Info}],
       cases : [{pat : Pat, body : Expr, info : Info}]}
    -> {params : [{ident : Name, tyAnnot : Type, tyParam : Type, info : Info}],
        cases : [{pat : Pat, body : Expr, info : Info}]}
    -> Int
  sem cmpSemImpl lhs =
  | rhs ->
    let paramsDiff = seqCmp cmpSemParam lhs.params rhs.params in
    if eqi paramsDiff 0 then seqCmp cmpSemCase lhs.cases rhs.cases
    else paramsDiff

  sem cmpDeclH +=
  | (DeclSem l, DeclSem r) ->
    let identDiff = nameCmp l.ident r.ident in
    if neqi identDiff 0 then identDiff else
    -- `tyAnnot` is the written signature (`sem foo : T`); `tyBody` is
    -- inferred later and thus not compared.
    let tyDiff = cmpType l.tyAnnot r.tyAnnot in
    if neqi tyDiff 0 then tyDiff else
    let implDiff = optionCmp cmpSemImpl l.impl r.impl in
    if neqi implDiff 0 then implDiff else
    cmpSemDeclKind (l.kind, r.kind)
end

lang LangDeclCmp = Cmp + LangDeclAst
  sem cmpLangInclude : (Name, Info) -> (Name, Info) -> Int
  sem cmpLangInclude lhs =
  | rhs -> nameCmp lhs.0 rhs.0

  sem cmpDeclH +=
  | (DeclLang l, DeclLang r) ->
    let identDiff = nameCmp l.ident r.ident in
    if neqi identDiff 0 then identDiff else
    let includesDiff = seqCmp cmpLangInclude l.includes r.includes in
    if neqi includesDiff 0 then includesDiff else
    seqCmp cmpDecl l.decls r.decls
end

lang MLangProgramCmp = Cmp + MLangTopLevel
  sem cmpProgram : MLangProgram -> MLangProgram -> Int
  sem cmpProgram lhs =
  | rhs ->
    let declsDiff = seqCmp cmpDecl lhs.decls rhs.decls in
    if eqi declsDiff 0 then cmpExpr lhs.expr rhs.expr
    else declsDiff
end

lang MLangCmp =
  MExprCmp + MLangProgramCmp +
  UseDeclCmp + TyUseCmp + IncludeDeclCmp + SynDeclCmp + SemDeclCmp + LangDeclCmp
end

mexpr

use MLangCmp in

let n = nameNoSym in
let i = NoInfo () in

let use_ = lam s. DeclUse {ident = n s, info = i} in
let include_ = lam s. DeclInclude {path = s, info = i} in
let synDef_ = lam s. lam ty. {ident = n s, tyIdent = ty, info = i} in
let syn_ = lam s. lam params. lam defs. lam kind.
  DeclSyn {ident = n s, params = map n params, defs = defs, info = i, kind = kind}
in
let semParam_ = lam s.
  {ident = n s, tyAnnot = tyunknown_, tyParam = tyunknown_, info = i} in
let semCase_ = lam p. lam b. {pat = p, body = b, info = i} in
let sem_ = lam s. lam tyAnnot. lam impl. lam kind.
  DeclSem {ident = n s, tyAnnot = tyAnnot, tyBody = tyunknown_,
           impl = impl, info = i, kind = kind}
in
let lang_ = lam s. lam includes. lam decls.
  DeclLang {ident = n s, includes = map (lam x. (n x, i)) includes,
            decls = decls, info = i}
in

-- `info` is ignored, so a differing one must not make two nodes differ.
utest cmpDecl (use_ "L") (DeclUse {ident = n "L", info = Info
  {filename = "f", row1 = 1, col1 = 0, row2 = 1, col2 = 1}}) with 0 in

utest cmpDecl (use_ "L") (use_ "L") with 0 in
utest cmpDecl (use_ "L") (use_ "M") with 0 using neqi in

utest cmpType (TyUse {ident = n "L", inty = tyint_, info = i})
              (TyUse {ident = n "L", inty = tyint_, info = i}) with 0 in
utest cmpType (TyUse {ident = n "L", inty = tyint_, info = i})
              (TyUse {ident = n "M", inty = tyint_, info = i}) with 0 using neqi in
utest cmpType (TyUse {ident = n "L", inty = tyint_, info = i})
              (TyUse {ident = n "L", inty = tybool_, info = i}) with 0 using neqi in

utest cmpDecl (include_ "a.mc") (include_ "a.mc") with 0 in
utest cmpDecl (include_ "a.mc") (include_ "b.mc") with 0 using neqi in

-- Two decls of different kinds are ordered, not equal.
utest cmpDecl (use_ "L") (include_ "a.mc") with 0 using neqi in

let synA = syn_ "Expr" ["a"] [synDef_ "TmInt" tyint_] (SynBase ()) in
utest cmpDecl synA (syn_ "Expr" ["a"] [synDef_ "TmInt" tyint_] (SynBase ())) with 0 in
utest cmpDecl synA (syn_ "Type" ["a"] [synDef_ "TmInt" tyint_] (SynBase ())) with 0
using neqi in
utest cmpDecl synA (syn_ "Expr" ["b"] [synDef_ "TmInt" tyint_] (SynBase ())) with 0
using neqi in
utest cmpDecl synA (syn_ "Expr" [] [synDef_ "TmInt" tyint_] (SynBase ())) with 0
using neqi in
utest cmpDecl synA (syn_ "Expr" ["a"] [synDef_ "TmFloat" tyint_] (SynBase ())) with 0
using neqi in
utest cmpDecl synA (syn_ "Expr" ["a"] [synDef_ "TmInt" tybool_] (SynBase ())) with 0
using neqi in
-- `syn Expr =` and `syn Expr +=` differ only in their kind.
utest cmpDecl synA (syn_ "Expr" ["a"] [synDef_ "TmInt" tyint_] (SynSum {base = n "B"}))
with 0 using neqi in
utest cmpSynDeclKind (SynSum {base = n "B"}, SynSum {base = n "B"}) with 0 in
utest cmpSynDeclKind (SynSum {base = n "B"}, SynSum {base = n "C"}) with 0 using neqi in

let impl1 = Some {params = [semParam_ "x"], cases = [semCase_ (pvar_ "p") (var_ "p")]} in
let semA = sem_ "f" tyunknown_ impl1 (SemBase ()) in
utest cmpDecl semA (sem_ "f" tyunknown_ impl1 (SemBase ())) with 0 in
utest cmpDecl semA (sem_ "g" tyunknown_ impl1 (SemBase ())) with 0 using neqi in
utest cmpDecl semA (sem_ "f" (tyarrow_ tyint_ tyint_) impl1 (SemBase ())) with 0
using neqi in
utest cmpDecl semA (sem_ "f" tyunknown_ (None ()) (SemBase ())) with 0 using neqi in
utest cmpDecl semA
  (sem_ "f" tyunknown_
    (Some {params = [semParam_ "y"], cases = [semCase_ (pvar_ "p") (var_ "p")]})
    (SemBase ()))
with 0 using neqi in
utest cmpDecl semA
  (sem_ "f" tyunknown_
    (Some {params = [semParam_ "x"], cases = [semCase_ (pvar_ "q") (var_ "p")]})
    (SemBase ()))
with 0 using neqi in
utest cmpDecl semA
  (sem_ "f" tyunknown_
    (Some {params = [semParam_ "x"], cases = [semCase_ (pvar_ "p") (var_ "q")]})
    (SemBase ()))
with 0 using neqi in
utest cmpDecl semA (sem_ "f" tyunknown_ impl1 (SemSum {base = n "B"})) with 0
using neqi in
utest cmpSemDeclKind (SemSum {base = n "B"}, SemSum {base = n "B"}) with 0 in
utest cmpSemDeclKind (SemSum {base = n "B"}, SemSum {base = n "C"}) with 0 using neqi in

-- `tyBody` is inferred rather than written, and so is deliberately not compared.
utest
  cmpDecl semA
    (DeclSem {ident = n "f", tyAnnot = tyunknown_, tyBody = tyint_,
              impl = impl1, info = i, kind = SemBase ()})
with 0 in

let langA = lang_ "L" ["A"] [synA] in
utest cmpDecl langA (lang_ "L" ["A"] [synA]) with 0 in
utest cmpDecl langA (lang_ "M" ["A"] [synA]) with 0 using neqi in
utest cmpDecl langA (lang_ "L" ["B"] [synA]) with 0 using neqi in
utest cmpDecl langA (lang_ "L" [] [synA]) with 0 using neqi in
utest cmpDecl langA (lang_ "L" ["A"] [synA, semA]) with 0 using neqi in

utest cmpProgram {decls = [langA], expr = int_ 1}
                 {decls = [langA], expr = int_ 1} with 0 in
utest cmpProgram {decls = [langA], expr = int_ 1}
                 {decls = [langA], expr = int_ 2} with 0 using neqi in
utest cmpProgram {decls = [langA], expr = int_ 1}
                 {decls = [], expr = int_ 1} with 0 using neqi in

-- The ordering is antisymmetric.
utest gti (cmpDecl (use_ "M") (use_ "L")) 0
with lti (cmpDecl (use_ "L") (use_ "M")) 0 in
utest gti (cmpDecl langA (lang_ "L" ["A"] [synA, semA])) 0
with lti (cmpDecl (lang_ "L" ["A"] [synA, semA]) langA) 0 in

()
