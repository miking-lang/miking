include "mlang/ast.mc"

include "mexpr/ast.mc"

include "name.mc"

lang SynProdExtDeclAst = DeclAst
  syn Decl =
  | SynDeclProdExt {ident : Name,
                    params : [Name],
                    globalExt : Option Type,
                    individualExts : [{ident : Name, tyIdent : Type, tyName : Name}],
                    includes : [(String, String)],
                    info : Info}

  sem infoDecl =
  | SynDeclProdExt {info = info} -> info

  sem smapAccumL_Decl_Type f acc =
  | SynDeclProdExt x ->
    let f = lam acc. lam def.
      match f acc def.tyIdent with (acc, tyIdent) in
      (acc, {def with tyIdent = tyIdent}) in
    match mapAccumL f acc x.individualExts with (acc, individualExts) in
    (acc, SynDeclProdExt {x with individualExts = individualExts})
end

lang CosynDeclAst = DeclAst + Ast
  syn Decl =
  | DeclCosyn {info : Info,
               ident : Name,
               params : [Name],
               isBase : Bool,
               ty : Type,
               includes : [(String, String)]}
end

lang CopatAst
  syn Copat =

  sem copatInfo =

  sem copatWithInfo info =
end

lang RecordCopatAst = CopatAst
  syn Copat =
  | RecordCopat {info : Info,
                 fields : [String]}

  sem copatInfo =
  | RecordCopat c -> c.info

  sem copatWithInfo info =
  | RecordCopat c -> {RecordCopat c with info = info}
end

lang CosemDeclAst = DeclAst + CopatAst + Ast
  syn Decl =
  | DeclCosem {info : Info,
               ident : Name,
               args : [{ident : Name, tyAnnot : Type}],
               cases : [(Copat, Expr)],
               includes : [(String, String)],
               isBase : Bool,
               tyAnnot : Type,
               targetTyIdent : Name}

  sem infoDecl =
  | DeclCosem d -> d.info

  sem smapAccumL_Decl_Type f acc =
  | DeclCosem x ->
    let farg = lam acc. lam arg.
      match f acc arg.tyAnnot with (acc, tyAnnot) in
      (acc, {arg with tyAnnot = tyAnnot}) in
    match f acc x.tyAnnot with (acc, tyAnnot) in
    match mapAccumL farg acc x.args with (acc, args) in
    (acc, DeclCosem {x with args = args, tyAnnot = tyAnnot})
end

lang ExtRecordAst = Ast
  syn Expr =
  | TmRecType {ident : Name,
               params : [Name],
               ty : Type,
               inexpr : Expr,
               info : Info}
  | TmRecField {label : String,
                tyIdent : Type,
                inexpr : Expr,
                ty : Type,
                info : Info}
  | TmExtRecord  {bindings : Map String Expr,
                  ident : Name,
                  ty : Type,
                  info : Info}
  | TmExtExtend {e : Expr,
                 bindings : Map String Expr,
                 ty : Type,
                 info : Info}

  sem infoTm =
  | TmRecField t -> t.info
  | TmRecType t -> t.info
  | TmExtRecord t -> t.info
  | TmExtExtend t -> t.info

  sem tyTm =
  | TmRecField t -> t.ty
  | TmRecType t -> t.ty
  | TmExtRecord t -> t.ty
  | TmExtExtend t -> t.ty

  sem withInfo info =
  | TmRecField t -> TmRecField {t with info = info}
  | TmRecType t -> TmRecType {t with info = info}
  | TmExtRecord t -> TmExtRecord {t with info = info}
  | TmExtExtend t -> TmExtExtend {t with info = info}

  sem withType  ty =
  | TmRecField t -> TmRecField {t with ty = ty}
  | TmRecType t -> TmRecType {t with ty = ty}
  | TmExtRecord t -> TmExtRecord {t with ty = ty}
  | TmExtExtend t -> TmExtExtend {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc =
  | TmRecType t ->
    match f acc t.inexpr with (acc, inexpr) in
    (acc, TmRecType {t with inexpr = inexpr})
  | TmRecField t ->
    match f acc t.inexpr with (acc, inexpr) in
    (acc, TmRecField {t with inexpr = inexpr})
  | TmExtRecord t ->
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc t.bindings with (acc, bindings) in
    (acc, TmExtRecord {t with bindings = bindings})
  | TmExtExtend t ->
    match f acc t.e with (acc, e) in
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc t.bindings
    with (acc, bindings) in
    (acc, TmExtExtend {t with e = e, bindings = bindings})

  sem smapAccumL_Expr_Type f acc =
  | TmRecType t ->
    match f acc t.ty with (acc, ty) in
    (acc, TmRecType {t with ty = ty})
  | TmRecField t ->
    match f acc t.tyIdent with (acc, tyIdent) in
    match f acc t.ty with (acc, ty) in
    (acc, TmRecField {t with tyIdent = tyIdent,
                             ty = ty})
  | TmExtRecord t ->
    match f acc t.ty with (acc, ty) in
    (acc, TmExtRecord {t with ty = ty})
  | TmExtExtend t ->
    match f acc t.ty with (acc, ty) in
    (acc, TmExtExtend {t with ty = ty})
end

lang TypeAbsAst = Ast
  syn Type =
  | TyAbs {ident : Name,
           kind : Kind,
           body : Type}

  sem tyWithInfo info =
  | TyAbs _ & t -> t

  sem smapAccumL_Type_Type f acc =
  | TyAbs t ->
    match f acc t.body with (acc, body) in
    (acc, TyAbs {t with body = body})
end

lang TypeAbsAppAst = Ast
  syn Type =
  | TyAbsApp {lhs : Type,
              rhs : Type}

  sem tyWithInfo info =
  | TyAbsApp _ & t -> t

  sem smapAccumL_Type_Type f acc =
  | TyAbsApp t ->
    match f acc t.lhs with (acc, lhs) in
    match f acc t.rhs with (acc, rhs) in
    (acc, TyAbsApp {t with lhs = lhs, rhs = rhs})
end

lang ExtRecordPat = MatchAst
  syn Pat =
  | PatExtRecord {ident : Name,
                  bindings : Map SID Pat,
                  info : Info,
                  ty : Type}

  sem infoPat =
  | PatExtRecord r -> r.info

  sem withInfoPat info =
  | PatExtRecord r -> PatExtRecord {r with info = info}

  sem tyPat =
  | PatExtRecord r -> r.ty

  sem withTypePat (ty : Type) =
  | PatExtRecord r -> PatExtRecord {r with ty = ty}

  sem smapAccumL_Pat_Pat f acc =
  | PatExtRecord p ->
    match mapMapAccum (lam acc. lam. lam p. f acc p) acc p.bindings with (acc, bindings) then
      (acc, PatExtRecord {p with bindings = bindings})
    else never
end

lang QualifiedTypeAst = Ast
  syn Type =
  | TyQualifiedName {pos : Bool,
                     info : Info,
                     lhs : Name,
                     rhs : Name,
                     plus : [(Name, Name)],
                     minus : [(Name, Name)]}

  sem tyWithInfo info =
  | TyQualifiedName t -> TyQualifiedName {t with info = info}

  sem infoTy =
  | TyQualifiedName {info = info} -> info
end

lang ExtRecAst = SynProdExtDeclAst + CosynDeclAst + CopatAst + RecordCopatAst +
                 CosemDeclAst + ExtRecordAst + TypeAbsAppAst + TypeAbsAst +
                 ExtRecordPat + QualifiedTypeAst
end