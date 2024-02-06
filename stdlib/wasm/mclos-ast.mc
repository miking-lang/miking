include "mexpr/ast.mc"

lang MClosAst = MExprAst
    syn Expr = 
    | TmFuncDef {funcIdent: Name,
                 argIdent: Name,
                 body: Expr,
                 env: [String],
                 tyAnnot: Type,
                 tyParam: Type,
                 ty: Type,
                 info: Info}
    | TMEnvVar {ident : Name,
                ty: Type,
                info: Info,
                frozen: Bool}
    | TmEnvAdd String

    sem infoTm =
    | TmFuncDef t -> t.info

    sem tyTm =
    | TmFuncDef t -> t.ty

    sem withInfo (info : Info) =
    | TmFuncDef t -> TmFuncDef {t with info = info}

    sem withType (ty : Type) =
    | TmFuncDef t -> TmFuncDef {t with ty = ty}

    sem smapAccumL_Expr_Type (f : acc -> Type -> (acc, Type)) (acc : acc) =
    | TmFuncDef t ->
        match f acc t.tyAnnot with (acc, tyAnnot) in
        (acc, TmFuncDef {t with tyAnnot = tyAnnot})

    sem smapAccumL_Expr_TypeLabel (f : acc -> Type -> (acc, Type)) (acc : acc) =
    | TmFuncDef t ->
        match f acc t.tyParam with (acc, tyParam) in
        match f acc t.ty with (acc, ty) in
        (acc, TmFuncDef {t with tyParam = tyParam, ty = ty})

    sem smapAccumL_Expr_Expr (f : acc -> Expr -> (acc, Expr)) (acc : acc) =
    | TmFuncDef t ->
        match f acc t.body with (acc, body) in
        (acc, TmFuncDef {t with body = body})
end