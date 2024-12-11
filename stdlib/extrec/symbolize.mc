include "mexpr/symbolize.mc"

include "mlang/symbolize.mc"

include "ast.mc"

lang ExtRecordSym = Sym + ExtRecordAst

  sem symbolizeExpr env =
  | TmRecType t ->
    match setSymbol env.currentEnv.tyConEnv t.ident with (tyConEnv, ident) in
    let env = symbolizeUpdateTyConEnv env tyConEnv in 

    let params = map (setSymbol env.currentEnv.tyVarEnv) t.params in
    let params = map snd params in 

    TmRecType {t with ident = ident,
                      params = params,
                      inexpr = symbolizeExpr env t.inexpr}
  | TmRecField t -> 
    TmRecField {t with inexpr = symbolizeExpr env t.inexpr,
                       tyIdent = symbolizeType env t.tyIdent}
  | TmExtRecord t ->
    let ident = getSymbol {kind = "type constructor", 
                           info = [t.info],
                           allowFree = env.allowFree} env.currentEnv.tyConEnv t.ident in 
    let bindings = mapMap (symbolizeExpr env) t.bindings in 
    TmExtRecord {t with ident = ident, bindings = bindings}
  | TmExtExtend t ->
    let e = symbolizeExpr env t.e in 
    let bindings = mapMap (symbolizeExpr env) t.bindings in 
    TmExtExtend {t with bindings = bindings, e = e}
  | TmExtProject t -> 
    let ident= getSymbol {kind = "type constructor", 
                          info = [t.info],
                          allowFree = env.allowFree} env.currentEnv.tyConEnv t.ident in 
    -- let ident = t.ident in 
    TmExtProject {t with ident = ident, e = symbolizeExpr env t.e}
end