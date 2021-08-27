include "map.mc"
include "string.mc"
include "c/ast.mc"

let cWrapperNamesRef = ref (None ())
let _genCWrapperNames = lam.
  let identifiers =
    ["value", "int64_t", "Long_val", "Bool_val", "Double_val", "Val_long",
     "Val_bool", "Val_double"]
  in
  mapFromSeq
    cmpString
    (map (lam s. (s, nameSym s)) [])
let getCWrapperNames = lam.
  match deref cWrapperNamesRef with Some names then names
  else
    let names = _genCWrapperNames () in
    modref cWrapperNamesRef (Some names)
    names
let _getIdentExn = lam str.
  match mapLookup str (getCWrapperNames) with Some id then id
  else error (concat "Undefined string " str)

type FutharkCWrapperEnv = {
  ocamlToC : [CStmt],
  cToFuthark : [CStmt],
  futharkToC : [CStmt],
  cToOCaml : [CStmt],
  args : [(Name, Type)]
}

let emptyWrapperEnv = {
  ocamlToC = [], cToFuthark = [], futharkToC = [], cToOCaml = [], args = []
}

lang FutharkCWrapper = MExprAst + CAst + CProgAst
  sem _generateWrapperForInputArg (env : FutharkCWrapperEnv) (ident : Name) =
  | TyInt _ | TyChar _ ->
    let cIdent = nameSym "t" in
    let ocamlToC = concat env.ocamlToC [
      CSDef {
        ty = CTyVar {id = _getIdentExn "int64_t"},
        id = Some cIdent,
        init = Some (CIExpr {expr = CEApp {fun = _getIdentExn "Long_val",
                                           args = [ident]}})}] in
    {env with ocamlToC = ocamlToC}
  | TyBool _ ->
    let cIdent = nameSym "t" in
    let ocamlToC = concat env.ocamlToC [
      CSDef {
        ty = CTyInt {},
        id = Some cIdent,
        init = Some (CIExpr {expr = CEApp {fun = _getIdentExn "Bool_val",
                                           args = [ident]}})}] in
    {env with ocamlToC = ocamlToC}
  | TyFloat _ ->
    let cIdent = nameSym "t" in
    let ocamlToC = concat env.ocamlToC [
      CSDef {
        ty = CTyDouble {},
        id = Some cIdent,
        init = Some (CIExpr {expr = CEApp {fun = _getIdentExn "Double_val",
                                           args = [ident]}})}] in
    {env with ocamlToC = ocamlToC}
  | TySeq t ->
    error "Wrapping of sequence types not yet implemented"
  | TyRecord t ->
    error "Wrapping of record types not yet implemented"

  sem _generateCWrapper (env : FutharkCWrapperEnv) =
  | TyArrow t ->
    let argIdent = nameSym "x" in
    let env = _generateWrapperForInputArg env argIdent t.from in
    let env = {env with args = snoc env.args (argIdent, t.from)} in
    _generateCWrapper env t.to
  | ty ->
    error "function return type handling not yet implemented"
    -- This is the return type of the function

  sem generateFutharkWrapperFunction =
  | (ident, ty) /- : (Name, Type) -/ ->
    let env = emptyWrapperEnv in
    match mapAccumL _generateCWrapper env ty with (env, retTy) then
      CTFun {
        ret = (),
        id = ident,
        params = [],
        body = join [env.ocamlToC, env.cToFuthark, env.futharkToC, env.cToOcaml]
      }
    else never

  sem generateFutharkWrapper =
  | accelerated /- : Map Name Type -/ ->
    -- NOTE(larshum, 2021-08-27): According to
    -- https://ocaml.org/manual/intfc.html CAML_NAME_SPACE should be defined
    -- before including caml headers, but the current C AST does not support
    -- this.
    CPProg {
      includes = [
        "<stddef.h>",
        "<stdlib.h>",
        "\"program.h\"",
        "\"caml/alloc.h\"",
        "\"caml/memory.h\"",
        "\"caml/mlvalues.h\""
      ],
      tops = map generateFutharkWrapperFunction (mapBindings accelerated)
    }
end
