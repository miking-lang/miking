include "map.mc"
include "string.mc"
include "c/ast.mc"
include "c/pprint.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

let cWrapperNamesRef = ref (None ())
let _genCWrapperNames = lam.
  let identifiers =
    ["malloc", "free", "value", "size_t", "int64_t", "Long_val", "Bool_val",
    "Double_val", "Val_long", "Val_bool", "Val_double", "Wosize_val",
    "caml_alloc", "Field", "Store_field", "Double_field", "Store_double_field",
    "Double_array_tag"]
  in
  mapFromSeq
    cmpString
    (map (lam s. (s, nameSym s)) identifiers)
let getCWrapperNames = lam.
  match deref cWrapperNamesRef with Some names then names
  else
    let names = _genCWrapperNames () in
    modref cWrapperNamesRef (Some names);
    names
let _getIdentExn = lam str.
  match mapLookup str (getCWrapperNames ()) with Some id then id
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

lang FutharkOCamlToCWrapper = MExprAst + CAst
  sem _wosize =
  | id ->
      CEApp {fun = _getIdentExn "Wosize_val", args = [CEVar {id = id}]}

  sem _assignConvertedTerm (dstIdent : Name) (fnId : String) =
  | srcIdent ->
    CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEUnOp {op = CODeref (), arg = CEVar {id = dstIdent}},
      rhs = CEApp {fun = _getIdentExn fnId, args = [CEVar {id = srcIdent}]}}}

  sem _generateOCamlToCSequenceWrapper (elemTy : CType) (iterId : Name)
                                       (srcIdent : Name) (dstIdents : [Name]) =
  | whileBody /- : Name -> Name -> [CStmt] -/ ->
    let accessIndex = lam idxExpr.
      CEBinOp {op = COSubScript (), lhs = CEVar {id = srcIdent}, rhs = idxExpr}
    in
    let sizeId = nameSym "n" in
    let iterationIndex = CSDef {
      ty = CTyInt (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let size = CSDef {
      ty = CTyInt (), id = Some sizeId,
      init = Some (CIExpr {expr = _wosize srcIdent})} in
    [ iterationIndex
    , size
    , CSWhile {
        cond = CEBinOp {op = COLt (), lhs = CEVar {id = iterId},
                        rhs = CEVar {id = sizeId}},
        body = whileBody}]

  sem _generateOCamlToCWrapperInner (elemTy : CType) (srcIdent : Name) (dstIdents : [Name]) =
  | TyInt _ | TyChar _ ->
    let dstIdent = head dstIdents in
    [_assignConvertedTerm dstIdent "Long_val" srcIdent]
  | TyFloat _ ->
    let dstIdent = head dstIdents in
    [_assignConvertedTerm dstIdent "Double_val" srcIdent]
  | TySeq {ty = TyFloat _} ->
    let dstIdent = head dstIdents in
    let iterId = nameSym "i" in
    _generateOCamlToCSequenceWrapper elemTy iterId srcIdent dstIdents
      [CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEBinOp {
          op = COSubScript (),
          lhs = CEVar {id = dstIdent},
          rhs = CEVar {id = iterId}},
        rhs = CEApp {fun = _getIdentExn "Double_field",
                     args = [CEVar {id = srcIdent}, CEVar {id = iterId}]}}},
      CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEVar {id = iterId},
        rhs = CEBinOp {
          op = COAdd (),
          lhs = CEVar {id = iterId},
          rhs = CEInt {i = 1}}}}]
  | TySeq {ty = innerTy} ->
    let iterId = nameSym "i" in
    let innerSrcId = nameSym "x" in
    let innerDstIdents = map (lam. nameSym "y") dstIdents in
    let innerDstAssignments =
      map
        (lam idents: (Name, Name).
          let dstIdent = idents.0 in
          let innerDstIdent = idents.1 in
          let offset =
            match innerTy with TySeq _ then
              CEBinOp {
                op = COMul (),
                lhs = CEVar {id = iterId},
                rhs = _wosize innerSrcId}
            else CEVar {id = iterId} in
          CSDef {
            ty = CTyPtr {ty = elemTy}, id = Some innerDstIdent,
            init = Some (CIExpr {expr = CEBinOp {
              op = COSubScript (),
              lhs = CEVar {id = dstIdent},
              rhs = offset}})})
        (zip dstIdents innerDstIdents) in
    let whileBody = join [
      [CSDef {
        ty = CTyVar {id = _getIdentExn "value"}, id = Some innerSrcId,
        init = Some (CIExpr {expr = CEApp {
          fun = _getIdentExn "Field",
          args = [CEVar {id = srcIdent}, CEVar {id = iterId}]}})}],
      innerDstAssignments,
      _generateOCamlToCWrapperInner elemTy innerSrcId innerDstIdents innerTy,
      [CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEVar {id = iterId},
        rhs = CEBinOp {
          op = COAdd (), lhs = CEVar {id = iterId},
          rhs = CEInt {i = 1}}}}]] in
    _generateOCamlToCSequenceWrapper elemTy iterId srcIdent dstIdents whileBody
end

lang FutharkCWrapper = MExprAst + CAst + CProgAst + FutharkOCamlToCWrapper
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
  | TySeq {elem = TyInt _ | TyChar _} ->
    let cIdent = nameSym "t" in
    let ptrTy = CTyPtr {ty = CTyVar {id = _getIdentExn "int64_t"}} in
    let size = CEBinOp {
      op = COMul (),
      lhs = CEApp {fun = _getIdentExn "Wosize_val", args = [ident]},
      rhs = CESizeOfType {ty = CTyVar {id = _getIdentExn "int64_t"}}} in
    let ocamlToC = concat env.ocamlToC [
      CSDef {
        ty = ptrTy,
        id = Some cIdent,
        init = Some (CIExpr {
          expr = CECast {ty = ptrTy,
                         rhs = CEApp {fun = _getIdentExn "malloc",
                                      args = size}}})}] in
    let cToFuthark = concat env.cToFuthark [
      
    ] in
    {{env with ocamlToC = ocamlToC}
          with cToFuthark = cToFuthark}
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

lang Test = FutharkOCamlToCWrapper + CPrettyPrint

mexpr

use Test in

let elemTy = CTyVar {id = _getIdentExn "int64_t"} in
let srcIdent = nameSym "src" in
let dstIdents = [nameSym "dst"] in
let ocamlArgTy = tyseq_ (tyseq_ (tyseq_ tyfloat_)) in
print (printCStmts 0 pprintEnvEmpty
  (_generateOCamlToCWrapperInner elemTy srcIdent dstIdents ocamlArgTy)).1

