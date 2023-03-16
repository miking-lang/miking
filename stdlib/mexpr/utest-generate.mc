-- Defines the generation of unit test code from utest expressions. This
-- includes a small runtime which keeps track of the number of failing tests
-- (defined in stdlib/mexpr/utest-runtime.mc), as well as the automated
-- generation of equality functions for comparing the arguments (unless
-- one is provided by the user) and pretty-print functions for printing the
-- arguments in case they are not equal.
--
-- The implementation supports automatic generation of equality and
-- pretty-print functions for all built-in types, with a few exceptions and
-- limitations:
-- * Pretty-printing of references use a hard-coded string literal instead of
-- inspecting the referenced value, as references may be cyclic. For the same
-- reason, an equality function must be user-defined. This includes all types
-- that may contain a reference.
-- * Boot parse trees are treated similarly, because they require a lot of work
-- to properly support.
-- * It assumes that a variant type is not extended with more constructors
-- after the first time it is used (in a utest). It would be possible to
-- support, by keeping track of which constructors were introduced at each
-- utest. As it was not required to pass all tests, this has not been
-- implemented.

include "stdlib.mc"
include "mexpr/ast.mc"
include "mexpr/boot-parser.mc"
include "mexpr/builtin.mc"
include "mexpr/cmp.mc"
include "mexpr/duplicate-code-elimination.mc"
include "mexpr/eval.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "mexpr/utils.mc"

let _utestRuntimeLoc = "/mexpr/utest-runtime.mc"


let _utestRuntimeExpected = [
  "utestRunner", "utestExitOnFailure", "defaultPprint", "ppBool", "ppInt",
  "ppFloat", "ppChar", "ppSeq", "eqBool", "eqInt", "eqFloat", "eqChar",
  "eqSeq", "join"
]
let _utestRuntimeCode = ref (None ())
let _utestRuntimeIds = ref (None ())

let resetStore = lam. modref _utestRuntimeCode (None ());
                 modref _utestRuntimeIds (None ());
                 ()

let _pprintId = ref 0
let _eqId = ref 0
let newRecordPprintName = lam.
  modref _pprintId (addi (deref _pprintId) 1);
  let idx = deref _pprintId in
  nameSym (concat "ppRecord" (int2string idx))
let newRecordEqualityName = lam.
  modref _eqId (addi (deref _eqId) 1);
  let idx = deref _eqId in
  nameSym (concat "eqRecord" (int2string idx))

let _ppSeqName = nameSym "ppSeq"
let _ppSeqTyVarName = nameSym "a"
let _eqSeqName = nameSym "eqSeq"
let _eqSeqTyVarName = nameSym "a"
let _ppTensorName = nameSym "ppTensor"
let _ppTensorTyVarName = nameSym "a"
let _eqTensorName = nameSym "eqTensor"
let _eqTensorTyVarName = nameSym "a"

let _builtinTypes = map (lam s. nameNoSym s.0) builtinTypes

let _utestInfo =
  let pos = initPos "utest-generated" in
  makeInfo pos pos

-- AST builder functions defined specifically for the utest generation. These
-- include an info-field to signify the origin of the generated code, and they
-- require concrete type information.
-- NOTE(larshum, 2022-12-30): Should these be merged with the AST-builder
-- functions?
let _boolTy = use MExprAst in TyBool {info = _utestInfo}
let _intTy = use MExprAst in TyInt {info = _utestInfo}
let _charTy = use MExprAst in TyChar {info = _utestInfo}
let _floatTy = use MExprAst in TyFloat {info = _utestInfo}
let _seqTy = lam ty.
  use MExprAst in
  TySeq {ty = ty, info = _utestInfo}
let _stringTy = _seqTy _charTy
let _tensorTy = lam ty.
  use MExprAst in
  TyTensor {ty = ty, info = _utestInfo}
let _conTy = lam id.
  use MExprAst in
  TyCon {ident = id, info = _utestInfo}
let _varTy = lam id.
  use MExprAst in
  TyVar {ident = id, info = _utestInfo}
let _recordTy = lam fields.
  use MExprAst in
  let fields = map (lam f. match f with (s, ty) in (stringToSid s, ty)) fields in
  TyRecord {fields = mapFromSeq cmpSID fields, info = _utestInfo}
let _tupleTy = lam types.
  _recordTy (mapi (lam i. lam ty. (int2string i, ty)) types)
let _unitTy = _recordTy []
let _tyarrows = lam tys.
  use MExprAst in
  foldr1
    (lam ty. lam acc. TyArrow {from = ty, to = acc, info = _utestInfo})
    tys
let _tyalls = lam vars. lam ty.
  use MExprAst in
  if null vars then error "" else
  foldr
    (lam tyvar. lam acc.
      TyAll {ident = tyvar, sort = PolyVar (), ty = acc,
             info = _utestInfo})
    ty vars
recursive let _pprintTy = lam ty.
  use MExprAst in
  match ty with TySeq {ty = elemTy} | TyTensor {ty = elemTy} then
    _tyarrows [_tyarrows [elemTy, _stringTy], ty, _stringTy]
  else _tyarrows [ty, _stringTy]
end
recursive let _eqTy = lam ty.
  use MExprAst in
  match ty with TySeq {ty = elemTy} | TyTensor {ty = elemTy} then
    _tyarrows [_tyarrows [elemTy, elemTy, _boolTy], ty, ty, _boolTy]
  else _tyarrows [ty, ty, _boolTy]
end

let _patVar = lam id. lam ty.
  use MExprAst in
  PatNamed {ident = PName id, ty = ty, info = _utestInfo}
let _patBool = lam b.
  use MExprAst in
  PatBool {val = b, ty = _boolTy, info = _utestInfo}
let _patRecord = lam bindings. lam ty.
  use MExprAst in
  let bindings = map (lam b. match b with (s, p) in (stringToSid s, p)) bindings in
  PatRecord {bindings = mapFromSeq cmpSID bindings, ty = ty, info = _utestInfo}
let _patTuple = lam args. lam ty.
  let binds = mapi (lam i. lam arg. (int2string i, arg)) args in
  _patRecord binds ty
let _patCon = lam id. lam subpat. lam ty.
  use MExprAst in
  PatCon {ident = id, subpat = subpat, ty = ty, info = _utestInfo}

let _bool = lam b.
  use MExprAst in
  TmConst {val = CBool {val = b}, ty = _boolTy, info = _utestInfo}
let _true = _bool true
let _false = _bool false
let _var = lam id. lam ty.
  use MExprAst in
  TmVar {ident = id, ty = ty, info = _utestInfo, frozen = false}
let _lam = lam id. lam ty. lam body.
  use MExprAst in
  TmLam {ident = id, tyAnnot = ty, tyParam = ty, body = body,
         ty = _tyarrows [ty, tyTm body], info = _utestInfo}
let _seq = lam tms. lam ty.
  use MExprAst in
  TmSeq {tms = tms,  ty = ty, info = _utestInfo}
let _stringLit = lam s.
  use MExprAst in
  let char2tm = lam c.
    TmConst {val = CChar {val = c}, ty = _charTy, info = _utestInfo}
  in
  _seq (map char2tm s) _stringTy
let _record = lam binds. lam ty.
  use MExprAst in
  let binds = map (lam b. match b with (s, e) in (stringToSid s, e)) binds in
  TmRecord {bindings = mapFromSeq cmpSID binds, ty = ty, info = _utestInfo}
let _tuple = lam exprs. lam ty.
  let exprs = mapi (lam i. lam e. (int2string i, e)) exprs in
  _record exprs ty
let _match = lam target. lam pat. lam thn. lam els. lam ty.
  use MExprAst in
  TmMatch {
    target = target, pat = pat, thn = thn, els = els,
    ty = ty, info = _utestInfo}
let _never = lam ty.
  use MExprAst in
  TmNever {ty = ty, info = _utestInfo}
let _recordproj = lam key. lam fieldTy. lam r.
  use MExprAst in
  let fieldId = nameSym "x" in
  _match r
    (_patRecord [(sidToString key, _patVar fieldId fieldTy)] (tyTm r))
    (_var fieldId fieldTy) (_never fieldTy) fieldTy
let _unit = _record [] _unitTy
let _recbind = lam id. lam ty. lam body.
  use MExprAst in
  {ident = id, tyAnnot = ty, tyBody = ty, body = body, info = _utestInfo}
recursive let _bind = lam f. lam bind. lam expr.
  use MExprAst in
  let ty = tyTm expr in
  switch bind
  case TmLet t then TmLet {t with inexpr = _bind f t.inexpr expr, ty = ty}
  case TmRecLets t then TmRecLets {t with inexpr = _bind f t.inexpr expr, ty = ty}
  case TmType t then TmType {t with inexpr = _bind f t.inexpr expr, ty = ty}
  case TmConDef t then TmConDef {t with inexpr = _bind f t.inexpr expr, ty = ty}
  case TmExt t then TmExt {t with inexpr = _bind f t.inexpr expr, ty = ty}
  case _ then f bind expr
  end
end
let _binds = lam bindings.
  use MExprAst in
  foldr1 (_bind (lam. lam expr. expr)) bindings
let _apps = lam fun. lam args.
  use MExprAst in
  foldl
    (lam acc. lam arg.
      match tyTm acc with TyArrow {to = to} then
        TmApp {lhs = acc, rhs = arg, ty = to, info = _utestInfo}
      else error "Invalid type of utest application")
    fun args
let _const = lam c. lam ty.
  use MExprAst in
  TmConst {val = c, ty = ty, info = _utestInfo}
let _concat =
  use MExprAst in
  _const (CConcat ()) (_tyarrows [_stringTy, _stringTy, _stringTy])

-- The base fragment for the utest generation. This defines the utest
-- environment as well as basic functions used in the generation of utest code.
lang UtestBase =
  UnknownTypeCmp + BoolTypeCmp + IntTypeCmp + FloatTypeCmp + CharTypeCmp +
  FunTypeCmp + RecordTypeCmp + VariantTypeCmp + ConTypeCmp + VarTypeCmp +
  AppTypeCmp + AllTypeCmp + SeqTypeAst + TensorTypeAst + TypeCheck

  -- NOTE(larshum, 2022-12-26): We customize the comparison of types such that
  -- all sequence and tensor types are considered equal. This is because we
  -- reuse the polymorphic functions for printing and equality for all sequence
  -- and tensor types.
  sem cmpTypeH =
  | (TySeq _, TySeq _) -> 0
  | (TyTensor _, TyTensor _) -> 0

  type UtestEnv = {
    -- Maps a type to the identifier of its pretty-print or equality function,
    -- respectively.
    pprint : Map Type Name,
    eq : Map Type Name,

    -- Set containing the types for which we have defined a pretty-print or
    -- equality function, respectively.
    pprintDef : Set Type,
    eqDef : Set Type,

    -- Maps the identifier of a variant type to an inner map, which in turn
    -- maps constructor names to their types.
    variants : Map Name (Map Name Type)
  }

  sem utestEnvEmpty : () -> UtestEnv
  sem utestEnvEmpty =
  | _ ->
    let baseTypes = [_boolTy, _intTy, _charTy, _floatTy] in
    { eq = mapEmpty cmpType, eqDef = setOfSeq cmpType baseTypes
    , pprint = mapEmpty cmpType, pprintDef = setOfSeq cmpType baseTypes
    , variants = mapEmpty nameCmp }

  sem lookupVariant : Name -> UtestEnv -> Info -> Map Name Type
  sem lookupVariant id env =
  | info ->
    match mapLookup id env.variants with Some constrs then constrs
    else errorSingle [info] "Unknown constructor type"

  -- Performs an unwrapping of all alias types.
  sem unwrapAlias : Type -> Type
  sem unwrapAlias =
  | ty -> smap_Type_Type unwrapAlias (unwrapType ty)

  -- Produces a sequence of the direct "child" types of a given type.
  sem shallowInnerTypes : UtestEnv -> Type -> [Type]
  sem shallowInnerTypes env =
  | ty ->
    let types = shallowInnerTypesH env ty in
    map unwrapAlias types

  sem shallowInnerTypesH : UtestEnv -> Type -> [Type]
  sem shallowInnerTypesH env =
  | TySeq {ty = elemTy} | TyTensor {ty = elemTy} -> [elemTy]
  | TyRecord {fields = fields} -> mapValues fields
  | (TyApp _ | TyCon _) & ty ->
    match collectTypeArguments [] ty with (id, tyArgs) in
    -- NOTE(larshum, 2022-12-29): Built-in types are handled differently, as
    -- they do not have any defined constructors.
    if any (nameEq id) _builtinTypes then tyArgs
    else
      let constrs = lookupVariant id env (infoTy ty) in
      let constrArgTypes = mapMapWithKey (specializeConstructorArgument tyArgs) constrs in
      mapValues constrArgTypes
  | _ -> []

  -- Generates an expression of type 'ty -> String' which we can use to
  -- pretty-print a value of type 'ty'.
  sem getPrettyPrintExpr : Info -> UtestEnv -> Type -> (UtestEnv, Expr)
  sem getPrettyPrintExpr info env =
  | ty -> getPrettyPrintExprH info env (unwrapAlias ty)

  sem getPrettyPrintExprH : Info -> UtestEnv -> Type -> (UtestEnv, Expr)
  sem getPrettyPrintExprH info env =
  | (TySeq {ty = elemTy} | TyTensor {ty = elemTy}) & ty ->
    match prettyPrintId info env ty with (env, pprintId) in
    match getPrettyPrintExprH info env elemTy with (env, ppElem) in
    (env, _apps (_var pprintId (_pprintTy ty)) [ppElem])
  | ty ->
    match
      match mapLookup ty env.pprint with Some pprintId then (env, pprintId)
      else
        match prettyPrintId info env ty with (env, pprintId) in
        let innerTypes = shallowInnerTypes env ty in
        match mapAccumL (getPrettyPrintExprH info) env innerTypes with (env, _) in
        (env, pprintId)
    with (env, pprintId) in
    (env, _var pprintId (_pprintTy ty))

  -- Generates an expression of type 'ty -> ty -> bool' which we can use to
  -- determine equality of values of type 'ty'.
  sem getEqualityExpr : Info -> UtestEnv -> Type -> (UtestEnv, Expr)
  sem getEqualityExpr info env =
  | ty -> getEqualityExprH info env (unwrapAlias ty)

  sem getEqualityExprH : Info -> UtestEnv -> Type -> (UtestEnv, Expr)
  sem getEqualityExprH info env =
  | (TySeq {ty = elemTy} | TyTensor {ty = elemTy}) & ty ->
    match equalityId info env ty with (env, eqId) in
    match getEqualityExprH info env elemTy with (env, elemEq) in
    (env, _apps (_var eqId (_eqTy ty)) [elemEq])
  | ty ->
    match
      match mapLookup ty env.eq with Some eqId then (env, eqId)
      else
        match equalityId info env ty with (env, eqId) in
        let innerTypes = shallowInnerTypes env ty in
        match mapAccumL (getEqualityExprH info) env innerTypes with (env, _) in
        (env, eqId)
    with (env, eqId) in
    (env, _var eqId (_eqTy ty))

  -- Generates an identifier for the pretty-print or equality function for a
  -- given type, respectively. We use this before generating the bodies of the
  -- functions to avoid infinite recursion when handling recursive ADTs.
  sem prettyPrintId : Info -> UtestEnv -> Type -> (UtestEnv, Name)
  sem equalityId : Info -> UtestEnv -> Type -> (UtestEnv, Name)

  -- Generates a body for the pretty-print or equality functions of a given
  -- type. These functions must be used after their corresponding functions
  -- above, so that an ID has already been generated for the tpye.
  sem generatePrettyPrintBody : Info -> UtestEnv -> Type -> (Name, Expr)
  sem generateEqualityBody : Info -> UtestEnv -> Type -> (Name, Expr)

  sem collectTypeArguments : [Type] -> Type -> (Name, [Type])
  sem collectTypeArguments args =
  | TyApp {lhs = lhs, rhs = rhs} ->
    collectTypeArguments (cons rhs args) lhs
  | TyCon {ident = ident} -> (ident, args)
  | ty -> errorSingle [infoTy ty] "Unexpected shape of type application"

  -- Specializes the argument type of a constructor given the type of the
  -- applied arguments.
  sem specializeConstructorArgument : [Type] -> Name -> Type -> Type
  sem specializeConstructorArgument tyArgs key =
  | constructorType ->
    specializeConstructorArgumentH (mapEmpty nameCmp) (tyArgs, constructorType)

  sem specializeConstructorArgumentH : Map Name Type -> ([Type], Type) -> Type
  sem specializeConstructorArgumentH subMap =
  | ([], TyArrow {from = argTy}) -> substituteVars subMap argTy
  | ([tyArg] ++ tyArgs, TyAll {ident = ident, ty = ty}) ->
    specializeConstructorArgumentH
      (mapInsert ident tyArg subMap) (tyArgs, ty)
  | (_, ty) -> errorSingle [infoTy ty] "Invalid constructor application"
end

-- The language fragment for handling the utest runtime. This includes a
-- function that produces a typed AST for the runtime file (utest-runtime.mc),
-- as well as functions for accessing identifiers defined in the runtime file.
lang UtestRuntime = BootParser + MExprSym + MExprTypeCheck + MExprFindSym

  sem loadRuntime : String -> Expr
  sem loadRuntime =
  | file ->
    match deref _utestRuntimeCode with Some ast then ast
    else
      let args = defaultBootParserParseMCoreFileArg in
      let utestRuntimeFile = concat stdlibLoc file in
      let ast = typeCheck (symbolize (parseMCoreFile args utestRuntimeFile)) in
      modref _utestRuntimeCode (Some ast);
      ast

  sem loadUtestRuntime : () -> Expr
  sem loadUtestRuntime =
  | _ -> loadRuntime _utestRuntimeLoc

  sem findRuntimeIds : [String] -> String -> [Name]
  sem findRuntimeIds expected =
  | file ->
    match deref _utestRuntimeIds with Some ids then ids
    else
      let rt = loadRuntime file in
      match optionMapM identity (findNamesOfStrings expected rt)
      with Some ids then
        modref _utestRuntimeIds (Some ids);
        ids
      else error "Missing required identifiers in utest runtime file"

  sem findUtestRuntimeIds : () -> [Name]
  sem findUtestRuntimeIds =
  | _ -> findRuntimeIds _utestRuntimeExpected _utestRuntimeLoc

  sem utestRunnerName : () -> Name
  sem utestRunnerName =
  | _ -> get (findUtestRuntimeIds ()) 0

  sem utestExitOnFailureName : () -> Name
  sem utestExitOnFailureName =
  | _ -> get (findUtestRuntimeIds ()) 1

  sem defaultPrettyPrintName : () -> Name
  sem defaultPrettyPrintName =
  | _ -> get (findUtestRuntimeIds ()) 2

  sem ppBoolName : () -> Name
  sem ppBoolName =
  | _ -> get (findUtestRuntimeIds ()) 3

  sem ppIntName : () -> Name
  sem ppIntName =
  | _ -> get (findUtestRuntimeIds ()) 4

  sem ppFloatName : () -> Name
  sem ppFloatName =
  | _ -> get (findUtestRuntimeIds ()) 5

  sem ppCharName : () -> Name
  sem ppCharName =
  | _ -> get (findUtestRuntimeIds ()) 6

  sem ppSeqName : () -> Name
  sem ppSeqName =
  | _ -> get (findUtestRuntimeIds ()) 7

  sem eqBoolName : () -> Name
  sem eqBoolName =
  | _ -> get (findUtestRuntimeIds ()) 8

  sem eqIntName : () -> Name
  sem eqIntName =
  | _ -> get (findUtestRuntimeIds ()) 9

  sem eqFloatName : () -> Name
  sem eqFloatName =
  | _ -> get (findUtestRuntimeIds ()) 10

  sem eqCharName : () -> Name
  sem eqCharName =
  | _ -> get (findUtestRuntimeIds ()) 11

  sem eqSeqName : () -> Name
  sem eqSeqName =
  | _ -> get (findUtestRuntimeIds ()) 12

  sem joinName : () -> Name
  sem joinName =
  | _ -> get (findUtestRuntimeIds ()) 13
end

lang GeneratePrettyPrintBase = UtestBase + UtestRuntime + MExprAst
  sem prettyPrintId : Info -> UtestEnv -> Type -> (UtestEnv, Name)
  sem prettyPrintId info env =
  | ty ->
    let id = prettyPrintIdH info env ty in
    ({env with pprint = mapInsert ty id env.pprint}, id)

  sem prettyPrintIdH : Info -> UtestEnv -> Type -> Name
  sem prettyPrintIdH info env =
  | ty -> defaultPrettyPrintName ()

  sem generatePrettyPrintBody : Info -> UtestEnv -> Type -> (Name, Expr)
  sem generatePrettyPrintBody info env =
  | ty ->
    match mapLookup ty env.pprint with Some id then
      (id, generatePrettyPrintBodyH info env ty)
    else
      errorSingle [info]
        (concat "Cannot generate pretty-print function for type " (type2str ty))

  sem generatePrettyPrintBodyH : Info -> UtestEnv -> Type -> Expr
  sem generatePrettyPrintBodyH info env =
  | ty -> _unit
end

lang BoolPrettyPrint = GeneratePrettyPrintBase + UtestRuntime
  sem prettyPrintIdH info env =
  | TyBool _ -> ppBoolName ()
end

lang IntPrettyPrint = GeneratePrettyPrintBase + UtestRuntime
  sem prettyPrintIdH info env =
  | TyInt _ -> ppIntName ()
end

lang FloatPrettyPrint = GeneratePrettyPrintBase + UtestRuntime
  sem prettyPrintIdH info env =
  | TyFloat _ -> ppFloatName ()
end

lang CharPrettyPrint = GeneratePrettyPrintBase + UtestRuntime
  sem prettyPrintIdH info env =
  | TyChar _ -> ppCharName ()
end

lang SeqPrettyPrint = GeneratePrettyPrintBase + UtestRuntime
  sem prettyPrintIdH info env =
  | TySeq _ -> _ppSeqName

  sem generatePrettyPrintBodyH info env =
  | TySeq t ->
    let ppElem = nameSym "ppElem" in
    let target = nameSym "s" in
    let elemTy = _varTy _ppSeqTyVarName in
    let ty = TySeq {t with ty = elemTy} in
    let ppSeq = _var (ppSeqName ()) (_pprintTy (_seqTy elemTy)) in
    _lam ppElem (_pprintTy elemTy) (_lam target ty
      (_apps ppSeq [_var ppElem (_pprintTy elemTy), _var target ty]))
end

lang TensorPrettyPrint = GeneratePrettyPrintBase + UtestRuntime
  sem prettyPrintIdH info env =
  | TyTensor _ -> _ppTensorName

  sem generatePrettyPrintBodyH info env =
  | TyTensor t ->
    let ppElem = nameSym "ppElem" in
    let target = nameSym "t" in
    let elemTy = _varTy _ppTensorTyVarName in
    let ty = TyTensor {t with ty = elemTy} in
    let tensorPp = _const (CTensorToString ()) (_pprintTy (_tensorTy elemTy)) in
    _lam ppElem (_pprintTy elemTy) (_lam target ty
      (_apps tensorPp [_var ppElem (_pprintTy elemTy), _var target ty]))
end

lang RecordPrettyPrint = GeneratePrettyPrintBase + UtestRuntime
  sem prettyPrintIdH info env =
  | TyRecord _ & ty ->
    match mapLookup ty env.pprint with Some id then id
    else newRecordPprintName ()

  sem generatePrettyPrintBodyH info env =
  | TyRecord {fields = fields} & ty ->
    recursive let intersperseComma : [Expr] -> [Expr] = lam strExprs.
      match strExprs with [] | [_] then
        strExprs
      else match strExprs with [expr] ++ strExprs then
        concat [expr, _stringLit ", "] (intersperseComma strExprs)
      else never
    in
    let recordId = nameSym "r" in
    let record = _var recordId ty in
    let printSeq =
      match record2tuple fields with Some types then
        let printTupleField = lam count. lam fieldTy.
          match getPrettyPrintExpr info env fieldTy with (_, ppExpr) in
          let key = stringToSid (int2string count) in
          (addi count 1, _apps ppExpr [_recordproj key fieldTy record])
        in
        match mapAccumL printTupleField 0 types with (_, strs) in
        join [[_stringLit "("], intersperseComma strs, [_stringLit ")"]]
      else
        let printRecordField = lam fields. lam sid. lam fieldTy.
          match getPrettyPrintExpr info env fieldTy with (_, ppExpr) in
          let str =
            _apps _concat
              [ _stringLit (concat (sidToString sid) " = ")
              , _apps ppExpr [_recordproj sid fieldTy record] ]
          in
          snoc fields str
        in
        let strs = mapFoldWithKey printRecordField [] fields in
        join [[_stringLit "{"], intersperseComma strs, [_stringLit "}"]]
    in
    let pprint =
      _apps
        (_var (joinName ()) (_tyarrows [_seqTy _stringTy, _stringTy]))
        [seq_ printSeq]
    in
    _lam recordId ty pprint
end

lang VariantPrettyPrint = GeneratePrettyPrintBase + UtestRuntime
  sem prettyPrintIdH info env =
  | (TyApp _ | TyCon _) & ty ->
    match mapLookup ty env.pprint with Some id then id
    else
      match collectTypeArguments [] ty with (id, argTypes) in
      nameSym (concat (concat "pp" (nameGetStr id)) (strJoin "" (map type2str argTypes)))

  sem generatePrettyPrintBodyH info env =
  | (TyApp _ | TyCon _) & ty ->
    match collectTypeArguments [] ty with (id, tyArgs) in
    if nameEq id (nameNoSym "Symbol") then
      generateSymbolPrettyPrint env ty
    else if nameEq id (nameNoSym "Ref") then
      generateReferencePrettyPrint env ty
    else if nameEq id (nameNoSym "BootParseTree") then
      generateBootParseTreePrettyPrint env ty
    else defaultVariantPrettyPrint info env id tyArgs ty

  sem generateSymbolPrettyPrint : UtestEnv -> Type -> Expr
  sem generateSymbolPrettyPrint env =
  | ty ->
    let target = nameSym "s" in
    let ppInt = _var (ppIntName ()) (_pprintTy _intTy) in
    let symHash =
      _apps (_const (CSym2hash ()) (_tyarrows [ty, _intTy]))
        [_var target ty] in
    _lam target ty
      (_apps _concat
        [ _stringLit "sym ("
        , _apps _concat [_apps ppInt [symHash], _stringLit ")"] ])

  sem generateReferencePrettyPrint : UtestEnv -> Type -> Expr
  sem generateReferencePrettyPrint env =
  | ty -> _lam (nameNoSym "") ty (_stringLit "<ref>")

  sem generateBootParseTreePrettyPrint : UtestEnv -> Type -> Expr
  sem generateBootParseTreePrettyPrint env =
  | ty -> _lam (nameNoSym "") ty (_stringLit "<boot parse tree>")

  sem defaultVariantPrettyPrint : Info -> UtestEnv -> Name -> [Type] -> Type -> Expr
  sem defaultVariantPrettyPrint info env id tyArgs =
  | ty ->
    let constrs = lookupVariant id env info in
    let constrArgTypes = mapMapWithKey (specializeConstructorArgument tyArgs) constrs in
    let target = nameSym "a" in
    let constrPprint = lam acc. lam constrId. lam constrArgTy.
      match getPrettyPrintExpr info env constrArgTy with (_, ppExpr) in
      let innerId = nameSym "x" in
      let thn =
        _apps _concat
          [ _stringLit (concat (nameGetStr constrId) " ")
          , _apps ppExpr [_var innerId constrArgTy] ]
      in
      _match (_var target ty)
        (_patCon constrId (_patVar innerId constrArgTy) ty)
        thn acc _stringTy
    in
    let body = mapFoldWithKey constrPprint (_never _stringTy) constrArgTypes in
    _lam target ty body
end

lang MExprGeneratePrettyPrint =
  BoolPrettyPrint + IntPrettyPrint + FloatPrettyPrint + CharPrettyPrint +
  SeqPrettyPrint + TensorPrettyPrint + RecordPrettyPrint + VariantPrettyPrint
end

lang GenerateEqualityBase = UtestBase + MExprAst + PrettyPrint
  sem equalityId : Info -> UtestEnv -> Type -> (UtestEnv, Name)
  sem equalityId info env =
  | ty ->
    let id = equalityIdH info env ty in
    ({env with eq = mapInsert ty id env.eq}, id)

  sem equalityIdH : Info -> UtestEnv -> Type -> Name
  sem equalityIdH info env =
  | ty ->
    let msg = join [
      "A custom equality function is required for type ", type2str ty, ".\n"
    ] in
    errorSingle [info] msg

  sem generateEqualityBody : Info -> UtestEnv -> Type -> (Name, Expr)
  sem generateEqualityBody info env =
  | ty ->
    match mapLookup ty env.eq with Some id then
      (id, generateEqualityBodyH info env ty)
    else
      errorSingle [infoTy ty]
        (concat "Cannot generate equality function for type " (type2str ty))

  sem generateEqualityBodyH : Info -> UtestEnv -> Type -> Expr
  sem generateEqualityBodyH info env =
  | ty ->
    errorSingle [infoTy ty]
      (concat "Cannot generate equality function for type " (type2str ty))
end

lang BoolEquality = GenerateEqualityBase + UtestRuntime
  sem equalityIdH info env =
  | TyBool _ -> eqBoolName ()

  sem generateEqualityBodyH info env =
  | TyBool _ -> _unit
end

lang IntEquality = GenerateEqualityBase + UtestRuntime
  sem equalityIdH info env =
  | TyInt _ -> eqIntName ()

  sem generateEqualityBodyH info env =
  | TyInt _ -> _unit
end

lang FloatEquality = GenerateEqualityBase + UtestRuntime
  sem equalityIdH info env =
  | TyFloat _ -> eqFloatName ()

  sem generateEqualityBodyH info env =
  | TyFloat _ -> _unit
end

lang CharEquality = GenerateEqualityBase + UtestRuntime
  sem equalityIdH info env =
  | TyChar _ -> eqCharName ()

  sem generateEqualityBodyH info env =
  | TyChar _ -> _unit
end

lang SeqEquality = GenerateEqualityBase + UtestRuntime
  sem equalityIdH info env =
  | TySeq _ -> _eqSeqName

  sem generateEqualityBodyH info env =
  | TySeq t ->
    let eqElem = nameSym "eqElem" in
    let larg = nameSym "l" in
    let rarg = nameSym "r" in
    let elemTy = _varTy _eqSeqTyVarName in
    let ty = TySeq {t with ty = elemTy} in
    let eqSeq = _var (eqSeqName ()) (_eqTy (_seqTy elemTy)) in
    _lam eqElem (_eqTy elemTy) (_lam larg ty (_lam rarg ty
      (_apps eqSeq [_var eqElem (_eqTy elemTy), _var larg ty, _var rarg ty])))
end

lang TensorEquality = GenerateEqualityBase + UtestRuntime
  sem equalityIdH info env =
  | TyTensor _ -> _eqTensorName

  sem generateEqualityBodyH info env =
  | TyTensor t ->
    let eqElem = nameSym "eqElem" in
    let larg = nameSym "l" in
    let rarg = nameSym "r" in
    let elemTy = _varTy _eqTensorTyVarName in
    let ty = TyTensor {t with ty = elemTy} in
    let tensorEq = _const (CTensorEq ()) (_eqTy (_tensorTy elemTy)) in
    _lam eqElem (_eqTy elemTy) (_lam larg ty (_lam rarg ty
      (_apps tensorEq [_var eqElem (_eqTy elemTy), _var larg ty, _var rarg ty])))
end

lang RecordEquality = GenerateEqualityBase + UtestRuntime
  sem equalityIdH info env =
  | TyRecord _ & ty ->
    match mapLookup ty env.eq with Some id then id
    else newRecordEqualityName ()

  sem generateEqualityBodyH info env =
  | TyRecord {fields = fields} & ty ->
    let larg = nameSym "l" in
    let rarg = nameSym "r" in
    let fieldEqual = lam acc. lam fieldSid. lam fieldTy.
      match getEqualityExpr info env fieldTy with (_, eqExpr) in
      let l = _recordproj fieldSid fieldTy (_var larg ty) in
      let r = _recordproj fieldSid fieldTy (_var rarg ty) in
      let cond = _apps eqExpr [l, r] in
      let truePat = PatBool {val = true, ty = _boolTy, info = _utestInfo} in
      _match cond truePat acc _false _boolTy
    in
    let body = mapFoldWithKey fieldEqual _true fields in
    _lam larg ty (_lam rarg ty body)
end

lang VariantEquality = GenerateEqualityBase + UtestRuntime
  sem equalityIdH info env =
  | (TyApp _ | TyCon _) & ty ->
    match mapLookup ty env.eq with Some id then id
    else
      match collectTypeArguments [] ty with (id, argTypes) in
      nameSym (concat (concat "eq" (nameGetStr id)) (strJoin "" (map type2str argTypes)))

  sem generateEqualityBodyH info env =
  | (TyCon _ | TyApp _) & ty ->
    match collectTypeArguments [] ty with (id, tyArgs) in
    if nameEq id (nameNoSym "Symbol") then
      generateSymbolEquality info env ty
    else if nameEq id (nameNoSym "Ref") then
      generateReferenceEquality info env ty
    else if nameEq id (nameNoSym "BootParseTree") then
      generateBootParseTreeEquality info env ty
    else defaultVariantEq info env id tyArgs ty

  sem generateSymbolEquality : Info -> UtestEnv -> Type -> Expr
  sem generateSymbolEquality info env =
  | ty ->
    let larg = nameSym "l" in
    let rarg = nameSym "r" in
    let eqsym = _const (CEqsym ()) (_tyarrows [ty, ty, _boolTy]) in
    _lam larg ty (_lam rarg ty (_apps eqsym [_var larg ty, _var rarg ty]))

  sem generateReferenceEquality : Info -> UtestEnv -> Type -> Expr
  sem generateReferenceEquality info env =
  | ty ->
    errorSingle [info]
      "A custom equality function must be provided for reference types.\n"

  sem generateBootParseTreeEquality : Info -> UtestEnv -> Type -> Expr
  sem generateBootParseTreeEquality info env =
  | ty -> errorSingle [info] "Cannot generate equality for boot parse trees"

  sem defaultVariantEq : Info -> UtestEnv -> Name -> [Type] -> Type -> Expr
  sem defaultVariantEq info env id tyArgs =
  | ty ->
    let constrs = lookupVariant id env info in
    let constrArgTypes = mapMapWithKey (specializeConstructorArgument tyArgs) constrs in
    let larg = nameSym "l" in
    let rarg = nameSym "r" in
    let lid = nameSym "lhs" in
    let rid = nameSym "rhs" in
    let constrEq = lam acc. lam constrId. lam constrArgTy.
      match getEqualityExpr info env constrArgTy with (_, argEq) in
      let target = _tuple [_var larg ty, _var rarg ty] (_tupleTy [ty, ty]) in
      let conPat = lam id. lam argTy. _patCon constrId (_patVar id argTy) ty in
      let pat =
        _patTuple [conPat lid constrArgTy, conPat rid constrArgTy]
          (_tupleTy [ty, ty]) in
      let thn = _apps argEq [_var lid constrArgTy, _var rid constrArgTy] in
      _match target pat thn acc _boolTy
    in
    let body = mapFoldWithKey constrEq _false constrArgTypes in
    _lam larg ty (_lam rarg ty body)
end

lang MExprGenerateEquality =
  BoolEquality + IntEquality + FloatEquality + CharEquality + SeqEquality +
  TensorEquality + RecordEquality + VariantEquality
end

-- The main utest generation language fragment. Here, we define functions for
-- replacing utest expressions with references to the utest runtime, as well as
-- the insertion of recursive bindings for pretty-print and equality functions
-- into the original AST.
lang MExprUtestGenerate =
  UtestRuntime + MExprGeneratePrettyPrint + MExprGenerateEquality +
  MExprEliminateDuplicateCode

  -- Generates a recursive let-expression containing pretty-print binding
  -- definitions for each subtype required to support pretty-printing all
  -- types in the provided sequence.
  sem generatePrettyPrintBindings : Info -> UtestEnv -> [Type] -> (UtestEnv, Expr)
  sem generatePrettyPrintBindings info env =
  | types ->
    let types = map unwrapAlias types in
    match mapAccumL (generatePrettyPrintBindingsH info) env types with (env, binds) in
    ( env
    , TmRecLets {bindings = join binds, inexpr = _unit, ty = _unitTy,
                 info = _utestInfo} )

  sem generatePrettyPrintBindingsH : Info -> UtestEnv -> Type
                                  -> (UtestEnv, [RecLetBinding])
  sem generatePrettyPrintBindingsH info env =
  | (TySeq {ty = elemTy} | TyTensor {ty = elemTy}) & ty ->
    if setMem ty env.pprintDef then
      generatePrettyPrintBindingsH info env elemTy
    else
      match generatePrettyPrintBody info env ty with (id, body) in
      match generatePrettyPrintBindingsH info env elemTy with (env, binds) in
      let varId =
        match ty with TySeq _ then _ppSeqTyVarName
        else _ppTensorTyVarName
      in
      let ty =
        let elemTy = _varTy varId in
        switch ty
        case TySeq t then TySeq {t with ty = elemTy}
        case TyTensor t then TyTensor {t with ty = elemTy}
        end
      in
      let ppTy = _tyalls [varId] (_pprintTy ty) in
      (env, cons (_recbind id ppTy body) binds)
  | ty ->
    if setMem ty env.pprintDef then (env, [])
    else
      let env = {env with pprintDef = setInsert ty env.pprintDef} in
      let innerTys = shallowInnerTypes env ty in
      match mapAccumL (generatePrettyPrintBindingsH info) env innerTys with (env, binds) in
      match generatePrettyPrintBody info env ty with (id, body) in
      if nameEq id (defaultPrettyPrintName ()) then (env, join binds)
      else (env, cons (_recbind id (_pprintTy ty) body) (join binds))

  -- Conditionally generates a recursive let-expression containing equality
  -- binding definitions for all subtypes required to support an equality
  -- operation on the provided type. If a user has provided a custom equality
  -- function (i.e., the tusing field is Some), we do not generate any
  -- bindings.
  sem generateEqualityBindings : Info -> UtestEnv -> Type -> Option Expr
                              -> (UtestEnv, Expr)
  sem generateEqualityBindings info env ty =
  | Some _ -> (env, _unit)
  | None _ ->
    let ty = unwrapAlias ty in
    match generateEqualityBindingsH info env ty with (env, binds) in
    ( env
    , TmRecLets {bindings = binds, inexpr = _unit, ty = _unitTy, info = _utestInfo} )

  sem generateEqualityBindingsH : Info -> UtestEnv -> Type
                               -> (UtestEnv, [RecLetBinding])
  sem generateEqualityBindingsH info env =
  | (TySeq {ty = elemTy} | TyTensor {ty = elemTy}) & ty ->
    if setMem ty env.eqDef then
      generateEqualityBindingsH info env elemTy
    else
      match generateEqualityBody info env ty with (id, body) in
      match generateEqualityBindingsH info env elemTy with (env, binds) in
      let varId =
        match ty with TySeq _ then _eqSeqTyVarName
        else _eqTensorTyVarName
      in
      let ty =
        let elemTy = _varTy varId in
        switch ty
        case TySeq t then TySeq {t with ty = elemTy}
        case TyTensor t then TyTensor {t with ty = elemTy}
        end
      in
      let eqTy = _tyalls [varId] (_eqTy ty) in
      (env, cons (_recbind id eqTy body) binds)
  | ty ->
    if setMem ty env.eqDef then (env, [])
    else
      let env = {env with eqDef = setInsert ty env.eqDef} in
      let innerTys = shallowInnerTypes env ty in
      match mapAccumL (generateEqualityBindingsH info) env innerTys with (env, binds) in
      match generateEqualityBody info env ty with (id, body) in
      (env, cons (_recbind id (_eqTy ty) body) (join binds))

  -- Replaces all TmUtest expressions found in the provided AST, with support
  -- for nested utests.
  sem replaceUtests : UtestEnv -> Expr -> (UtestEnv, Expr)
  sem replaceUtests env =
  | TmUtest t ->
    let info = _stringLit (info2str t.info) in
    let usingStr =
      _stringLit
        (match t.tusing with Some eqfn then
          concat "\n    Using: " (expr2str eqfn)
        else "")
    in
    let lty = tyTm t.test in
    let rty = tyTm t.expected in
    match getPrettyPrintExpr t.info env lty with (env, lpp) in
    match getPrettyPrintExpr t.info env rty with (env, rpp) in
    match
      match t.tusing with Some eqfn then (env, eqfn)
      else
        -- NOTE(larshum, 2022-12-26): Both arguments to the utest must have the
        -- same type if no equality function was provided.
        getEqualityExpr t.info env lty
    with (env, eqfn) in
    let utestRunnerType =
      let infoTy = _stringTy in
      let usingStrTy = _stringTy in
      let lppTy = _tyarrows [lty, _stringTy] in
      let rppTy = _tyarrows [rty, _stringTy] in
      let eqTy = _tyarrows [lty, rty, _boolTy] in
      tyarrows_ [infoTy, usingStrTy, lppTy, rppTy, eqTy, lty, rty, _unitTy]
    in
    let utestRunner = TmVar {
      ident = utestRunnerName (), ty = utestRunnerType,
      info = _utestInfo, frozen = false
    } in

    -- Insert definitions of equality and pretty-print functions that have not
    -- yet been declared.
    match generatePrettyPrintBindings t.info env [lty, rty] with (env, ppBinds) in
    match generateEqualityBindings t.info env lty t.tusing with (env, eqBinds) in

    match replaceUtests env t.test with (_, test) in
    match replaceUtests env t.expected with (_, expected) in
    match replaceUtests env t.next with (env, next) in
    let testExpr =
      _apps utestRunner [info, usingStr, lpp, rpp, eqfn, test, expected]
    in
    let utestBinds = TmLet {
      ident = nameNoSym "", tyAnnot = _unitTy, tyBody = _unitTy,
      body = testExpr, inexpr = next, ty = tyTm next, info = t.info
    } in
    (env, _binds [eqBinds, ppBinds, utestBinds])
  | TmType t ->
    let env =
      match t.tyIdent with TyVariant _ then
        {env with variants = mapInsert t.ident (mapEmpty nameCmp) env.variants}
      else env
    in
    match replaceUtests env t.inexpr with (env, inexpr) in
    (env, TmType {t with inexpr = inexpr})
  | TmConDef t ->
    recursive let extractVariantType = lam ty.
      match ty with TyAll {ty = innerTy} then extractVariantType innerTy
      else match ty with TyArrow {to = to} then extractVariantType to
      else match ty with TyApp {lhs = lhs} then extractVariantType lhs
      else match ty with TyCon {ident = ident} then ident
      else errorSingle [t.info] "Invalid constructor definition"
    in
    let ident = extractVariantType t.tyIdent in
    let constrs = lookupVariant ident env t.info in
    let constrs = mapInsert t.ident t.tyIdent constrs in
    let env = {env with variants = mapInsert ident constrs env.variants} in
    match replaceUtests env t.inexpr with (env, inexpr) in
    (env, TmConDef {t with inexpr = inexpr})
  | TmLet t ->
    match replaceUtests env t.body with (_, body) in
    match replaceUtests env t.inexpr with (env, inexpr) in
    (env, TmLet {t with body = body, inexpr = inexpr})
  | TmRecLets t ->
    let replaceBinding = lam env. lam bind.
      match replaceUtests env bind.body with (env, body) in
      (env, {bind with body = body})
    in
    match mapAccumL replaceBinding env t.bindings with (_, bindings) in
    match replaceUtests env t.inexpr with (env, inexpr) in
    (env, TmRecLets {t with bindings = bindings, inexpr = inexpr})
  | t -> smapAccumL_Expr_Expr replaceUtests env t

  -- Inserts utest runtime code at the tail of the program. In case any test
  -- failed, this code ensures that the program exits with return code 1. The
  -- insertion is performed such that the final in-expression is always
  -- evaluated, regardless of whether tests failed or not.
  sem insertUtestTail : Expr -> Expr
  sem insertUtestTail =
  | TmLet t ->
    let inexpr = insertUtestTail t.inexpr in
    TmLet {t with inexpr = inexpr, ty = tyTm inexpr}
  | TmRecLets t ->
    let inexpr = insertUtestTail t.inexpr in
    TmRecLets {t with inexpr = inexpr, ty = tyTm inexpr}
  | TmType t ->
    let inexpr = insertUtestTail t.inexpr in
    TmType {t with inexpr = inexpr, ty = tyTm inexpr}
  | TmConDef t ->
    let inexpr = insertUtestTail t.inexpr in
    TmConDef {t with inexpr = inexpr, ty = tyTm inexpr}
  | TmUtest t ->
    let next = insertUtestTail t.next in
    TmUtest {t with next = next, ty = tyTm next}
  | TmExt t ->
    let inexpr = insertUtestTail t.inexpr in
    TmExt {t with inexpr = inexpr, ty = tyTm inexpr}
  | t ->
    let exitOnFailure =
      _var (utestExitOnFailureName ()) (_tyarrows [tyTm t, tyTm t]) in
    _apps exitOnFailure [t]

  -- Merges the AST with the utest header, which consists of the runtime
  -- definitions from 'utest-runtime.mc'.
  sem mergeWithUtestHeader : UtestEnv -> Expr -> Expr
  sem mergeWithUtestHeader env =
  | ast -> mergeWithUtestHeaderH env ast (loadUtestRuntime ())

  sem mergeWithUtestHeaderH : UtestEnv -> Expr -> Expr -> Expr
  sem mergeWithUtestHeaderH env ast =
  | TmLet t ->
    TmLet {t with inexpr = mergeWithUtestHeaderH env ast t.inexpr,
                  ty = tyTm ast}
  | TmRecLets t ->
    TmRecLets {t with inexpr = mergeWithUtestHeaderH env ast t.inexpr,
                      ty = tyTm ast}
  | TmType t ->
    TmType {t with inexpr = mergeWithUtestHeaderH env ast t.inexpr,
                   ty = tyTm ast}
  | TmConDef t ->
    TmConDef {t with inexpr = mergeWithUtestHeaderH env ast t.inexpr,
                     ty = tyTm ast}
  | TmUtest t ->
    TmUtest {t with next = mergeWithUtestHeaderH env ast t.next, ty = tyTm ast}
  | TmExt t ->
    TmExt {t with inexpr = mergeWithUtestHeaderH env ast t.inexpr,
                  ty = tyTm ast}
  | _ -> ast

  sem stripUtests : Expr -> Expr
  sem stripUtests =
  | TmUtest t -> stripUtests t.next
  | t -> smap_Expr_Expr stripUtests t

  sem generateUtest : Bool -> Expr -> Expr
  sem generateUtest testsEnabled =
  | ast ->
    if testsEnabled then
      match replaceUtests (utestEnvEmpty ()) ast with (env, ast) in
      let ast = insertUtestTail ast in
      let ast = mergeWithUtestHeader env ast in
      eliminateDuplicateCode ast
    else stripUtests ast
end

lang TestLang =
  MExprUtestGenerate + MExprEval + MExprEq + MExprTypeCheck + MExprPrettyPrint
end

mexpr

use TestLang in

let emptyEnv = utestEnvEmpty () in

let eval = lam env. lam e.
  let e = mergeWithUtestHeader env e in
  eval (evalCtxEmpty ()) e
in

let evalEquality : UtestEnv -> Type -> Expr -> Expr -> Expr =
  lam env. lam ty. lam l. lam r.
  match getEqualityExpr (NoInfo ()) env ty with (env, expr) in
  match generateEqualityBindings (NoInfo ()) env ty (None ()) with (env, binds) in
  eval env (bind_ binds (appf2_ expr l r))
in

let evalPrettyPrint : UtestEnv -> Type -> Expr -> Expr =
  lam env. lam ty. lam t.
  match getPrettyPrintExpr (NoInfo ()) env ty with (env, expr) in
  match generatePrettyPrintBindings (NoInfo ()) env [ty] with (env, binds) in
  eval env (bind_ binds (app_ expr t))
in

let i1 = const_ tyint_ (CInt {val = 1}) in
let i2 = const_ tyint_ (CInt {val = 2}) in
utest evalPrettyPrint emptyEnv tyint_ i1 with str_ "1" using eqExpr in
utest evalPrettyPrint emptyEnv tyint_ i2 with str_ "2" using eqExpr in
utest evalEquality emptyEnv tyint_ i1 i2 with false_ using eqExpr in
utest evalEquality emptyEnv tyint_ i2 i2 with true_ using eqExpr in

let c1 = const_ tychar_ (CChar {val = 'a'}) in
let c2 = const_ tychar_ (CChar {val = 'b'}) in
utest evalPrettyPrint emptyEnv tychar_ c1 with str_ "'a'" using eqExpr in
utest evalPrettyPrint emptyEnv tychar_ c2 with str_ "'b'" using eqExpr in
utest evalEquality emptyEnv tychar_ c1 c2 with false_ using eqExpr in
utest evalEquality emptyEnv tychar_ c1 c1 with true_ using eqExpr in

let bt = const_ tybool_ (CBool {val = true}) in
let bf = const_ tybool_ (CBool {val = false}) in
utest evalPrettyPrint emptyEnv tybool_ bt with str_ "true" using eqExpr in
utest evalPrettyPrint emptyEnv tybool_ bf with str_ "false" using eqExpr in
utest evalEquality emptyEnv tybool_ bt bf with false_ using eqExpr in
utest evalEquality emptyEnv tybool_ bf bf with true_ using eqExpr in

let f1 = const_ tyfloat_ (CFloat {val = 2.5}) in
let f2 = const_ tyfloat_ (CFloat {val = 2.6}) in
utest evalPrettyPrint emptyEnv tyfloat_ f1 with str_ "2.5" using eqExpr in
utest evalPrettyPrint emptyEnv tyfloat_ f2 with str_ "2.6" using eqExpr in
utest evalEquality emptyEnv tyfloat_ f1 f2 with false_ using eqExpr in
utest evalEquality emptyEnv tyfloat_ f1 f1 with true_ using eqExpr in

let ty = tyseq_ tyint_ in
let s1 = TmSeq {tms = [i1, i2], ty = ty, info = NoInfo ()} in
let s2 = TmSeq {tms = [i1, i2, i1], ty = ty, info = NoInfo ()} in
let s3 = TmSeq {tms = [], ty = ty, info = NoInfo ()} in
utest evalPrettyPrint emptyEnv ty s1 with str_ "[1,2]" using eqExpr in
utest evalPrettyPrint emptyEnv ty s2 with str_ "[1,2,1]" using eqExpr in
utest evalPrettyPrint emptyEnv ty s3 with str_ "[]" using eqExpr in
utest evalEquality emptyEnv ty s3 s3 with true_ using eqExpr in
utest evalEquality emptyEnv ty s1 s2 with false_ using eqExpr in
utest evalEquality emptyEnv ty s2 s1 with false_ using eqExpr in
utest evalEquality emptyEnv ty s1 s1 with true_ using eqExpr in

let t1 = tensorCreate_ tyint_ (TmSeq {tms = [i1], ty = ty, info = NoInfo ()})
  (lam_ "" (tyseq_ tyint_) i1) in
let t2 = tensorCreate_ tyint_ (TmSeq {tms = [i2], ty = ty, info = NoInfo ()})
  (lam_ "" (tyseq_ tyint_) i1) in
let ty = tytensor_ tyint_ in
utest evalPrettyPrint emptyEnv ty t1 with str_ "[1]" using eqExpr in
utest evalPrettyPrint emptyEnv ty t2 with str_ "[1, 1]" using eqExpr in
utest evalEquality emptyEnv ty t1 t1 with true_ using eqExpr in
utest evalEquality emptyEnv ty t1 t2 with false_ using eqExpr in
utest evalEquality emptyEnv ty t2 t1 with false_ using eqExpr in
utest evalEquality emptyEnv ty t2 t2 with true_ using eqExpr in

let ty = tytuple_ [tyint_, tyfloat_, tybool_, tychar_] in
let r1 = tuple_ ty [i1, f1, bf, c1] in
let r2 = tuple_ ty [i1, f1, bt, c1] in
utest evalPrettyPrint emptyEnv ty r1 with str_ "(1, 2.5, false, 'a')" using eqExpr in
utest evalPrettyPrint emptyEnv ty r2 with str_ "(1, 2.5, true, 'a')" using eqExpr in
utest evalEquality emptyEnv ty r1 r1 with true_ using eqExpr in
utest evalEquality emptyEnv ty r1 r2 with false_ using eqExpr in
utest evalEquality emptyEnv ty r2 r1 with false_ using eqExpr in
utest evalEquality emptyEnv ty r2 r2 with true_ using eqExpr in

let ty = tytuple_ [] in
let r = tuple_ ty [] in
utest evalPrettyPrint emptyEnv ty r with str_ "{}" using eqExpr in
utest evalEquality emptyEnv ty r r with true_ using eqExpr in

let r1 = urecord_ [("a", i1), ("b", f1), ("c", bf), ("d", c1)] in
let r2 = urecord_ [("a", i1), ("b", f1), ("c", bf), ("d", c2)] in
let ty = tyrecord_ [("a", tyint_), ("b", tyfloat_), ("c", tybool_), ("d", tychar_)] in
utest evalPrettyPrint emptyEnv ty r1 with str_ "{a = 1, b = 2.5, c = false, d = 'a'}"
using eqExpr in
utest evalPrettyPrint emptyEnv ty r2 with str_ "{a = 1, b = 2.5, c = false, d = 'b'}"
using eqExpr in
utest evalEquality emptyEnv ty r1 r1 with true_ using eqExpr in
utest evalEquality emptyEnv ty r1 r2 with false_ using eqExpr in
utest evalEquality emptyEnv ty r2 r1 with false_ using eqExpr in
utest evalEquality emptyEnv ty r2 r2 with true_ using eqExpr in

let treeId = nameSym "Tree" in
let leafId = nameSym "Leaf" in
let emptyLeafId = nameSym "EmptyLeaf" in
let branchId = nameSym "Branch" in
let treeTy = tyapp_ (ntycon_ treeId) (tyvar_ "a") in
let constrs = mapFromSeq nameCmp
  [ (leafId, tyall_ "a" (tyarrow_ (tyvar_ "a") treeTy))
  , (emptyLeafId, tyall_ "a" (tyarrow_ tyunit_ treeTy))
  , (branchId, tyall_ "a" (tyarrow_ (tytuple_ [treeTy, treeTy]) treeTy))
  ] in
let env = {emptyEnv with variants = mapFromSeq nameCmp [(treeId, constrs)]} in
let c1 = nconapp_ leafId i1 in
let c2 = nconapp_ leafId i2 in
let c3 = nconapp_ emptyLeafId unit_ in
let c4 = nconapp_ branchId (utuple_ [c1, c3]) in
let c5 = nconapp_ branchId (utuple_ [c3, c1]) in
let ty = tyapp_ (ntycon_ treeId) tyint_ in
utest evalPrettyPrint env ty c1 with str_ "Leaf 1" using eqExpr in
utest evalPrettyPrint env ty c2 with str_ "Leaf 2" using eqExpr in
utest evalPrettyPrint env ty c3 with str_ "EmptyLeaf {}" using eqExpr in
utest evalPrettyPrint env ty c4 with str_ "Branch (Leaf 1, EmptyLeaf {})" using eqExpr in
utest evalPrettyPrint env ty c5 with str_ "Branch (EmptyLeaf {}, Leaf 1)" using eqExpr in
utest evalEquality env ty c1 c1 with true_ using eqExpr in
utest evalEquality env ty c1 c2 with false_ using eqExpr in
utest evalEquality env ty c3 c3 with true_ using eqExpr in
utest evalEquality env ty c1 c3 with false_ using eqExpr in
utest evalEquality env ty c1 c4 with false_ using eqExpr in
utest evalEquality env ty c4 c5 with false_ using eqExpr in
utest evalEquality env ty c4 c4 with true_ using eqExpr in
utest evalEquality env ty c5 c5 with true_ using eqExpr in

let symTy = tycon_ "Symbol" in
let s = gensym_ unit_ in
utest evalEquality env symTy s s with false_ using eqExpr in
utest match expr2str (evalPrettyPrint env symTy s) with "\"sym (" ++ _ ++ ")\"" then true else false
with true in

let refTy = tyapp_ (tycon_ "Ref") tyint_ in
let r = ref_ (int_ 0) in
utest evalPrettyPrint env refTy r with str_ "<ref>" using eqExpr in

()