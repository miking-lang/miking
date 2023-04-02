include "peval/include.mc" 
include "peval/ast.mc"

include "mexpr/utils.mc"
include "mexpr/pprint.mc"
include "mexpr/extract.mc"
include "mexpr/ast.mc"

include "set.mc"


lang SpecializeUtils = SpecializeAst + SpecializeInclude + MExprPrettyPrint + MExprExtract + LamAst 

  type SpecializeNames = {
    pevalNames : [Name],
    consNames : [Name],
    builtinsNames : [Name],
    tyConsNames : [Name],
    otherFuncs : [Name]
  }

  type SpecializeArgs = {
    lib : Map Name Expr,
    -- For each binding in the reclet, store the name of the other bindings
    -- and the binding itself
    rlMapping: Map Name ([Name], RecLetBinding),
    idMapping : Map Name Name,
    closing : Bool
  }
  sem initArgs : () -> SpecializeArgs
  sem initArgs = | _ -> {lib = (mapEmpty nameCmp), 
                   rlMapping = (mapEmpty nameCmp),
                   closing=false, idMapping= (mapEmpty nameCmp)}

  sem updateLib : SpecializeArgs -> Map Name Expr -> SpecializeArgs
  sem updateLib args = | lib -> {args with lib = lib}

  sem updateRlMapping : SpecializeArgs -> Map Name ([Name], RecLetBinding)
                        -> SpecializeArgs
  sem updateRlMapping args = | lib -> {args with rlMapping = lib}

  sem updateIds : SpecializeArgs -> Map Name Name -> SpecializeArgs
  sem updateIds args = | idm -> {args with idMapping =idm}

  sem updateClosing : SpecializeArgs -> Bool -> SpecializeArgs
  sem updateClosing args = | b -> {args with closing = b}

  sem isClosing : SpecializeArgs -> Bool
  sem isClosing = | args -> args.closing

  sem findNames : Expr -> [String] -> [Name]
  sem findNames ast = | includes ->
  let names = filterOption (findNamesOfStrings includes ast) in
  if eqi (length includes) (length names) then
      names
  else 
    error "A necessary include could not be found in the AST"

  sem createNames : Expr -> [Name] -> SpecializeNames
  sem createNames ast =
  | pevalNames ->
  let consNames = findNames ast includeConsNames in
  let builtinsNames = findNames ast includeBuiltins in
  let tyConsNames = findNames ast includeTyConsNames in
  let otherFuncs = findNames ast otherFuncs in
  {pevalNames = pevalNames, consNames = consNames,
   builtinsNames = builtinsNames, tyConsNames = tyConsNames,
   otherFuncs=otherFuncs}

  sem getName : [Name] -> String -> Option Name
  sem getName names =
  | str -> find (lam x. eqString str x.0) names

  sem pevalName : SpecializeNames -> Name
  sem pevalName = | names -> match getName (names.pevalNames) "pevalWithEnv" with Some t then t
                             else error "semantic function peval not found"

  sem tmClosName : SpecializeNames -> Name
  sem tmClosName = | names -> match getName (names.consNames) "ClosAst_TmClos"
                              with Some t then t else error "TmClos not found"

  sem tmAppName : SpecializeNames -> Name
  sem tmAppName = | names -> match getName (names.consNames) "AppAst_TmApp" with Some t then t
                             else error "TmApp not found"

  sem tmLamName : SpecializeNames -> Name
  sem tmLamName = | names -> match getName (names.consNames) "LamAst_TmLam" with Some t then t
                             else error "TmLam not found"

  sem tmVarName : SpecializeNames -> Name
  sem tmVarName = | names -> match getName (names.consNames) "VarAst_TmVar" with Some t then t
                             else error "TmVar not found"

  sem tmRecName : SpecializeNames -> Name
  sem tmRecName = | names -> match getName (names.consNames) "RecordAst_TmRecord" with
                             Some t then t else error "TmRecord not found"

  sem tmSeqName : SpecializeNames -> Name
  sem tmSeqName = | names -> match getName (names.consNames) "SeqAst_TmSeq" with
                             Some t then t else error "TmSeq not found"

  sem tmConstName : SpecializeNames -> Name
  sem tmConstName = | names -> match getName (names.consNames) "ConstAst_TmConst" with
                             Some t then t else error "TmConst not found"

  sem tmMatchName : SpecializeNames -> Name
  sem tmMatchName = | names -> match getName (names.consNames) "MatchAst_TmMatch" with
                             Some t then t else error "TmMatch not found"

  sem tmLetName : SpecializeNames -> Name
  sem tmLetName = | names -> match getName (names.consNames) "LetAst_TmLet" with
                             Some t then t else error "TmLet not found"

  sem listConsName : SpecializeNames -> Name
  sem listConsName = | names -> match getName (names.consNames) "Cons" with
                             Some t then t else error "List Cons not found"

  sem listNilName : SpecializeNames -> Name
  sem listNilName = | names -> match getName (names.consNames) "Nil" with
                             Some t then t else error "List Nil not found"

  sem infoName : SpecializeNames -> Name
  sem infoName = | names -> match getName (names.consNames) "Info" with
                             Some t then t else error "Info constructor not found"

  sem noInfoName : SpecializeNames -> Name
  sem noInfoName = | names -> match getName (names.consNames) "NoInfo" with
                             Some t then t else error "NoInfo constructor not found"

  sem tyAppName : SpecializeNames -> Name
  sem tyAppName = | names -> match getName (names.tyConsNames) "AppTypeAst_TyApp" with
                             Some t then t else error "TyApp not found"

  sem tyVarName : SpecializeNames -> Name
  sem tyVarName = | names -> match getName (names.tyConsNames) "VarTypeAst_TyVar" with
                             Some t then t else error "TyVar not found"

  sem tyIntName : SpecializeNames -> Name
  sem tyIntName = | names -> match getName (names.tyConsNames) "IntTypeAst_TyInt" with
                             Some t then t else error "TyInt not found"
  sem tyBoolName : SpecializeNames -> Name
  sem tyBoolName = | names -> match getName (names.tyConsNames) "BoolTypeAst_TyBool" with
                             Some t then t else error "TyBool not found"

  sem tyFloatName : SpecializeNames -> Name
  sem tyFloatName = | names -> match getName (names.tyConsNames) "FloatTypeAst_TyFloat" with
                             Some t then t else error "TyFloat not found"

  sem tyCharName : SpecializeNames -> Name
  sem tyCharName = | names -> match getName (names.tyConsNames) "CharTypeAst_TyChar" with
                             Some t then t else error "TyChar not found"

  sem tyUnknownName : SpecializeNames -> Name
  sem tyUnknownName = | names -> match getName (names.tyConsNames) "UnknownTypeAst_TyUnknown"
                                 with Some t then t else error "TyUnknown not found"

  sem tyArrowName : SpecializeNames -> Name
  sem tyArrowName = | names -> match getName (names.tyConsNames) "FunTypeAst_TyArrow"
                               with Some t then t else error "TyArrow not found"


  sem mapFromSeqName : SpecializeNames -> Name
  sem mapFromSeqName = | names -> match getName (names.otherFuncs) "mapFromSeq"
                                  with Some t then t else error "MapFromSeq not found"

  sem mapToSeqName : SpecializeNames -> Name
  sem mapToSeqName = | names -> match getName (names.otherFuncs) "mapToSeq"
                                with Some t then t else error "mapToSeq not found"

  sem noSymbolName : SpecializeNames -> Name
  sem noSymbolName = | names -> match getName (names.consNames) "_noSymbol"
                                with Some t then t else error "_noSymbol not found"

  sem stringToSidName : SpecializeNames -> Name
  sem stringToSidName = | names -> match getName (names.otherFuncs) "stringToSid"
                          with Some t then t else error "stringToSid not found"

  sem mexprStringName : SpecializeNames -> Name
  sem mexprStringName = | names -> match getName (names.otherFuncs) "toString" 
                          with Some t then t else error "mexprToString not found"

  sem patIntName : SpecializeNames -> Name
  sem patIntName = | names -> match getName (names.consNames) "IntPat_PatInt" 
                          with Some t then t else error "IntPat not found"

  sem patNamedName : SpecializeNames -> Name
  sem patNamedName = | names -> match getName (names.consNames) "NamedPat_PatNamed"
                          with Some t then t else error "PatNamed not found"

  sem pNameName: SpecializeNames -> Name
  sem pNameName = | names -> match getName (names.consNames) "PName"
                          with Some t then t else error "PName not found"

  sem pWildcardName: SpecializeNames -> Name
  sem pWildcardName = | names -> match getName (names.consNames) "PWildcard"
                          with Some t then t else error "PWildcard not found"

  -- Return a string representation of the constant along with whether
  -- it takes an argument when constructed
  sem getConstString : Const -> String
  sem getConstString =
  | CInt _ -> "int"
  | CFloat _ -> "float"
  | CBool _ -> "bool"
  | CChar _ -> "char"
  | CSymb _ -> "symb"
  | t -> getConstStringCode 0 t

  sem getBuiltinName : String -> SpecializeNames -> Name
  sem getBuiltinName str = | names ->
    match find (lam x. eqString str x.0) builtinsMapping with Some astStr then
        match getName (names.builtinsNames) astStr.1 with Some t in
        t
    else error "Could not find a builtin name"

  sem getBuiltinNameFromConst : Const -> SpecializeNames -> Name
  sem getBuiltinNameFromConst val = | names ->
    let str = getConstString val in
    getBuiltinName str names
end
