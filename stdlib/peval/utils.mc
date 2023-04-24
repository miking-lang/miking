include "peval/include.mc" 
include "peval/ast.mc"

include "mexpr/utils.mc"
include "mexpr/pprint.mc"
include "mexpr/extract.mc"
include "mexpr/ast.mc"

include "set.mc"


lang SpecializeUtils = SpecializeAst + SpecializeInclude + MExprPrettyPrint + MExprExtract + LamAst 

  type SpecializeNames = {
    pevalNames : Map String Name,
    consNames : Map String Name,
    builtinsNames : Map String Name,
    tyConsNames : Map String Name,
    otherFuncs : Map String Name
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

  sem _nameSeqToMap : [Name] -> Map String Name
  sem _nameSeqToMap = | names ->
  mapFromSeq cmpString (map (lam name. (name.0, name)) names)

  sem findNames : Expr -> [String] -> Map String Name 
  sem findNames ast = | includes ->
  let names = filterOption (findNamesOfStrings includes ast) in
  if eqi (length includes) (length names) then
    _nameSeqToMap names 
  else 
    error "A necessary include could not be found in the AST"

  sem createNames : Expr -> [Name] -> SpecializeNames
  sem createNames ast =
  | pevalNames ->
  let pevalNames = _nameSeqToMap pevalNames in
  let consNames = findNames ast includeConsNames in
  let builtinsNames = findNames ast includeBuiltins in
  let tyConsNames = findNames ast includeTyConsNames in
  let otherFuncs = findNames ast otherFuncs in
  {pevalNames = pevalNames, 
   consNames = consNames,
   builtinsNames = builtinsNames, 
   tyConsNames = tyConsNames,
   otherFuncs=otherFuncs}

  sem getName : Map String Name -> String -> Name
  sem getName names =
  | str -> match mapLookup str names with Some n then n
           else error (concat "Could not find: " str) 

  sem pevalName : SpecializeNames -> Name
  sem pevalName = | names -> getName (names.pevalNames) "pevalWithEnv"

  sem tmClosName : SpecializeNames -> Name
  sem tmClosName = | names -> getName (names.consNames) "ClosAst_TmClos"

  sem tmAppName : SpecializeNames -> Name
  sem tmAppName = | names -> getName (names.consNames) "AppAst_TmApp"

  sem tmLamName : SpecializeNames -> Name
  sem tmLamName = | names -> getName (names.consNames) "LamAst_TmLam"

  sem tmVarName : SpecializeNames -> Name
  sem tmVarName = | names -> getName (names.consNames) "VarAst_TmVar"

  sem tmRecName : SpecializeNames -> Name
  sem tmRecName = | names -> getName (names.consNames) "RecordAst_TmRecord"

  sem tmSeqName : SpecializeNames -> Name
  sem tmSeqName = | names -> getName (names.consNames) "SeqAst_TmSeq"

  sem tmConstName : SpecializeNames -> Name
  sem tmConstName = | names -> getName (names.consNames) "ConstAst_TmConst"

  sem tmMatchName : SpecializeNames -> Name
  sem tmMatchName = | names -> getName (names.consNames) "MatchAst_TmMatch"

  sem tmLetName : SpecializeNames -> Name
  sem tmLetName = | names -> getName (names.consNames) "LetAst_TmLet"

  sem listConsName : SpecializeNames -> Name
  sem listConsName = | names -> getName (names.consNames) "Cons"

  sem listNilName : SpecializeNames -> Name
  sem listNilName = | names -> getName (names.consNames) "Nil"

  sem infoName : SpecializeNames -> Name
  sem infoName = | names -> getName (names.consNames) "Info"

  sem noInfoName : SpecializeNames -> Name
  sem noInfoName = | names -> getName (names.consNames) "NoInfo"

  sem tyAppName : SpecializeNames -> Name
  sem tyAppName = | names -> getName (names.tyConsNames) "AppTypeAst_TyApp"

  sem tyVarName : SpecializeNames -> Name
  sem tyVarName = | names -> getName (names.tyConsNames) "VarTypeAst_TyVar"

  sem tyIntName : SpecializeNames -> Name
  sem tyIntName = | names -> getName (names.tyConsNames) "IntTypeAst_TyInt"

  sem tyBoolName : SpecializeNames -> Name
  sem tyBoolName = | names -> getName (names.tyConsNames) "BoolTypeAst_TyBool"

  sem tyFloatName : SpecializeNames -> Name
  sem tyFloatName = | names -> getName (names.tyConsNames) "FloatTypeAst_TyFloat"

  sem tyCharName : SpecializeNames -> Name
  sem tyCharName = | names -> getName (names.tyConsNames) "CharTypeAst_TyChar"

  sem tyUnknownName : SpecializeNames -> Name
  sem tyUnknownName = | names -> getName (names.tyConsNames) "UnknownTypeAst_TyUnknown"

  sem tyArrowName : SpecializeNames -> Name
  sem tyArrowName = | names -> getName (names.tyConsNames) "FunTypeAst_TyArrow"

  sem mapFromSeqName : SpecializeNames -> Name
  sem mapFromSeqName = | names -> getName (names.otherFuncs) "mapFromSeq"

  sem mapToSeqName : SpecializeNames -> Name
  sem mapToSeqName = | names -> getName (names.otherFuncs) "mapToSeq"

  sem noSymbolName : SpecializeNames -> Name
  sem noSymbolName = | names -> getName (names.consNames) "_noSymbol"

  sem stringToSidName : SpecializeNames -> Name
  sem stringToSidName = | names -> getName (names.otherFuncs) "stringToSid"

  sem mexprStringName : SpecializeNames -> Name
  sem mexprStringName = | names -> getName (names.otherFuncs) "toString" 

  sem patIntName : SpecializeNames -> Name
  sem patIntName = | names -> getName (names.consNames) "IntPat_PatInt" 

  sem patNamedName : SpecializeNames -> Name
  sem patNamedName = | names -> getName (names.consNames) "NamedPat_PatNamed"

  sem pNameName: SpecializeNames -> Name
  sem pNameName = | names -> getName (names.consNames) "PName"

  sem pWildcardName: SpecializeNames -> Name
  sem pWildcardName = | names -> getName (names.consNames) "PWildcard"

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
  match mapLookup str builtinsMapping with Some astStr then
    getName (names.builtinsNames) astStr
  else error (join ["Could not find ", str, " in builtin-mapping"])

  sem getBuiltinNameFromConst : Const -> SpecializeNames -> Name
  sem getBuiltinNameFromConst val = | names ->
    let str = getConstString val in
    getBuiltinName str names
end
