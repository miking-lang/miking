-- The bulk of this file contains helper functions for handling names, incl.
-- 1. Finding the names of the strings (defined in include.mc) in the AST
-- 2. Getting a certain name from a given string
-- Moreover, the different arguments types that are used by the lifting, and
-- in the transformation are defined here.

include "peval/include.mc"
include "peval/ast.mc"
include "mexpr/utils.mc"
include "mexpr/ast.mc"

include "set.mc"

lang SpecializeUtils = SpecializeAst + SpecializeInclude + MExprFindSym

  -- Holds the names of constructors/functions/types that could be needed
  -- in peval transformation.
  type SpecializeNames = {
    pevalNames : Map String Name,
    consNames : Map String Name,
    builtinsNames : Map String Name,
    tyConsNames : Map String Name,
    otherFuncs : Map String Name
  }

  type SpecializeArgs = {
    idMapping : Map Name Name,
    extractMap : Map Name Expr
  }

  sem initArgs : Map Name Expr -> SpecializeArgs
  sem initArgs = | emap ->
    {extractMap = emap,
     idMapping = (mapEmpty nameCmp)}

  sem updateIds : SpecializeArgs -> Map Name Name -> SpecializeArgs
  sem updateIds args = | idm -> {args with idMapping =idm}

  sem _nameSeqToMap : [Name] -> Map String Name
  sem _nameSeqToMap =
  | names -> mapFromSeq cmpString (map (lam name. (name.0, name)) names)

  sem findNames : Expr -> [String] -> Map String Name
  sem findNames ast = | includes ->
    let names = filterOption (findNamesOfStrings includes ast) in
    let nameMap = _nameSeqToMap names in
    if eqi (length includes) (length names) then
      nameMap
    else
      let notIn = filter (lam str. not (mapMem str nameMap)) includes in
      let notIn = strJoin "\n" notIn in
      error (concat "A necessary include could not be found in the AST\n" notIn)

  sem createNames : Expr -> SpecializeNames
  sem createNames =
  | ast ->
    let pevalNames = findNames ast includeSpecializeNames in
    let consNames = findNames ast includeConsNames in
    let builtinsNames = findNames ast includeBuiltins in
    let tyConsNames = findNames ast includeTyConsNames in
    let otherFuncs = findNames ast includeOtherFuncs in
    {pevalNames = pevalNames,
     consNames = consNames,
     builtinsNames = builtinsNames,
     tyConsNames = tyConsNames,
     otherFuncs=otherFuncs}

  sem getName : Map String Name -> String -> Name
  sem getName names =
  | str ->
    match mapLookup str names with Some n then n
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

  sem tmRecLetsName : SpecializeNames -> Name
  sem tmRecLetsName = | names -> getName (names.consNames) "RecLetsAst_TmRecLets"

  sem tmConDefName : SpecializeNames -> Name
  sem tmConDefName = | names -> getName (names.consNames) "DataAst_TmConDef"

  sem tmConAppName : SpecializeNames -> Name
  sem tmConAppName = | names -> getName (names.consNames) "DataAst_TmConApp"

  sem tmTypeName : SpecializeNames -> Name
  sem tmTypeName = | names -> getName (names.consNames) "TypeAst_TmType"

  sem tmNeverName : SpecializeNames -> Name
  sem tmNeverName = | names -> getName (names.consNames) "NeverAst_TmNever"

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
  sem noSymbolName = | names -> getName (names.otherFuncs) "_noSymbol"

  sem stringToSidName : SpecializeNames -> Name
  sem stringToSidName = | names -> getName (names.otherFuncs) "stringToSid"

  sem mexprStringName : SpecializeNames -> Name
  sem mexprStringName = | names -> getName (names.otherFuncs) "toString"

  sem patIntName : SpecializeNames -> Name
  sem patIntName = | names -> getName (names.consNames) "IntPat_PatInt"

  sem patBoolName : SpecializeNames -> Name
  sem patBoolName = | names -> getName (names.consNames) "BoolPat_PatBool"

  sem patCharName : SpecializeNames -> Name
  sem patCharName = | names -> getName (names.consNames) "CharPat_PatChar"

  sem patSeqTotName : SpecializeNames -> Name
  sem patSeqTotName = | names -> getName (names.consNames) "SeqTotPat_PatSeqTot"

  sem patSeqEdgeName : SpecializeNames -> Name
  sem patSeqEdgeName = | names -> getName (names.consNames) "SeqEdgePat_PatSeqEdge"

  sem patRecName : SpecializeNames -> Name
  sem patRecName = | names -> getName (names.consNames) "RecordPat_PatRecord"

  sem patConName : SpecializeNames -> Name
  sem patConName = | names -> getName (names.consNames) "DataPat_PatCon"

  sem patAndName : SpecializeNames -> Name
  sem patAndName = | names -> getName (names.consNames) "AndPat_PatAnd"

  sem patOrName : SpecializeNames -> Name
  sem patOrName = | names -> getName (names.consNames) "OrPat_PatOr"

  sem patNotName : SpecializeNames -> Name
  sem patNotName = | names -> getName (names.consNames) "NotPat_PatNot"

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
