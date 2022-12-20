include "bool.mc"
include "string.mc"
include "name.mc"

include "ast.mc"
include "ast-builder.mc"
include "boot-parser.mc"
include "builtin.mc"
include "eq.mc"
include "type-annot.mc"
include "type-lift.mc"
include "type-check.mc"

include "common.mc"

type UtestTypeEnv = {
  -- Maps every type to the names of its pretty-print and equality functions,
  -- respectively.
  typeFunctions : Map Type (Name, Name),

  -- Maps every variant type name to a map mapping its constructor names to
  -- their argument types.
  variants : Map Name (Map Name Type),

  -- Maps every alias name to the type it is an alias for.
  aliases : Map Name Type
}

let _utestRunnerStr = "
let numFailed = ref 0 in

let join = lam seqs.
  foldl concat [] seqs
in

let printLn = lam s.
  print (concat s \"\\n\")
in

let int2string = lam n.
  recursive
  let int2string_rechelper = lam n.
    if lti n 10
    then [int2char (addi n (char2int '0'))]
    else
      let d = [int2char (addi (modi n 10) (char2int '0'))] in
      concat (int2string_rechelper (divi n 10)) d
  in
  if lti n 0
  then cons '-' (int2string_rechelper (negi n))
  else int2string_rechelper n
in

recursive
  let strJoin = lam delim. lam strs.
    if eqi (length strs) 0
    then \"\"
    else if eqi (length strs) 1
         then head strs
         else concat (concat (head strs) delim) (strJoin delim (tail strs))
in

let eqSeq = lam eq : (Unknown -> Unknown -> Bool).
  recursive let work = lam as. lam bs.
    let pair = (as, bs) in
    match pair with ([], []) then true else
    match pair with ([a] ++ as, [b] ++ bs) then
      if eq a b then work as bs else false
    else false
  in work
in

recursive
  let forAll = lam p. lam seq.
    if null seq
    then true
    else if p (head seq) then forAll p (tail seq)
    else false
in

let utestTestPassed = lam.
  print \".\"
in

let utestTestFailed =
  lam info   : String.
  lam lhsStr : String.
  lam rhsStr : String.
  lam usingStr : String.
  modref numFailed (addi (deref numFailed) 1);
  printLn (join [
    \"\n ** Unit test FAILED: \", info, \"**\", \"\n    LHS: \", lhsStr,
    \"\n    RHS: \", rhsStr, usingStr])
in

let utestRunner =
  lam info     : String.
  lam usingStr : String.
  lam lpprint  : Unknown -> String.
  lam rpprint  : Unknown -> String.
  lam eqfunc   : Unknown -> Unknown -> Bool.
  lam lhs      : Unknown.
  lam rhs      : Unknown.
  -- Comparison
  if eqfunc lhs rhs then
    utestTestPassed ()
  else
    utestTestFailed info (lpprint lhs) (rpprint rhs) usingStr
in

()
"

let _utestRunnerCode = ref (None())

-- Makes sure that the code is only parsed once and that it is
-- not parsed if it is not used.
let utestRunner = lam.
  match deref _utestRunnerCode with Some t then t
  else
    use BootParser in
    use MExprTypeCheck in
    let code = typeCheck (parseMExprStringKeywords [] _utestRunnerStr) in
    modref _utestRunnerCode (Some code);
    code


-- Get the name of a string identifier in an expression
let findName : String -> Expr -> Option Name = use MExprAst in
  lam str. lam expr.
    recursive let findNameH = lam acc. lam expr.
      match acc with Some n then Some n
      else match expr with TmLet {ident = ident, body = body, inexpr = inexpr} then
        if eqString (nameGetStr ident) str then Some ident
        else match findNameH (None ()) body with Some n then Some n
        else match findNameH (None ()) inexpr with Some n then Some n
        else None ()
      else match expr with TmRecLets {bindings = bindings, inexpr = inexpr} then
        match
          foldl (lam a. lam b : RecLetBinding.
            match a with Some _ then a
            else if eqString (nameGetStr b.ident) str then Some b.ident
            else match findNameH (None ()) b.body with Some n then Some n
            else None ()) (None ()) bindings
        with Some n then Some n
        else match findNameH (None ()) inexpr with Some n then Some n
        else None ()
      else match expr with TmExt {ident = ident, inexpr = inexpr} then
        if eqString (nameGetStr ident) str then Some ident
        else match findNameH (None ()) inexpr with Some n then Some n
        else None ()
      else sfold_Expr_Expr findNameH (None ()) expr
    in
    findNameH (None ()) expr

let _expr =
  use BootParser in
  parseMExprStringKeywords [] "let foo = lam. 42 in ()"
utest
  match findName "foo" _expr
  with Some n
  then eqString (nameGetStr n) "foo"
  else false
with true

let _expr =
  use BootParser in
  parseMExprStringKeywords [] "recursive let foo = lam. 42 in ()"
utest
  match findName "foo" _expr
  with Some n
  then eqString (nameGetStr n) "foo"
  else false
with true

let _expr =
  use BootParser in
  parseMExprStringKeywords [] "external foo : () in ()"
utest
  match findName "foo" _expr
  with Some n
  then eqString (nameGetStr n) "foo"
  else false
with true

let utestRunnerName = lam. optionGetOrElse
  (lam. error "Expected utestRunner to be defined")
  (findName "utestRunner" (utestRunner ()))

let numFailedName = lam. optionGetOrElse
  (lam. error "Expected utestNumFailed to be defined")
  (findName "numFailed" (utestRunner ()))

let getUniquePprintAndEqualityNames = lam.
  (nameSym "pp", nameSym "eq")

let collectKnownProgramTypes = use MExprAst in
  lam expr.
  recursive let unwrapTypeVarIdent = lam ty.
    match ty with TyCon {ident = ident} then Some ident
    else match ty with TyApp t then unwrapTypeVarIdent t.lhs
    else None ()
  in
  recursive let collectType = lam acc : UtestTypeEnv. lam ty.
    if mapMem ty acc.typeFunctions then
      acc
    else
      let funcNames = getUniquePprintAndEqualityNames () in
      match ty with TySeq {ty = elemTy} then
        let typeFuns = mapInsert ty funcNames acc.typeFunctions in
        let acc = {acc with typeFunctions = typeFuns} in
        collectType acc elemTy
      else match ty with TyTensor {ty = elemTy} then
        let typeFuns = mapInsert ty funcNames acc.typeFunctions in
        let acc = {acc with typeFunctions = typeFuns} in
        collectType acc elemTy
      else match ty with TyRecord {fields = fields} then
        let typeFuns = mapInsert ty funcNames acc.typeFunctions in
        let acc = {acc with typeFunctions = typeFuns} in
        mapFoldWithKey (lam acc. lam. lam fieldTy. collectType acc fieldTy)
                       acc fields
      else match unwrapTypeVarIdent ty with Some ident then
        let acc =
          match mapLookup ident acc.aliases with Some ty then
            collectType acc ty
          else acc
        in
        {acc with typeFunctions = mapInsert ty funcNames acc.typeFunctions}
      else
        {acc with typeFunctions = mapInsert ty funcNames acc.typeFunctions}
  in
  let expectedArrowType = use MExprPrettyPrint in
    lam info. lam tyIdent.
    let tyIdentStr = (getTypeStringCode 0 pprintEnvEmpty tyIdent).1 in
    let msg = join [
      "Expected constructor of arrow type, got ", tyIdentStr
    ] in
    errorSingle [info] msg
  in
  recursive let collectTypes : UtestTypeEnv -> Expr -> UtestTypeEnv =
    lam acc : UtestTypeEnv. lam expr.
    match expr with TmType t then
      match t.tyIdent with TyUnknown _ | TyVariant _ then
        let variants = mapInsert t.ident (mapEmpty nameCmp) acc.variants in
        let acc = {acc with variants = variants} in
        sfold_Expr_Expr collectTypes acc expr
      else
        let aliases = mapInsert t.ident t.tyIdent acc.aliases in
        let acc = {acc with aliases = aliases} in
        sfold_Expr_Expr collectTypes acc expr
    else match expr with TmConDef t then
      match stripTyAll t.tyIdent with (_, TyArrow {from = argTy, to = to}) then
        match unwrapTypeVarIdent to with Some ident then
          let constructors =
            match mapLookup ident acc.variants with Some constructors then
              mapInsert t.ident argTy constructors
            else
              let msg = join [
                "Constructor definition refers to undefined type ",
                nameGetStr ident
              ] in
              errorSingle [infoTm expr] msg
          in
          let variants = mapInsert ident constructors acc.variants in
          let acc = collectType acc argTy in
          let acc = {acc with variants = variants} in
          sfold_Expr_Expr collectTypes acc expr
        else expectedArrowType (infoTm expr) t.tyIdent
      else expectedArrowType (infoTm expr) t.tyIdent
    else match expr with TmUtest t then
      let acc = collectType acc (tyTm t.test) in
      let acc = collectType acc (tyTm t.expected) in
      let acc =
        match t.tusing with Some t then
          match tyTm t with
            TyArrow {from = lhs, to = TyArrow {from = rhs, to = TyBool _}}
          then
            collectType (collectType acc lhs) rhs
          else
            let msg = join [
              "Arguments of equality function must be properly annotated"
            ] in
            errorSingle [infoTm t] msg
        else acc
      in
      let acc = collectTypes acc t.test in
      let acc = collectTypes acc t.expected in
      let acc = match t.tusing with Some t then collectTypes acc t else acc in
      collectTypes acc t.next
    else sfold_Expr_Expr collectTypes acc expr
  in
  let emptyUtestTypeEnv = {
    variants = mapEmpty nameCmp,      -- Map Name Type
    aliases = mapFromSeq nameCmp (    -- Map Name Type
      map (lam t : (String, [String]). (nameNoSym t.0, tyunknown_)) builtinTypes
    ),
    typeFunctions = use MExprCmp in mapEmpty cmpType -- Map Type (Name, Name)
  } in
  collectTypes emptyUtestTypeEnv expr

let _unwrapAlias = use MExprAst in
  lam aliases : Map Name Type. lam ty : Type.
  match ty with TyCon t then
    match mapLookup t.ident aliases with Some aliasedTy then
      aliasedTy
    else ty
  else ty

let getPprintFuncName = lam env : UtestTypeEnv. lam ty.
  let ty = _unwrapAlias env.aliases ty in
  match mapLookup ty env.typeFunctions with Some n then
    let n : (Name, Name) = n in
    n.0
  else dprintLn ty; error "Could not find pretty-print function definition for type"

let getEqualFuncName = lam env : UtestTypeEnv. lam ty.
  let ty = _unwrapAlias env.aliases ty in
  match mapLookup ty env.typeFunctions with Some n then
    let n : (Name, Name) = n in
    n.1
  else dprintLn ty; error "Could not find equality function definition for type"

let _pprintUnknown =
  ulam_ "a" (str_ "?")

let _pprintInt =
  lam_ "a" tyint_ (app_ (var_ "int2string") (var_ "a"))

let _equalInt =
  lam_ "a" tyint_ (lam_ "b" tyint_ (eqi_ (var_ "a") (var_ "b")))

let _pprintFloat =
  lam_ "a" tyfloat_ (float2string_ (var_ "a"))

let _equalFloat =
  lam_ "a" tyfloat_ (lam_ "b" tyfloat_ (eqf_ (var_ "a") (var_ "b")))

let _pprintBool =
  lam_ "a" tybool_ (if_ (var_ "a") (str_ "true") (str_ "false"))

let _equalBool =
  lam_ "a" tybool_ (lam_ "b" tybool_
    (or_ (and_ (var_ "a") (var_ "b"))
         (and_ (not_ (var_ "a")) (not_ (var_ "b")))))

let _pprintChar =
  lam_ "a" tychar_ (app_ (var_ "join")
                   (seq_ [str_ "\'", seq_ [var_ "a"], str_ "\'"]))

let _equalChar =
  lam_ "a" tychar_ (lam_ "b" tychar_ (eqc_ (var_ "a") (var_ "b")))

let _pprintStr =
  lam_ "a" tystr_ (app_ (var_ "join") (seq_ [str_ "\"", var_ "a", str_ "\""]))

let _pprintSeq = use MExprAst in
  lam ty. lam elemPprintFuncName.
  match ty with TySeq {ty = TyChar _} then
    _pprintStr
  else
    lam_ "a" ty (app_ (var_ "join") (seq_ [
        str_ "[",
        appf2_ (var_ "strJoin")
          (str_ ",")
          (map_ (nvar_ elemPprintFuncName) (var_ "a")),
        str_ "]"
      ]))

let _equalSeq = lam ty. lam elemEqualFuncName.
  lam_ "a" ty (lam_ "b" ty
    (appf3_ (var_ "eqSeq") (nvar_ elemEqualFuncName) (var_ "a") (var_ "b")))

let _equalTensor = lam ty. lam elemEqualFuncName.
  lam_ "a" ty (lam_ "b" ty
    (utensorEq_ (nvar_ elemEqualFuncName) (var_ "a") (var_ "b")))

let _pprintTensor = lam ty. lam elemPprintFuncName.
  lam_ "a" ty (utensor2string_ (nvar_ elemPprintFuncName) (var_ "a"))

let _pprintRecord = use MExprAst in
  lam env. lam ty. lam fields.
  if mapIsEmpty fields then lam_ "a" ty (str_ "()")
  else
    let recordBindings =
      mapMapWithKey (lam id. lam. pvar_ (sidToString id)) fields
    in
    let recordPattern =
      PatRecord
        { bindings = recordBindings
        , info = makeInfo (posVal "utest_pprint" 0 0) (posVal "utest_pprint" 0 0)
        , ty = TyRecord
          { info = makeInfo (posVal "utest_pprint" 0 0) (posVal "utest_pprint" 0 0)
          , fields = fields
          }
        }
    in
    let pprintSeq =
      match record2tuple fields with Some types then
        let tuplePprints = lam seq. lam id. lam fieldTy.
          let fieldPprintName = getPprintFuncName env fieldTy in
          let pprintApp = app_ (nvar_ fieldPprintName) (var_ (sidToString id)) in
          snoc seq pprintApp
        in
        let pprintFuncs = mapFoldWithKey tuplePprints [] fields in
        seq_ [
          str_ "(",
          appf2_ (var_ "strJoin") (str_ ",") (seq_ pprintFuncs),
          str_ ")"]
      else
        let fieldPprints = lam seq. lam id. lam fieldTy.
          let fieldPprintName = getPprintFuncName env fieldTy in
          let pprintApp = app_ (var_ "join") (seq_ [
            str_ (sidToString id),
            str_ " = ",
            app_ (nvar_ fieldPprintName) (var_ (sidToString id))]) in
          snoc seq pprintApp
        in
        let pprintFuncs = mapFoldWithKey fieldPprints [] fields in
        seq_ [
          str_ "{",
          appf2_ (var_ "strJoin") (str_ ",") (seq_ pprintFuncs),
          str_ "}"]
    in
    lam_ "a" ty
      (match_ (var_ "a")
        recordPattern
        (app_ (var_ "join") pprintSeq)
        never_)

let _equalRecord =
  lam env. lam ty. lam fields.
  use MExprAst in
  let recordBindings = lam prefix.
    mapMapWithKey (lam id. lam. pvar_ (join [prefix, sidToString id])) fields
  in
  let lhsPrefix = "lhs_" in
  let rhsPrefix = "rhs_" in
  let intSid = lam i. lam v. (stringToSid (int2string i), v) in
  let eqInfo = makeInfo (posVal "utest_eq" 0 0) (posVal "utest_eq" 0 0) in
  let eqPats = [
    PatRecord {bindings = recordBindings lhsPrefix, info = eqInfo, ty = ty},
    PatRecord {bindings = recordBindings rhsPrefix, info = eqInfo, ty = ty}] in
  let matchPatternTy = TyRecord {
    fields = mapFromSeq cmpSID (mapi intSid [ty, ty]), info = eqInfo} in
  let matchPattern = PatRecord {
    bindings = mapFromSeq cmpSID (mapi intSid eqPats),
    info = eqInfo, ty = matchPatternTy} in
  let fieldEquals = lam seq. lam id. lam fieldTy.
    let fieldEqName = getEqualFuncName env fieldTy in
    let lhs = var_ (join [lhsPrefix, sidToString id]) in
    let rhs = var_ (join [rhsPrefix, sidToString id]) in
    let equalApp = appf2_ (nvar_ fieldEqName) lhs rhs in
    cons equalApp seq
  in
  let equalFuncs = mapFoldWithKey fieldEquals [] fields in
  let allEqual =
    if mapIsEmpty fields then true_
    else appf2_ (var_ "forAll") (ulam_ "b" (var_ "b")) (seq_ equalFuncs)
  in
  lam_ "a" ty (lam_ "b" ty
    (match_ (utuple_ [var_ "a", var_ "b"])
      matchPattern
      allEqual
      never_))

let _pprintVariant = lam env. lam ty. lam constrs.
  let constrPprint = lam cont. lam constrId. lam argTy.
    let pprintFuncId = getPprintFuncName env argTy in
    let constructorPattern = pcon_ (nameGetStr constrId) (pvar_ "t") in
    match_ (var_ "a")
      constructorPattern
      (app_ (var_ "join") (seq_ [
        str_ (nameGetStr constrId),
        str_ " ",
        app_ (nvar_ pprintFuncId) (var_ "t")]))
      cont
  in
  let constructorMatches = mapFoldWithKey constrPprint never_ constrs in
  lam_ "a" ty constructorMatches

let _equalVariant = lam env. lam ty. lam constrs.
  use MExprAst in
  let constrEqual = lam cont. lam constrId. lam argTy.
    let equalFuncId = getEqualFuncName env argTy in
    let lhsId = nameSym "lhs" in
    let rhsId = nameSym "rhs" in
    let intSid = lam i. lam v. (stringToSid (int2string i), v) in
    let eqInfo = makeInfo (posVal "utest_eq" 0 0) (posVal "utest_eq" 0 0) in
    let pvar = lam id. PatNamed {ident = PName id, info = eqInfo, ty = argTy} in
    let eqPats = [
      PatCon {ident = constrId, subpat = pvar lhsId, info = eqInfo, ty = ty},
      PatCon {ident = constrId, subpat = pvar rhsId, info = eqInfo, ty = ty}] in
    let constructorPatternTy = TyRecord {
      fields = mapFromSeq cmpSID (mapi intSid [ty, ty]), info = eqInfo} in
    let constructorPattern = PatRecord {
      bindings = mapFromSeq cmpSID (mapi intSid eqPats),
      info = eqInfo, ty = constructorPatternTy} in
    match_ (utuple_ [var_ "a", var_ "b"])
      constructorPattern
      (appf2_ (nvar_ equalFuncId) (nvar_ lhsId) (nvar_ rhsId))
      cont
  in
  let constructorMatches = mapFoldWithKey constrEqual false_ constrs in
  lam_ "a" ty (lam_ "b" ty constructorMatches)

let _pprintAlias = lam env. lam ty. lam aliasedTypePprintName.
  lam_ "a" ty (app_ (nvar_ aliasedTypePprintName) (var_ "a"))

let _equalAlias = lam env. lam ty. lam aliasedTypeEqualName.
  lam_ "a" ty (lam_ "b" ty
    (appf2_ (nvar_ aliasedTypeEqualName) (var_ "a") (var_ "b")))

let typeHasDefaultEquality = use MExprAst in
  lam env : UtestTypeEnv. lam ty.
  recursive let work = lam visited. lam ty.
    match ty with TyInt _ | TyFloat _ | TyBool _ | TyChar _ then true
    else match ty with TySeq t | TyTensor t then
      work visited t.ty
    else match ty with TyRecord t then
      mapAll (lam ty. work visited ty) t.fields
    else match ty with TyCon t then
      -- If we have already visited a type variable, we stop here to avoid
      -- infinite recursion.
      if mapMem t.ident visited then true
      else
        let visited = mapInsert t.ident () visited in
        match mapLookup t.ident env.variants with Some constrs then
          mapAll (lam ty. work visited ty) constrs
        else match mapLookup t.ident env.aliases with Some ty then
          work visited ty
        else false
    else false
  in
  work (mapEmpty nameCmp) ty

let getTypeFunctions =
  use MExprAst in
  use MExprPrettyPrint in
  lam env : UtestTypeEnv. lam ty.
  let reportError = lam msg : String -> String.
    match getTypeStringCode 0 pprintEnvEmpty ty with (_, tyStr) then
      errorSingle [infoTy ty] (msg tyStr)
    else never
  in
  match ty with TyInt _ then
    (_pprintInt, Some _equalInt)
  else match ty with TyFloat _ then
    (_pprintFloat, Some _equalFloat)
  else match ty with TyBool _ then
    (_pprintBool, Some _equalBool)
  else match ty with TyChar _ then
    (_pprintChar, Some _equalChar)
  else match ty with TySeq {ty = elemTy} then
    let elemPprintName = getPprintFuncName env elemTy in
    let elemEqualName = getEqualFuncName env elemTy in
    (_pprintSeq ty elemPprintName, Some (_equalSeq ty elemEqualName))
  else match ty with TyTensor {ty = elemTy} then
    let elemPprintName = getPprintFuncName env elemTy in
    let elemEqualName = getEqualFuncName env elemTy in
    (_pprintTensor ty elemPprintName , Some (_equalTensor ty elemEqualName))
  else match ty with TyRecord {fields = fields} then
    ( _pprintRecord env ty fields
    , Some (_equalRecord env ty fields))
  else match ty with TyCon {ident = ident} then
    match mapLookup ident env.variants with Some constrs then
      let annotTy = ntycon_ ident in
      if forAll (lam ty. typeHasDefaultEquality env ty) (mapValues constrs) then
        ( _pprintVariant env annotTy constrs
        , Some (_equalVariant env annotTy constrs))
      else
        (_pprintVariant env annotTy constrs, None ())
    else match mapLookup ident env.aliases with Some ty then
      let aliasVar = ntycon_ ident in
      let aliasedTypePprintName = getPprintFuncName env ty in
      let aliasedTypeEqualName = getEqualFuncName env ty in
      ( _pprintAlias env aliasVar aliasedTypePprintName
      , Some (_equalAlias env aliasVar aliasedTypeEqualName))
    else
      let msg = lam tyStr. join [
        "Type variable ", tyStr, " references unknown type."
      ] in
      reportError msg
  else (_pprintUnknown, None ())

let generateUtestFunctions =
  use MExprAst in
  use MExprPrettyPrint in
  lam env : UtestTypeEnv.
  -- NOTE(larshum, 2021-03-29): The fallback equality function should never be
  -- called because attempts to use it are to be caught statically for better
  -- error reporting.
  let fallbackEqFunc = lam ty.
    lam_ "a" ty (lam_ "b" ty never_)
  in
  recursive let f = lam seq. lam ty. lam ids.
    match ids with (pprintName, equalName) then
      match getTypeFunctions env ty with (pprintFunc, equalFunc) then
        let eqFunc =
          match equalFunc with Some eqFunc then eqFunc else fallbackEqFunc ty
        in
        cons ( (pprintName, tyunknown_, pprintFunc)
             , (equalName, tyunknown_, eqFunc))
             seq
      else never
    else never
  in
  match unzip (mapFoldWithKey f [] env.typeFunctions) with (pprints, equals) then
    if null pprints then
      uunit_
    else
      bind_ (nreclets_ pprints) (nreclets_ equals)
  else never

let utestRunnerCall =
  lam info. lam usingStr. lam lPprintFunc. lam rPprintFunc.
  lam eqFunc. lam l. lam r.
  appSeq_ (nvar_ (utestRunnerName ()))
    [str_ info, str_ usingStr, lPprintFunc, rPprintFunc, eqFunc, l, r]

lang UtestViaMatch = Ast + PrettyPrint
  sem mkPatsAndExprs (env : UtestTypeEnv) /- : Expr -> ([Expr], Pat) -/ =
  | t ->
    let pprintTy = use MExprPrettyPrint in
      lam ty.
      match getTypeStringCode 0 pprintEnvEmpty ty with (_, tyStr) then
        tyStr
      else never
    in
    let name = nameSym "x" in
    let ty = tyTm t in
    let equalName = getEqualFuncName env ty in
    if typeHasDefaultEquality env ty then
      ([appf2_ (nvar_ equalName) (nvar_ name) t], npvar_ name)
    else
      let msg = join [
        "Utest needs a custom equality function to be provided, or for the expected value to be a literal. ",
        "No default equality implemented for type ", pprintTy ty, "."
      ] in errorSingle [infoTm t] msg
end

lang UtestViaMatchInt = UtestViaMatch + IntAst
  sem mkPatsAndExprs (env : UtestTypeEnv) /- : Expr -> ([Expr], Pat) -/ =
  | TmConst {val = CInt {val = val}} -> ([], pint_ val)
end

lang UtestViaMatchBool = UtestViaMatch + BoolAst
  sem mkPatsAndExprs (env : UtestTypeEnv) /- : Expr -> ([Expr], Pat) -/ =
  | TmConst {val = CBool {val = val}} -> ([], pbool_ val)
end

lang UtestViaMatchChar = UtestViaMatch + CharAst
  sem mkPatsAndExprs (env : UtestTypeEnv) /- : Expr -> ([Expr], Pat) -/ =
  | TmConst {val = CChar {val = val}} -> ([], pchar_ val)
end

lang UtestViaMatchSeq = UtestViaMatch + SeqAst
  sem mkPatsAndExprs (env : UtestTypeEnv) /- : Expr -> ([Expr], Pat) -/ =
  | TmSeq {tms = tms} ->
    let f = lam acc. lam t.
      let res: ([Expr], Pat) = mkPatsAndExprs env t in
      (concat acc res.0, res.1) in
    let res: ([Expr], [Pat]) = mapAccumL f [] tms in
    (res.0, pseqtot_ res.1)
end

lang UtestViaMatchRecord = UtestViaMatch + RecordAst + RecordTypeAst + RecordPat
  sem mkPatsAndExprs (env : UtestTypeEnv) /- : Expr -> ([Expr], Pat) -/ =
  | TmRecord {bindings = bindings} ->
    let f = lam acc. lam. lam t.
      let res: ([Expr], Pat) = mkPatsAndExprs env t in
      (concat acc res.0, res.1) in
    let res: ([Expr], Map SID Pat) = mapMapAccum f [] bindings in
    let pat = PatRecord
      { bindings = res.1
      , info = makeInfo (posVal "utest_via_match" 0 0) (posVal "utest_via_match" 0 0)
      , ty = TyRecord
        { info = NoInfo ()
        , fields = mapMap (lam. tyunknown_) res.1
        }
      } in
    (res.0, pat)
end

lang UtestViaMatchData = UtestViaMatch + DataAst
  sem mkPatsAndExprs (env : UtestTypeEnv) /- : Expr -> ([Expr], Pat) -/ =
  | TmConApp {ident = ident, body = body} ->
    let res: ([Expr], Pat) = mkPatsAndExprs env body in
    (res.0, npcon_ ident res.1)
end

lang MExprUtestViaMatch = MExprAst + UtestViaMatchInt + UtestViaMatchBool + UtestViaMatchChar + UtestViaMatchSeq + UtestViaMatchRecord + UtestViaMatchData
end

let _generateUtest = use MExprTypeAnnot in
  lam env : UtestTypeEnv.
  lam t : {test : Expr, expected : Expr, next : Expr, tusing : Option Expr,
           ty : Type, info : Info}.
  let pprintTy = use MExprPrettyPrint in
    lam ty.
    match getTypeStringCode 0 pprintEnvEmpty ty with (_, tyStr) then
      tyStr
    else never
  in
  let utestInfo = info2str t.info in
  let usingStr =
    match t.tusing with Some expr then
      use MExprPrettyPrint in concat "\n    Using: " (expr2str expr)
    else ""
  in
  -- NOTE(aathn, 2022-03-09): We assume that the types of the operands
  -- have already been annotated and checked by type-check.mc or
  -- type-annot.mc.
  match t.tusing with Some eqFunc then
    let lhsPprintName = getPprintFuncName env (tyTm t.test) in
    let rhsPprintName = getPprintFuncName env (tyTm t.expected) in
    let lhsPprintFunc = nvar_ lhsPprintName in
    let rhsPprintFunc = nvar_ rhsPprintName in
    let eqFunc =
      lam_ "a" (tyTm t.test)
        (lam_ "b" (tyTm t.expected)
          (appf2_ eqFunc (var_ "a") (var_ "b"))) in
    utestRunnerCall utestInfo usingStr lhsPprintFunc rhsPprintFunc eqFunc
                    t.test t.expected
  else
    let eTy = tyTm t.test in
    let pprintName = getPprintFuncName env eTy in
    let pprintFunc = nvar_ pprintName in
    use MExprUtestViaMatch in
    let res: ([Expr], Pat) = mkPatsAndExprs env t.expected in
    match res with (conditions, pat & !PatNamed _) then
      -- NOTE(vipa, 2021-06-14): The expected value has some useful
      -- structure that we can use, make the equality function a match
      -- instead
      let lName = nameSym "l" in
      let inner = foldl and_ true_ conditions in
      let eqFunc = nulam_ lName (ulam_ "" (match_ (nvar_ lName) pat inner false_)) in
      utestRunnerCall utestInfo usingStr pprintFunc pprintFunc eqFunc t.test
                      t.expected
    else
      -- NOTE(vipa, 2021-06-14): We couldn't find any useful structure
      -- in the expected field, just use the default equality, if
      -- there is one
      let equalName = getEqualFuncName env eTy in
      let eqFunc =
        if typeHasDefaultEquality env eTy then
          nvar_ equalName
        else
          let msg = join [
            "Utest needs a custom equality function to be provided. ",
            "No default equality implemented for type ", pprintTy eTy, "."
          ] in
          errorSingle [t.info] msg
      in
      utestRunnerCall utestInfo usingStr pprintFunc pprintFunc eqFunc t.test
                      t.expected

let constructSymbolizeEnv = lam env : UtestTypeEnv.
  let constructorNames = mapFoldWithKey (lam acc. lam. lam constructors.
    foldl (lam acc. lam n. mapInsert (nameGetStr n) n acc)
          acc
          (mapKeys constructors)
  ) (mapEmpty cmpString) env.variants in
  let typeNames = mapFoldWithKey (lam acc. lam typeId. lam.
    mapInsert (nameGetStr typeId) typeId acc) (mapEmpty cmpString) env.variants in
  let typeNames = mapFoldWithKey (lam acc. lam id. lam.
    mapInsert (nameGetStr id) id acc) typeNames env.aliases in
   {{symEnvEmpty with conEnv = constructorNames}
                 with tyConEnv = typeNames}

let withUtestRunner = lam utestFunctions. lam term.
  bindall_ [utestRunner (), utestFunctions, ulet_ "" term, print_ (str_ "\n")]

-- NOTE(linnea, 2021-03-17): Assumes that typeAnnot has been called prior to the
-- transformation.
lang MExprUtestTrans = MExprAst
  sem utestStripH =
  | TmUtest t -> utestStripH t.next
  | t -> smap_Expr_Expr utestStripH t

  sem utestStrip =
  | t -> utestStripH t

  sem utestGenH (env : UtestTypeEnv) =
  | TmUtest t ->
    let test = utestGenH env t.test in
    let expected = utestGenH env t.expected in
    let tusing = optionMap (utestGenH env) t.tusing in
    let t =
      { { { t with test = test }
              with expected = expected }
              with tusing = tusing }
    in
    bind_ (ulet_ "" (_generateUtest env t))
          (utestGenH env t.next)
  | t -> smap_Expr_Expr (utestGenH env) t

  -- NOTE(larshum, 2021-10-26): If a test has failed, we want to return a
  -- non-zero exit code to indicate failure.
  sem returnNonZeroIfTestsFailed =
  | TmLet t -> TmLet {t with inexpr = returnNonZeroIfTestsFailed t.inexpr}
  | TmRecLets t -> TmRecLets {t with inexpr = returnNonZeroIfTestsFailed t.inexpr}
  | TmType t -> TmType {t with inexpr = returnNonZeroIfTestsFailed t.inexpr}
  | TmConDef t -> TmConDef {t with inexpr = returnNonZeroIfTestsFailed t.inexpr}
  | TmExt t -> TmExt {t with inexpr = returnNonZeroIfTestsFailed t.inexpr}
  | t ->
    let info = infoTm t in
    -- NOTE(larshum, 2021-10-26): Check if a test failed, which is true if the
    -- 'numFailed' reference contains a non-zero value.
    let testsFailedCond = TmApp {
      lhs = TmApp {
        lhs = TmConst {
          val = CGti (), info = info,
          ty = TyArrow {
            from = TyArrow {
              from = TyInt {info = info},
              to = TyInt {info = info}, info = info},
            to = TyInt {info = info},
            info = info}},
        rhs = TmApp {
          lhs = TmConst {
            val = CDeRef (), info = info,
            ty = TyArrow {
              from = TyUnknown {info = info},
              to = TyUnknown {info = info}, info = info}},
          rhs = TmVar {
            ident = numFailedName (), info = info,
            ty = TyUnknown {info = info},
            frozen = false},
          ty = TyInt {info = info}, info = info},
        ty = TyArrow {
          from = TyInt {info = info}, to = TyBool {info = info},
          info = info},
        info = info},
      rhs = TmConst {val = CInt {val = 0}, ty = TyInt {info = info}, info = info},
      ty = TyBool {info = info}, info = info} in
    -- NOTE(larshum, 2021-10-26): This produces code equivalent to
    --   'if testsFailed then t; exit 1 else t'
    -- where t is the final expression of the MExpr AST.
    TmMatch {
      target = testsFailedCond,
      pat = PatBool {val = true, info = info, ty = TyBool {info = info}},
      thn = TmLet {
        ident = nameSym "", tyAnnot = tyTm t, tyBody = tyTm t, body = t,
        inexpr = TmApp {
          lhs = TmConst {
            val = CExit (), info = info,
            ty = TyArrow {
              from = TyInt {info = info}, to = TyUnknown {info = info},
              info = info}},
          rhs = TmConst {
            val = CInt {val = 1}, info = info,
            ty = TyInt {info = info}},
          ty = TyUnknown {info = info},
          info = info},
        ty = TyUnknown {info = info}, info = info},
      els = t, ty = tyTm t, info = info}

  sem utestGen =
  | t ->
    let env : UtestTypeEnv = collectKnownProgramTypes t in
    let utestFunctions = generateUtestFunctions env in
    let t = utestGenH env t in
    let t = returnNonZeroIfTestsFailed t in
    -- NOTE(larshum, 2021-03-27): We will need to create a symbolization
    -- environment here to avoid errors later because the generated utest
    -- functions will be placed before the definitions of any types in the
    -- program.
    let symEnv = constructSymbolizeEnv env in
    (symEnv, withUtestRunner utestFunctions t)
end

lang TestLang = MExprUtestTrans + MExprEq + MExprTypeAnnot
end

mexpr

use TestLang in

let default_info =
  Info { filename = "utesttrans.mc"
       , row1 = 0, col1 = 0, row2 = 0, col2 = 0}
in

let utest_info_ =
  lam t. lam e. lam n.
  TmUtest { test = t
          , expected = e
          , next = n
          , tusing = None ()
          , ty = tyunknown_
          , info = default_info}
in

let utestu_info_ =
  lam t. lam e. lam n. lam u.
  TmUtest { test = t
          , expected = e
          , next = n
          , tusing = Some u
          , ty = tyunknown_
          , info = default_info}
in

let intNoUsing = typeAnnot (utest_info_ (int_ 1) (int_ 0) uunit_) in
utest utestStrip intNoUsing with uunit_ using eqExpr in

let intWithUsing = typeAnnot (
  utestu_info_ (int_ 1) (int_ 0) uunit_ (uconst_ (CGeqi{}))) in
utest utestStrip intWithUsing with uunit_ using eqExpr in

let lhs = seq_ [seq_ [int_ 1, int_ 2], seq_ [int_ 3, int_ 4]] in
let rhs = reverse_ (seq_ [
  reverse_ (seq_ [int_ 4, int_ 3]),
  reverse_ (seq_ [int_ 2, int_ 1])]) in
let nestedSeqInt = typeAnnot (utest_info_ lhs rhs uunit_) in
utest utestStrip nestedSeqInt with uunit_ using eqExpr in

let lhs = seq_ [
  float_ 6.5, float_ 1.0, float_ 0.0, float_ 3.14
] in
let rhs = reverse_ (seq_ [
  float_ 3.14, float_ 0.0, float_ 1.0, float_ 6.5
]) in
let elemEq = uconst_ (CEqf ()) in
let seqEq =
  bind_
    (let_ "seqEq" (tyarrows_ [tyseq_ tyfloat_, tyseq_ tyfloat_, tybool_])
      (ulam_ "a" (ulam_ "b"
        (appf3_ (var_ "eqSeq") elemEq (var_ "a") (var_ "b")))))
    (var_ "seqEq") in
let floatSeqWithUsing = typeAnnot (utestu_info_ lhs rhs uunit_ seqEq) in
utest utestStrip floatSeqWithUsing with uunit_ using eqExpr in

let charNoUsing = typeAnnot (utest_info_ (char_ 'a') (char_ 'A') uunit_) in
utest utestStrip charNoUsing with uunit_ using eqExpr in

let charWithUsing = typeAnnot (bindall_ [
  ulet_ "leqChar" (ulam_ "c1" (ulam_ "c2" (
    leqi_ (char2int_ (var_ "c1")) (char2int_ (var_ "c2"))
  ))),
  ulet_ "geqChar" (ulam_ "c1" (ulam_ "c2" (
    geqi_ (char2int_ (var_ "c1")) (char2int_ (var_ "c2"))
  ))),
  ulet_ "char2lower" (ulam_ "c" (
    if_
      (and_
        (appf2_ (var_ "geqChar") (var_ "c") (char_ 'A'))
        (appf2_ (var_ "leqChar") (var_ "c") (char_ 'Z')))
      (int2char_ (addi_ (char2int_ (var_ "c")) (int_ 32)))
      (var_ "c")
  )),
  ulet_ "charEqIgnoreCase"
    (ulam_ "a"
      (ulam_ "b"
        (eqc_
          (app_ (var_ "char2lower") (var_ "a"))
          (app_ (var_ "char2lower") (var_ "b"))))),
  utestu_info_ (char_ 'a') (char_ 'A') uunit_ (var_ "charEqIgnoreCase")
]) in

let baseRecordFields = [
  ("a", int_ 4),
  ("b", true_),
  ("c", char_ 'x'),
  ("d", seq_ [int_ 1, int_ 2, int_ 4, int_ 8]),
  ("e", urecord_ [
    ("x", int_ 1),
    ("y", int_ 0)
  ])
] in
let r = urecord_ baseRecordFields in
let recordNoUsing = typeAnnot (utest_info_ r r uunit_) in
utest utestStrip recordNoUsing with uunit_ using eqExpr in

let lhs = urecord_ (cons ("k", int_ 4) baseRecordFields) in
let rhs = urecord_ (cons ("k", int_ 2) baseRecordFields) in
let recordEq =
  ulam_ "r1" (ulam_ "r2" (
    eqi_ (recordproj_ "k" (var_ "r1")) (recordproj_ "k" (var_ "r2"))
  ))
in
let recordWithUsing = typeAnnot (utestu_info_ lhs rhs uunit_ recordEq) in
utest utestStrip recordWithUsing with uunit_ using eqExpr in

()
