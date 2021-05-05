include "bool.mc"
include "string.mc"
include "name.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/builtin.mc"
include "mexpr/eq.mc"
include "mexpr/eval.mc"
include "mexpr/type-annot.mc"
include "mexpr/type-lift.mc"
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
let head = lam seq. get seq 0 in
let tail = lam seq. subsequence seq 1 (length seq) in
let null = lam seq. eqi (length seq) 0 in

recursive
  let foldl = lam f. lam acc. lam seq.
    if null seq then acc
    else foldl f (f acc (head seq)) (tail seq)
in
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

let inf =
  divf 1.0 0.0
in

-- A naive float2string implementation that only formats in standard form
let float2string = lam arg.
  -- Quick fix to check for infinities
  if eqf arg inf then \"INFINITY\" else
  if eqf arg (negf inf) then \"-INFINITY\" else
  -- End of quick fix
  let precision = 7 in -- Precision in number of digits
  let prefixpair = if ltf arg 0.0 then (\"-\", negf arg) else (\"\", arg) in
  let prefix = prefixpair.0 in
  let val = prefixpair.1 in
  recursive
  let float2string_rechelper = lam prec. lam digits. lam v.
    -- Assume 0 <= v < 10
    if eqi prec digits then
      \"\"
    else if eqf v 0.0 then
      \"0\"
    else
      let fstdig = floorfi v in
      let remaining = mulf (subf v (int2float fstdig)) 10.0 in
      let c = int2char (addi fstdig (char2int '0')) in
      cons c (float2string_rechelper prec (addi digits 1) remaining)
  in
  recursive
  let positiveExponentPair = lam acc. lam v.
    if ltf v 10.0
    then (v, acc)
    else positiveExponentPair (addi acc 1) (divf v 10.0)
  in
  recursive
  let negativeExponentPair = lam acc. lam v.
    if geqf v 1.0
    then (v, acc)
    else negativeExponentPair (addi acc 1) (mulf v 10.0)
  in
  let res = if eqf val 0.0 then
              \"0.0\"
            else if gtf val 1.0 then
              let pospair = positiveExponentPair 0 val in
              let retstr = float2string_rechelper precision 0 (pospair.0) in
              let decimals = cons (head retstr) (cons '.' (tail retstr)) in
              concat decimals (concat \"e+\" (int2string pospair.1))
            else
              let pospair = negativeExponentPair 0 val in
              let retstr = float2string_rechelper precision 0 (pospair.0) in
              let decimals = cons (head retstr) (cons '.' (tail retstr)) in
              concat decimals (concat \"e-\" (int2string pospair.1))
  in
  concat prefix res
in

recursive
  let strJoin = lam delim. lam strs.
    if eqi (length strs) 0
    then \"\"
    else if eqi (length strs) 1
         then head strs
         else concat (concat (head strs) delim) (strJoin delim (tail strs))
in

let mapi = lam f. lam seq.
  recursive let work = lam i. lam f. lam seq.
      if null seq then []
      else cons (f i (head seq)) (work (addi i 1) f (tail seq))
  in
  work 0 f seq
in

let map = lam f. mapi (lam. lam x. f x) in

let eqSeq = lam eq : (Unknown -> Unknown -> Bool).
  recursive let work = lam as. lam bs.
    let pair = (as, bs) in
    match pair with ([], []) then true else
    match pair with ([a] ++ as, [b] ++ bs) then
      if eq a b then work as bs else false
    else false
  in work
in

let and : Bool -> Bool -> Bool =
  lam a. lam b. if a then b else false
in

recursive
  let all = lam p. lam seq.
    if null seq
    then true
    else and (p (head seq)) (all p (tail seq))
in

let utestTestPassed = lam.
  print \".\"
in

let utestTestFailed =
  lam line   : String.
  lam lhsStr : String.
  lam rhsStr : String.
  printLn \"\";
  printLn (join [\" ** Unit test FAILED on line \", line, \" **\"]);
  printLn (join [\"    LHS: \", lhsStr]);
  printLn (join [\"    RHS: \", rhsStr])
in

let utestRunner =
  lam info    : {row : String}.
  lam lpprint : Unknown -> String.
  lam rpprint : Unknown -> String.
  lam eqfunc  : Unknown -> Unknown -> Bool.
  lam lhs     : Unknown.
  lam rhs     : Unknown.
  -- Comparison
  if eqfunc lhs rhs then
    utestTestPassed ()
  else
    utestTestFailed info.row (lpprint lhs) (rpprint rhs)
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
    let code = parseMExprString [] _utestRunnerStr in
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
      else match expr with TmExt {ident = ident, inexpr = inexpr} then
        if eqString (nameGetStr ident) str then Some ident
        else match findNameH (None ()) inexpr with Some n then Some n
        else None ()
      else sfold_Expr_Expr findNameH (None ()) expr
    in
    findNameH (None ()) expr


let utestRunnerName = lam. optionGetOrElse
  (lam. error "Expected utestRunner to be defined")
  (findName "utestRunner" (utestRunner ()))

let getUniquePprintAndEqualityNames = lam.
  (nameSym "pp", nameSym "eq")

let collectKnownProgramTypes = use MExprAst in
  lam expr.
  recursive let unwrapTypeVarIdent = lam ty.
    match ty with TyVar {ident = ident} then Some ident
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
    infoErrorExit info msg
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
      match t.tyIdent with TyArrow {from = argTy, to = to} then
        match unwrapTypeVarIdent to with Some ident then
          let constructors =
            match mapLookup ident acc.variants with Some constructors then
              mapInsert t.ident argTy constructors
            else
              let msg = join [
                "Constructor definition refers to undefined type ",
                nameGetStr ident
              ] in
              infoErrorExit (infoTm expr) msg
          in
          let variants = mapInsert ident constructors acc.variants in
          let acc = collectType acc argTy in
          let acc = {acc with variants = variants} in
          sfold_Expr_Expr collectTypes acc expr
        else expectedArrowType (infoTm expr) t.tyIdent
      else expectedArrowType (infoTm expr) t.tyIdent
    else match expr with TmUtest t then
      let acc = collectType acc (ty t.test) in
      let acc = collectType acc (ty t.expected) in
      let acc =
        match t.tusing with Some t then
          match ty t with TyArrow {from = lhs, to = TyArrow {from = rhs, to = TyBool _}} then
            collectType (collectType acc lhs) rhs
          else
            let msg = join [
              "Arguments of equality function must be properly annotated"
            ] in
            infoErrorExit (infoTm t) msg
        else acc
      in
      collectTypes acc t.next
    else sfold_Expr_Expr collectTypes acc expr
  in
  let emptyUtestTypeEnv = {
    variants = mapEmpty nameCmp,      -- Map Name Type
    aliases = mapEmpty nameCmp,       -- Map Name Type
    typeFunctions = mapEmpty _cmpType -- Map Type (Name, Name)
  } in
  collectTypes emptyUtestTypeEnv expr

let _unwrapAlias = use MExprAst in
  lam aliases : Map Name Type. lam ty : Type.
  match ty with TyVar t then
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
  lam_ "a" tyfloat_ (app_ (var_ "float2string") (var_ "a"))

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
          (appf2_ (var_ "map") (nvar_ elemPprintFuncName) (var_ "a")),
        str_ "]"
      ]))

let _equalSeq = lam ty. lam elemEqualFuncName.
  lam_ "a" ty (lam_ "b" ty
    (appf3_ (var_ "eqSeq") (nvar_ elemEqualFuncName) (var_ "a") (var_ "b")))

let _pprintRecord = use MExprAst in
  lam env. lam ty. lam fields.
  if mapIsEmpty fields then lam_ "a" ty (str_ "()")
  else
    let recordBindings =
      mapMapWithKey (lam id. lam. pvar_ (sidToString id)) fields
    in
    let recordPattern =
      PatRecord {bindings = recordBindings, info = NoInfo ()}
    in
    let pprintSeq =
      match _record2tuple fields with Some types then
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

let _equalRecord = use MExprAst in
  lam env. lam ty. lam fields.
  let recordBindings = lam prefix.
    mapMapWithKey (lam id. lam. pvar_ (join [prefix, sidToString id])) fields
  in
  let lhsPrefix = "lhs_" in
  let rhsPrefix = "rhs_" in
  let matchPattern =
    ptuple_ [
      PatRecord {bindings = recordBindings lhsPrefix, info = NoInfo ()},
      PatRecord {bindings = recordBindings rhsPrefix, info = NoInfo ()}] in
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
    else appf2_ (var_ "all") (ulam_ "b" (var_ "b")) (seq_ equalFuncs)
  in
  lam_ "a" ty (lam_ "b" ty
    (match_ (tuple_ [var_ "a", var_ "b"])
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
  let constrEqual = lam cont. lam constrId. lam argTy.
    let equalFuncId = getEqualFuncName env argTy in
    let lhsId = nameSym "lhs" in
    let rhsId = nameSym "rhs" in
    let constructorPattern = ptuple_ [
      pcon_ (nameGetStr constrId) (npvar_ lhsId),
      pcon_ (nameGetStr constrId) (npvar_ rhsId)
    ] in
    match_ (tuple_ [var_ "a", var_ "b"])
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
    match ty with TyInt _ | TyBool _ | TyChar _ then true
    else match ty with TySeq t | TyTensor t then
      work visited t.ty
    else match ty with TyRecord t then
      mapAll (lam ty. work visited ty) t.fields
    else match ty with TyVar t then
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
      infoErrorExit (infoTy ty) (msg tyStr)
    else never
  in
  match ty with TyInt _ then
    (_pprintInt, Some _equalInt)
  else match ty with TyFloat _ then
    (_pprintFloat, None ())
  else match ty with TyBool _ then
    (_pprintBool, Some _equalBool)
  else match ty with TyChar _ then
    (_pprintChar, Some _equalChar)
  else match ty with TySeq {ty = elemTy} then
    let elemPprintName = getPprintFuncName env elemTy in
    let elemEqualName = getEqualFuncName env elemTy in
    (_pprintSeq ty elemPprintName, Some (_equalSeq ty elemEqualName))
  else match ty with TyRecord {fields = fields} then
    ( _pprintRecord env ty fields
    , Some (_equalRecord env ty fields))
  else match ty with TyVar {ident = ident} then
    match mapLookup ident env.variants with Some constrs then
      let annotTy = ntyvar_ ident in
      if all (lam ty. typeHasDefaultEquality env ty) (mapValues constrs) then
        ( _pprintVariant env annotTy constrs
        , Some (_equalVariant env annotTy constrs))
      else
        (_pprintVariant env annotTy constrs, None ())
    else match mapLookup ident env.aliases with Some ty then
      let aliasVar = ntyvar_ ident in
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
      unit_
    else
      bind_ (nreclets_ pprints) (nreclets_ equals)
  else never

let utestRunnerCall =
  lam info : {row : String}. lam lPprintFunc. lam rPprintFunc.
  lam eqFunc. lam l. lam r.
  appf6_
    (nvar_ (utestRunnerName ()))
    (record_ [
      ("row", str_ info.row)])
    lPprintFunc
    rPprintFunc
    eqFunc
    l
    r

let _generateUtest = use MExprAst in
  lam env : UtestTypeEnv.
  lam t : {test : Expr, expected : Expr, next : Expr, tusing : Option Expr,
           ty : Type, info : Info}.
  let pprintTy = use MExprPrettyPrint in
    lam ty.
    match getTypeStringCode 0 pprintEnvEmpty ty with (_, tyStr) then
      tyStr
    else never
  in
  let utestInfo =
    match t.info with Info {row1 = row} then
      {row = int2string row}
    else match t.info with NoInfo () then
      {row = "0"}
    else never
  in
  -- NOTE(larshum, 2021-04-12): We only require that the types of the operands
  -- are compatible if no equality function is provided. Otherwise it should be
  -- possible to compare different types using a custom equality function, but
  -- this function has to be annotated with explicit types.
  match t.tusing with Some eqFunc then
    match ty eqFunc with TyArrow {from = lty, to = TyArrow {from = rty, to = TyBool _}} then
      match compatibleType env.aliases (ty t.test) lty with Some lty then
        match compatibleType env.aliases (ty t.expected) rty with Some rty then
          let lhsPprintName = getPprintFuncName env lty in
          let rhsPprintName = getPprintFuncName env rty in
          let lhsPprintFunc = nvar_ lhsPprintName in
          let rhsPprintFunc = nvar_ rhsPprintName in
          let eqFunc =
            lam_ "a" lty
              (lam_ "b" rty
                (appf2_ eqFunc (var_ "a") (var_ "b"))) in
          utestRunnerCall utestInfo lhsPprintFunc rhsPprintFunc eqFunc
                          t.test t.expected
        else
          let msg = join [
            "Custom equality function expected right-hand side of type ",
            pprintTy rty, ", got argument of incompatible type ",
            pprintTy (ty t.expected)
          ] in
          infoErrorExit t.info msg
      else
        let msg = join [
          "Custom equality function expected left-hand side of type ",
          pprintTy lty, ", got argument of incompatible type ",
          pprintTy (ty t.test)
        ] in
        infoErrorExit t.info msg
    else
      let msg = join [
        "Equality function was found to have incorrect type.\n",
        "Type was inferred to be ", pprintTy (ty eqFunc)
      ] in
      infoErrorExit t.info msg
  else match compatibleType env.aliases (ty t.test) (ty t.expected) with Some ty then
    let pprintName = getPprintFuncName env ty in
    let equalName = getEqualFuncName env ty in
    let pprintFunc = nvar_ pprintName in
    let eqFunc =
      if typeHasDefaultEquality env ty then
        nvar_ equalName
      else
        let msg = join [
          "Utest needs a custom equality function to be provided. ",
          "No default equality implemented for type ", pprintTy ty, "."
        ] in
        infoErrorExit t.info msg
    in
    utestRunnerCall utestInfo pprintFunc pprintFunc eqFunc t.test t.expected
  else
    let msg = join [
      "Arguments to utest have incompatible types\n",
      "LHS: ", pprintTy (ty t.test), "\nRHS: ", pprintTy (ty t.expected)
    ] in
    infoErrorExit t.info msg

let constructSymbolizeEnv = lam env : UtestTypeEnv.
  let constructorNames = mapFoldWithKey (lam acc. lam. lam constructors.
    foldl (lam acc. lam n. mapInsert (nameGetStr n) n acc)
          acc
          (mapKeys constructors)
  ) (mapEmpty cmpString) env.variants in
  let typeNames = mapFoldWithKey (lam acc. lam typeId. lam.
    mapInsert (nameGetStr typeId) typeId) (mapEmpty cmpString) env.variants in
  let typeNames = mapFoldWithKey (lam acc. lam id. lam.
    mapInsert (nameGetStr id) id) typeNames env.aliases in
   {{symEnvEmpty with conEnv = constructorNames}
                 with tyEnv = typeNames}

let withUtestRunner = lam utestFunctions. lam term.
  bindall_ [utestRunner (), utestFunctions, term]

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
    bind_ (ulet_ "" (_generateUtest env t))
          (utestGenH env t.next)
  | t -> smap_Expr_Expr (utestGenH env) t

  sem utestGen =
  | t ->
    let env : UtestTypeEnv = collectKnownProgramTypes t in
    let utestFunctions = generateUtestFunctions env in
    let t = utestGenH env t in
    -- NOTE(larshum, 2021-03-27): We will need to create a symbolization
    -- environment here to avoid errors later because the generated utest
    -- functions will be placed before the definitions of any types in the
    -- program.
    let symEnv = constructSymbolizeEnv env in
    (symEnv, withUtestRunner utestFunctions t)
end

lang TestLang = MExprUtestTrans + MExprEq + MExprTypeAnnot + MExprEval

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

let intNoUsing = typeAnnot (utest_info_ (int_ 1) (int_ 0) unit_) in
-- eval {env = builtinEnv} (symbolize (utestGen intNoUsing));
utest utestStrip intNoUsing with unit_ using eqExpr in

let intWithUsing = typeAnnot (
  utestu_info_ (int_ 1) (int_ 0) unit_ (uconst_ (CGeqi{}))) in
-- eval {env = builtinEnv} (symbolize (utestGen intWithUsing));
utest utestStrip intWithUsing with unit_ using eqExpr in

let lhs = seq_ [seq_ [int_ 1, int_ 2], seq_ [int_ 3, int_ 4]] in
let rhs = reverse_ (seq_ [
  reverse_ (seq_ [int_ 4, int_ 3]),
  reverse_ (seq_ [int_ 2, int_ 1])]) in
let nestedSeqInt = typeAnnot (utest_info_ lhs rhs unit_) in
-- eval {env = builtinEnv} (symbolize (utestGen nestedSeqInt));
utest utestStrip nestedSeqInt with unit_ using eqExpr in

let lhs = seq_ [
  float_ 6.5, float_ 1.0, float_ 0.0, float_ 3.14
] in
let rhs = reverse_ (seq_ [
  float_ 3.14, float_ 0.0, float_ 1.0, float_ 6.5
]) in
let elemEq = uconst_ (CEqf ()) in
let seqEq =
  ulam_ "a"
    (ulam_ "b" (appf3_ (var_ "eqSeq") elemEq (var_ "a") (var_ "b"))) in
let floatSeqWithUsing = typeAnnot (utestu_info_ lhs rhs unit_ seqEq) in
-- eval {env = builtinEnv} (symbolize (utestGen floatSeqWithUsing));
utest utestStrip floatSeqWithUsing with unit_ using eqExpr in

let charNoUsing = typeAnnot (utest_info_ (char_ 'a') (char_ 'A') unit_) in
-- eval {env = builtinEnv} (symbolize (utestGen charNoUsing));
utest utestStrip charNoUsing with unit_ using eqExpr in

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
  utestu_info_ (char_ 'a') (char_ 'A') unit_ (var_ "charEqIgnoreCase")
]) in
-- eval {env = builtinEnv} (symbolize (utestGen charWithUsing));

let baseRecordFields = [
  ("a", int_ 4),
  ("b", true_),
  ("c", char_ 'x'),
  ("d", seq_ [int_ 1, int_ 2, int_ 4, int_ 8]),
  ("e", record_ [
    ("x", int_ 1),
    ("y", int_ 0)
  ])
] in
let r = record_ baseRecordFields in
let recordNoUsing = typeAnnot (utest_info_ r r unit_) in
-- eval {env = builtinEnv} (symbolize (utestGen recordNoUsing));
utest utestStrip recordNoUsing with unit_ using eqExpr in

let lhs = record_ (cons ("k", int_ 4) baseRecordFields) in
let rhs = record_ (cons ("k", int_ 2) baseRecordFields) in
let recordEq =
  ulam_ "r1" (ulam_ "r2" (
    eqi_ (recordproj_ "k" (var_ "r1")) (recordproj_ "k" (var_ "r2"))
  ))
in
let recordWithUsing = typeAnnot (utestu_info_ lhs rhs unit_ recordEq) in
-- eval {env = builtinEnv} (symbolize (utestGen recordWithUsing));
utest utestStrip recordWithUsing with unit_ using eqExpr in

()
