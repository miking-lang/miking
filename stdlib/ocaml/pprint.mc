include "ocaml/ast.mc"
include "mexpr/ast-builder.mc"
include "ocaml/symbolize.mc"
include "mexpr/pprint.mc"
include "mexpr/record.mc"
include "char.mc"
include "name.mc"
include "intrinsics-ops.mc"

let _isValidChar = lam c.
  if isAlphanum c then true
  else eqChar c '\''

let _escapeChar = lam c.
  if _isValidChar c then c else '_'

utest map _escapeChar "abcABC/:@_'" with "abcABC____'"

let escapeVarString = lam s.
  concat "v_" (map _escapeChar s)

let escapeConString = lam s.
  concat "C" (map _escapeChar s)

let escapeLabelString = lam s.
  concat "l_" (map _escapeChar s)

utest escapeVarString "abcABC/:@_'" with "v_abcABC____'"
utest escapeVarString "" with "v_"
utest escapeVarString "@" with "v__"
utest escapeVarString "ABC123" with "v_ABC123"
utest escapeVarString "'a/b/c" with "v_'a_b_c"
utest escapeVarString "123" with "v_123"

utest escapeConString "abcABC/:@_'" with "CabcABC____'"
utest escapeConString "" with "C"
utest escapeConString "@" with "C_"
utest escapeConString "ABC123" with "CABC123"
utest escapeConString "'a/b/c" with "C'a_b_c"
utest escapeConString "123" with "C123"

let escapeName = lam n.
  match n with (str,symb) then (escapeVarString str, symb)
  else never

let escapeConName = lam n.
  match n with (str,symb) then (escapeConString str, symb)
  else never

utest (escapeName ("abcABC/:@_'", gensym ())).0
with ("v_abcABC____'", gensym ()).0

utest (escapeName ("ABC123", gensym ())).0
with ("v_ABC123", gensym ()).0

-- Prefix of non-symbolized identifiers, to avoid collision with symbolized
-- identifiers
let noSymVarPrefix = "n"

let noSymConPrefix = "N"

-- Pretty-printing of MExpr types in OCaml. Due to the obj-wrapping, we do not
-- want to specify the type names in general. Record types are printed in a
-- different way because their types must be declared at the top of the program
-- in order to use them (e.g. for pattern matching). As type-lifting replaces
-- all nested record types with type variables, all fields of a record type
-- will be printed as Obj.t.
lang OCamlTypePrettyPrint =
  UnknownTypeAst + BoolTypeAst + IntTypeAst + FloatTypeAst + CharTypeAst +
  SeqTypeAst + RecordTypeAst + VariantTypeAst + ConTypeAst + AppTypeAst +
  FunTypePrettyPrint + OCamlTypeAst + IdentifierPrettyPrint + RecordTypeUtils

  sem getTypeStringCode (indent : Int) (env : PprintEnv) =
  | (TyRecord t) & ty ->
    if mapIsEmpty t.fields then (env, "Obj.t")
    else
      let orderedFields = tyRecordOrderedFields ty in
      let f = lam env. lam field : (SID, Type).
        match field with (sid, ty) in
        match getTypeStringCode indent env ty with (env,ty) in
        let str = pprintLabelString sid in
        (env, join [str, ": ", ty])
      in
      match mapAccumL f env orderedFields with (env, fields) in
      (env, join ["{", strJoin ";" fields, "}"])
  | OTyVar {ident = ident} -> pprintVarName env ident
  | OTyVarExt {ident = ident, args = []} -> (env, ident)
  | OTyVarExt {ident = ident, args = [arg]} ->
    match getTypeStringCode indent env arg with (env, arg) in
    (env, join [arg, " ", ident])
  | OTyVarExt {ident = ident, args = args} ->
    match mapAccumL (getTypeStringCode indent) env args with (env, args) in
    (env, join ["(", strJoin ", " args, ") ", ident])
  | _ -> (env, "Obj.t")
end

lang OCamlPrettyPrint =
  ConstPrettyPrint + OCamlAst +
  IdentifierPrettyPrint + NamedPatPrettyPrint + IntPatPrettyPrint +
  CharPatPrettyPrint + BoolPatPrettyPrint + OCamlTypePrettyPrint +
  AppPrettyPrint + MExprAst-- TODO(vipa, 2021-05-12): should MExprAst be here? It wasn't before, but some of the copied constants aren't in the others

  sem pprintOcamlTops =
  | tops ->
    let env = collectTopNames tops in
    match mapAccumL pprintTop env tops with (_, tops) then
      strJoin "\n" tops
    else never

  sem _nameSymString (esc : Name -> Name) =
  | name ->
    join [ nameGetStr (esc name)
         , "\'"
         , (int2string (sym2hash (optionGetOrElse
                                   (lam. error "Expected symbol")
                                   (nameGetSym name))))]

  sem _nameNoSymString (prefix : String) (esc : Name -> Name) =
  | name ->
    concat prefix (nameGetStr (esc name))

  sem pprintConName (env : PprintEnv) =
  | name ->
    (env,
     if nameHasSym name then
       _nameSymString escapeConName name
     else
       _nameNoSymString noSymConPrefix escapeConName name)

  sem pprintVarName (env : PprintEnv) =
  | name ->
    (env,
     match mapLookup name env.nameMap with Some n then n
     else if nameHasSym name then
       _nameSymString escapeName name
     else
       _nameNoSymString noSymVarPrefix escapeName name)

  sem pprintLabelString =
  | s -> escapeLabelString (sidToString s)

  sem isAtomic =
  | TmLam _ -> false
  | TmLet _ -> false
  | TmRecLets _ -> false
  | TmRecord _ -> true
  | TmRecordUpdate _ -> true
  | OTmArray _ -> true
  | OTmMatch _ -> false
  | OTmTuple _ -> true
  | OTmConApp {args = []} -> true
  | OTmConApp _ -> false
  | OTmVarExt _ -> true
  | OTmExprExt _ -> false
  | OTmConAppExt _ -> false
  | OTmString _ -> true
  | OTmLabel _ -> true
  | OTmRecord _ -> true
  | OTmProject _ -> true
  | OTmRecordUpdate _ -> true
  | OTmLam _ -> false
  | TmVar _ -> true

  sem patPrecedence =
  | OPatRecord _ -> 0
  | OPatCon {args = ![]} -> 2
  | OPatConExt _ -> 2

  sem getConstStringCode (indent : Int) =
  | CUnsafeCoerce _ -> "(fun x -> x)"
  -- NOTE(oerikss, 2023-10-06): Integer and float constant can here be both
  -- negative and positive. Note that -0 = 0, which is the reason for the
  -- condition on grouping below.
  | CInt {val = n} ->
    if eqi n 0 then "0"
    else
      let str = int2string n in
      if leqi n 0 then join ["(", str, ")"] else str
  | CFloat {val = f} ->
    if eqf f 0. then "0."
    else
      if eqf f (divf 1. 0.) then "infinity"
      else
        if eqf f (negf (divf 1. 0.)) then "neg_infinity"
        else
          let str = float2string f in
          if leqf f 0. then join ["(", str, ")"] else str
  | CAddi _ -> "Int.add"
  | CSubi _ -> "Int.sub"
  | CMuli _ -> "Int.mul"
  | CDivi _ -> "Int.div"
  | CModi _ -> "Int.rem"
  | CNegi _ -> "Int.neg"
  | CAddf _ -> "Float.add"
  | CSubf _ -> "Float.sub"
  | CMulf _ -> "Float.mul"
  | CDivf _ -> "Float.div"
  | CNegf _ -> "Float.neg"
  | CBool {val = b} -> if b then "true" else "false"
  | CEqi _ -> "((=) : int -> int -> bool)"
  | CLti _ -> "((<) : int -> int -> bool)"
  | CLeqi _ -> "((<=) : int -> int -> bool)"
  | CGti _ -> "((>) : int -> int -> bool)"
  | CGeqi _ -> "((>=) : int -> int -> bool)"
  | CNeqi _ -> "((<>) : int -> int -> bool)"
  | CSlli _ -> "Int.shift_left"
  | CSrli _ -> "Int.shift_right_logical"
  | CSrai _ -> "Int.shift_right"
  | CEqf _ -> "((=) : float -> float -> bool)"
  | CLtf _ -> "((<) : float -> float -> bool)"
  | CLeqf _ -> "((<=) : float -> float -> bool)"
  | CGtf _ -> "((>) : float -> float -> bool)"
  | CGeqf _ -> "((>=) : float -> float -> bool)"
  | CNeqf _ -> "((<>) : float -> float -> bool)"
  | CInt2float _ -> "float_of_int"
  | CChar {val = c} -> int2string (char2int c)
  | CEqc _ -> "Int.equal"
  | CChar2Int _ -> "Fun.id"
  | CInt2Char _ -> "Fun.id"
  | CRef _ -> "ref"
  | CModRef _ -> "(:=)"
  | CDeRef _ -> "(!)"
  | CConstructorTag _ -> intrinsicOpConTag "constructor_tag"
  | CFloorfi _ -> intrinsicOpFloat "floorfi"
  | CCeilfi _ -> intrinsicOpFloat "ceilfi"
  | CRoundfi _ -> intrinsicOpFloat "roundfi"
  | CStringIsFloat _ -> intrinsicOpFloat "string_is_float"
  | CString2float _ -> intrinsicOpFloat "string2float"
  | CFloat2string _ -> intrinsicOpFloat "float2string"
  | CCreate _ -> intrinsicOpSeq "create"
  | CCreateList _ -> intrinsicOpSeq "create_list"
  | CCreateRope _ -> intrinsicOpSeq "create_rope"
  | CIsList _ -> intrinsicOpSeq "is_list"
  | CIsRope _ -> intrinsicOpSeq "is_rope"
  | CLength _ -> intrinsicOpSeq "length"
  | CConcat _ -> intrinsicOpSeq "concat"
  | CGet _ -> intrinsicOpSeq "get"
  | CSet _ -> intrinsicOpSeq "set"
  | CCons _ -> intrinsicOpSeq "cons"
  | CSnoc _ -> intrinsicOpSeq "snoc"
  | CSplitAt _ -> intrinsicOpSeq "split_at"
  | CReverse _ -> intrinsicOpSeq "reverse"
  | CHead _ -> intrinsicOpSeq "head"
  | CTail _ -> intrinsicOpSeq "tail"
  | CNull _ -> intrinsicOpSeq "null"
  | CMap _ -> intrinsicOpSeq "map"
  | CMapi _ -> intrinsicOpSeq "mapi"
  | CIter _ -> intrinsicOpSeq "iter"
  | CIteri _ -> intrinsicOpSeq "iteri"
  | CFoldl _ -> intrinsicOpSeq "Helpers.fold_left"
  | CFoldr _ -> intrinsicOpSeq "Helpers.fold_right"
  | CSubsequence _ -> intrinsicOpSeq "subsequence"
  | CPrint _ -> intrinsicOpIO "print"
  | CPrintError _ -> intrinsicOpIO "print_error"
  | CDPrint _ -> intrinsicOpIO "dprint"
  | CFlushStdout _ -> intrinsicOpIO "flush_stdout"
  | CFlushStderr _ -> intrinsicOpIO "flush_stderr"
  | CReadLine _ -> intrinsicOpIO "read_line"
  | CArgv _ -> intrinsicOpSys "argv"
  | CFileRead _ -> intrinsicOpFile "read"
  | CFileWrite _ -> intrinsicOpFile "write"
  | CFileExists _ -> intrinsicOpFile "exists"
  | CFileDelete _ -> intrinsicOpFile "delete"
  | CError _ -> intrinsicOpSys "error"
  | CExit _ -> intrinsicOpSys "exit"
  | CCommand _ -> intrinsicOpSys "command"
  | CEqsym _ -> intrinsicOpSymb "eqsym"
  | CGensym _ -> intrinsicOpSymb "gensym"
  | CSym2hash _ -> intrinsicOpSymb "hash"
  | CRandIntU _ -> intrinsicOpRand "int_u"
  | CRandSetSeed _ -> intrinsicOpRand "set_seed"
  | CWallTimeMs _ -> intrinsicOpTime "get_wall_time_ms"
  | CSleepMs _ -> intrinsicOpTime "sleep_ms"
  | CTensorIterSlice _ -> intrinsicOpTensor "iter_slice"
  | CTensorCreateUninitInt _ -> intrinsicOpTensor "uninit_int_packed"
  | CTensorCreateUninitFloat _ -> intrinsicOpTensor "uninit_float_packed"
  | CTensorCreateInt _ -> intrinsicOpTensor "create_int_packed"
  | CTensorCreateFloat _ -> intrinsicOpTensor "create_float_packed"
  | CTensorCreate _ -> intrinsicOpTensor "create_generic_packed"
  | CTensorRank _ -> intrinsicOpTensor "rank"
  | CTensorShape _ -> intrinsicOpTensor "shape"
  | CTensorGetExn _ -> intrinsicOpTensor "get_exn"
  | CTensorSetExn _ -> intrinsicOpTensor "set_exn"
  | CTensorLinearGetExn _ -> intrinsicOpTensor "linear_get_exn"
  | CTensorLinearSetExn _ -> intrinsicOpTensor "linear_set_exn"
  | CTensorReshapeExn _ -> intrinsicOpTensor "reshape_exn"
  | CTensorCopy _ -> intrinsicOpTensor "copy"
  | CTensorTransposeExn _ -> intrinsicOpTensor "transpose_exn"
  | CTensorSliceExn _ -> intrinsicOpTensor "slice_exn"
  | CTensorSubExn _ -> intrinsicOpTensor "sub_exn"
  | CTensorEq _ -> intrinsicOpTensor "equal"
  | CTensorToString _ -> intrinsicOpTensor "to_string"
  | CBootParserParseMExprString _ -> intrinsicOpBootparser "parseMExprString"
  | CBootParserParseMLangString _ -> intrinsicOpBootparser "parseMLangString"
  | CBootParserParseMLangFile _ -> intrinsicOpBootparser "parseMLangFile"
  | CBootParserParseMCoreFile _ -> intrinsicOpBootparser "parseMCoreFile"
  | CBootParserGetId _ -> intrinsicOpBootparser "getId"
  | CBootParserGetTerm _ -> intrinsicOpBootparser "getTerm"
  | CBootParserGetTop _ -> intrinsicOpBootparser "getTop"
  | CBootParserGetDecl _ -> intrinsicOpBootparser "getDecl"
  | CBootParserGetType _ -> intrinsicOpBootparser "getType"
  | CBootParserGetString _ -> intrinsicOpBootparser "getString"
  | CBootParserGetInt _ -> intrinsicOpBootparser "getInt"
  | CBootParserGetFloat _ -> intrinsicOpBootparser "getFloat"
  | CBootParserGetListLength _ -> intrinsicOpBootparser "getListLength"
  | CBootParserGetConst _ -> intrinsicOpBootparser "getConst"
  | CBootParserGetPat _ -> intrinsicOpBootparser "getPat"
  | CBootParserGetInfo _ -> intrinsicOpBootparser "getInfo"

  sem collectTopNames =
  | tops ->
    let maybeAdd = lam name. lam str. lam env: PprintEnv.
      match mapLookup str env.strings with Some _ then
        env
      else
        {{env with nameMap = mapInsert name str env.nameMap}
              with strings = setInsert str env.strings}
    in
    let f = lam top. lam env.
      switch top
      case OTopLet t then
        maybeAdd t.ident (escapeVarString t.ident.0) env
      case OTopRecLets t then
        let f = lam binding : OCamlTopBinding. lam env.
          maybeAdd binding.ident (escapeVarString binding.ident.0) env
        in foldr f env t.bindings
      case top then
        env
      end
    in
    foldr f pprintEnvEmpty tops

  sem pprintTop (env : PprintEnv) =
  | OTopTypeDecl t ->
    let indent = 0 in
    match pprintVarName env t.ident with (env, ident) in
    match getTypeStringCode indent env t.ty with (env, ty) in
    (env, join ["type ", ident, " = ", ty, ";;"])
  | OTopVariantTypeDecl t ->
    let indent = 0 in
    let f = lam env. lam ident. lam ty.
      match pprintConName env ident with (env, ident) then
        let isUnit = match ty with TyRecord {fields = fields} then
          mapIsEmpty fields else false in
        if isUnit then
          (env, join ["| ", ident])
        else match getTypeStringCode indent env ty with (env, ty) then
          (env, join ["| ", ident, " of ", ty])
        else never
      else never
    in
    match pprintVarName env t.ident with (env, ident) then
      match mapMapAccum f env t.constrs with (env, constrs) then
        let constrs = strJoin (pprintNewline (pprintIncr indent))
                              (mapValues constrs) in
        (env, join ["type ", ident, " =", pprintNewline (pprintIncr indent),
                    constrs, ";;"])
      else never
    else never
  | OTopCExternalDecl t ->
    -- NOTE(larshum, 2022-03-10): Externals are declared before type
    -- definitions, so we cannot refer to them here. The below function
    -- produces a type string with the correct number of arguments, but
    -- otherwise unspecified types.
    recursive let objTypeString = lam ty.
      match ty with TyArrow {from = from, to = to} then
        join [objTypeString from, " -> ", objTypeString to]
      else "Obj.t" in
    match pprintVarName env t.ident with (env, ident) in
    let ty = objTypeString t.ty in
    (env, join ["external ", ident, " : ", ty, " = ",
                "\"", nameGetStr t.bytecodeIdent, "\" ",
                "\"", nameGetStr t.nativeIdent, "\";;"])
  | OTopLet t ->
    let indent = 0 in
    match pprintVarName env t.ident with (env, ident) then
      match pprintCode (pprintIncr indent) env t.body with (env, body) then
        (env, join ["let ", ident, " =", pprintNewline (pprintIncr indent),
                    body, ";;"])
      else never
    else never
  | OTopRecLets {bindings = bindings} ->
    let indent = 0 in
    let lname = lam env. lam bind : OCamlTopBinding.
      match pprintVarName env bind.ident with (env,str) then
        (env, str)
      else never in
    let lbody = lam env. lam bind : OCamlTopBinding.
      match pprintCode (pprintIncr (pprintIncr indent)) env bind.body
      with (env,str) then (env, str)
      else never in
    match mapAccumL lname env bindings with (env,idents) then
      match mapAccumL lbody env bindings with (env,bodies) then
        match bodies with [] then (env,"") else
          let fzip = lam ident. lam body.
            join [ident, " =",
                  pprintNewline (pprintIncr (pprintIncr indent)),
                  body]
          in
          (env,join ["let rec ",
                     strJoin (join [pprintNewline indent, "and "])
                     (zipWith fzip idents bodies), ";;"])
      else never
    else never
  | OTopExpr {expr = expr} ->
    let indent = 0 in
    match pprintCode indent env expr with (env, code) then
      (env, concat code ";;")
    else never
  | OTopTryWith {try = try, arms = arms} ->
    let i = pprintIncr 0 in
    let ii = pprintIncr i in
    let iii = pprintIncr ii in
    match pprintCode i env try with (env, try) in
    let pprintArm = lam env. lam arm. match arm with (pat, expr) then
      match getPatStringCode ii env pat with (env, pat) then
        match printParen iii env expr with (env, expr) then
          (env, join [pprintNewline i, "| ", pat, " ->", pprintNewline iii, expr])
        else never
      else never
    else never in
    match mapAccumL pprintArm env arms with (env, arms) then
      (env, join ["try", pprintNewline i, try, pprintNewline 0,
                  "with", join arms])
    else never


  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmVar {ident = ident} -> pprintVarName env ident
  | OTmVarExt {ident = ident} -> (env, ident)
  | OTmExprExt {expr = expr} -> (env, expr)
  | OTmConApp {ident = ident, args = []} -> pprintConName env ident
  | OTmConApp {ident = ident, args = [arg]} ->
    match pprintConName env ident with (env, ident) then
      match printParen indent env arg with (env, arg) then
        (env, join [ident, " ", arg])
      else never
    else never
  | OTmConApp {ident = ident, args = args} ->
    match pprintConName env ident with (env, ident) then
      match mapAccumL (pprintCode indent) env args with (env, args) then
        (env, join [ident, " (", strJoin ", " args, ")"])
      else never
    else never
  | OTmConAppExt {ident = ident, args = []} -> (env, ident)
  | OTmConAppExt {ident = ident, args = [arg]} ->
    match printParen indent env arg with (env, arg) then
      (env, join [ident, " ", arg])
    else never
  | OTmConAppExt {ident = ident, args = args} ->
    match mapAccumL (pprintCode indent) env args with (env, args) then
      (env, join [ident, " (", strJoin ", " args, ")"])
    else never
  | TmLam {ident = id, body = b} ->
    match pprintVarName env id with (env,str) then
      match pprintCode (pprintIncr indent) env b with (env,body) then
        (env,join ["fun ", str, " ->", pprintNewline (pprintIncr indent), body])
      else never
    else never
  | OTmLam {label = label, ident = id, body = b} ->
    match pprintVarName env id with (env,str) then
      let str =
        match label with Some label then join ["~", label, ":", str]
        else match label with None _ then str
        else never
      in
      match pprintCode (pprintIncr indent) env b with (env,body) then
        (env,join ["fun ", str, " ->", pprintNewline (pprintIncr indent), body])
      else never
    else never
  | TmLet t ->
    match pprintVarName env t.ident with (env,str) then
      match pprintCode (pprintIncr indent) env t.body with (env,body) then
        match pprintCode indent env t.inexpr with (env,inexpr) then
          (env,
           join ["let ", str, " =", pprintNewline (pprintIncr indent),
                 body, pprintNewline indent,
                 "in", pprintNewline indent,
                 inexpr])
        else never
      else never
    else never
  | TmRecord t ->
    if mapIsEmpty t.bindings then (env, "()")
    else
      let innerIndent = pprintIncr (pprintIncr indent) in
      let orderedLabels = recordOrderedLabels (mapKeys t.bindings) in
      match
        mapAccumL (lam env. lam k.
          let v = mapFindExn k t.bindings in
          match pprintCode innerIndent env v with (env, str) then
            (env, join [pprintLabelString k, " =", pprintNewline innerIndent,
                        "(", str, ")"])
          else never) env orderedLabels
      with (env, binds) then
        let merged =
          strJoin (concat ";" (pprintNewline (pprintIncr indent))) binds
        in
        (env, join ["{ ", merged, " }"])
      else never
  | TmRecordUpdate t ->
    let i = pprintIncr indent in
    let ii = pprintIncr i in
    match pprintCode i env t.rec with (env,rec) then
      match pprintCode ii env t.value with (env,value) then
        (env,join ["{ ", rec, pprintNewline i,
                   "with", pprintNewline i,
                   pprintLabelString t.key, " =", pprintNewline ii, value,
                   " }"])
      else never
    else never
  | OTmRecordUpdate {rec = rec, updates = updates} ->
    let i = pprintIncr indent in
    let ii = pprintIncr i in
    let pprintUpdate = lam env. lam update.
      match update with (key, value) in
      match pprintCode ii env value with (env, value) in
      (env, join [pprintLabelString key, " =", pprintNewline ii, value])
    in
    let pprintUpdates = lam env. lam updates.
      match mapAccumL pprintUpdate env updates with (env, updates) in
      (env, strJoin (concat ";" (pprintNewline i)) updates)
    in
    match pprintCode i env rec with (env, rec) in
    match pprintUpdates env updates with (env, updates) in
    (env, join ["{ ", rec, pprintNewline i,
                "with", pprintNewline i, updates, " }"])
  | TmRecLets {bindings = bindings, inexpr = inexpr} ->
    let lname = lam env. lam bind : RecLetBinding.
      match pprintVarName env bind.ident with (env,str) then
        (env, str)
      else never in
    let lbody = lam env. lam bind : RecLetBinding.
      match pprintCode (pprintIncr (pprintIncr indent)) env bind.body
      with (env,str) then (env, str)
      else never in
    match mapAccumL lname env bindings with (env,idents) then
      match mapAccumL lbody env bindings with (env,bodies) then
        match pprintCode indent env inexpr with (env,inexpr) then
        match bodies with [] then (env,inexpr) else
          let fzip = lam ident. lam body.
            join [ident, " =",
                  pprintNewline (pprintIncr (pprintIncr indent)),
                  body]
          in
          (env,join ["let rec ",
                     strJoin (join [pprintNewline indent, "and "])
                     (zipWith fzip idents bodies),
                     pprintNewline indent, "in ", inexpr])
        else never
      else never
    else never
  | OTmArray t ->
    match mapAccumL (lam env. lam tm. pprintCode (pprintIncr indent) env tm)
                    env t.tms
    with (env,tms) then
      let merged =
        strJoin (concat ";" (pprintNewline (pprintIncr indent)))
                (map (lam t. join ["(", t, ")"]) tms)
      in
      (env,join ["[| ", merged, " |]"])
    else never
  | OTmTuple {values = values} ->
    match mapAccumL (pprintCode indent) env values
    with (env, values) then
      (env, join ["(", strJoin ", " values, ")"])
    else never
  | OTmMatch {
    target = target,
    arms
      = [ (PatBool {val = true}, thn), (PatBool {val = false}, els) ]
      | [ (PatBool {val = false}, els), (PatBool {val = true}, thn) ]
    } ->
    let i = indent in
    let ii = pprintIncr i in
    match pprintCode ii env target with (env, target) then
      match pprintCode ii env thn with (env, thn) then
        match pprintCode ii env els with (env, els) then  -- NOTE(vipa, 2020-11-30): if we add sequential composition (`;`) this will be wrong, it should be `printParen` instead of `printCode`.
          (env, join ["if", pprintNewline ii,
                      target, pprintNewline i,
                      "then", pprintNewline ii,
                      thn, pprintNewline i,
                      "else", pprintNewline ii,
                      els])
        else never
      else never
    else never
  | OTmMatch { target = target, arms = [(pat, expr)] } ->
    let i = indent in
    let ii = pprintIncr i in
    match pprintCode ii env target with (env, target) then
      match getPatStringCode ii env pat with (env, pat) then
        match pprintCode i env expr with (env, expr) then  -- NOTE(vipa, 2020-11-30): the NOTE above with the same date does not apply here; `let` has lower precedence than `;`
          (env, join ["let", pprintNewline ii,
                      pat, pprintNewline i,
                      "=", pprintNewline ii,
                      target, pprintNewline i,
                      "in", pprintNewline i,
                      expr])
        else never
      else never
    else never
  | OTmMatch {target = target, arms = arms} ->
    let i = indent in
    let ii = pprintIncr i in
    let iii = pprintIncr ii in
    match pprintCode ii env target with (env, target) then
      let pprintArm = lam env. lam arm. match arm with (pat, expr) then
        match getPatStringCode ii env pat with (env, pat) then
          match printParen iii env expr with (env, expr) then
            (env, join [pprintNewline i, "| ", pat, " ->", pprintNewline iii, expr])
          else never
        else never
      else never in
      match mapAccumL pprintArm env arms with (env, arms) then
        (env, join ["match", pprintNewline ii, target, pprintNewline i,
                    "with", join arms])
      else never
    else never
  | OTmString t -> (env, join ["\"", t.text, "\""])
  | OTmLabel {label = label, arg = arg} ->
    match pprintCode indent env arg with (env, arg) then
      (env, join ["~", label, ":(", arg, ")"])
    else never
  | OTmRecord {bindings = bindings, tyident = tyident} ->
    let innerIndent = pprintIncr (pprintIncr indent) in
    match unzip bindings with (labels, tms) in
    match mapAccumL (pprintCode innerIndent) env tms with (env, tms) in
    let strs =
      mapi
        (lam i. lam t.
          join [get labels i, " =", pprintNewline innerIndent, "(", t, ")"])
        tms
    in
    match getTypeStringCode indent env tyident with (env, tystr) in
    let tystr =
      -- NOTE(larshum, 2022-04-06): Do not add type annotations for an inlined
      -- record.
      match tyident with OTyInlinedRecord _ then ""
      else concat " : " tystr
    in
    let merged =
      strJoin (concat ";" (pprintNewline (pprintIncr indent))) strs
    in
    (env, join ["({", merged , "}", tystr, ")"])
  | OTmProject {field = field, tm = tm} ->
    match pprintCode indent env tm with (env, tm) then
      (env, join [tm, ".", field])
    else never

  sem getPatStringCode (indent : Int) (env : PprintEnv) =
  | OPatRecord {bindings = bindings} ->
    let labels = map pprintLabelString (mapKeys bindings) in
    let pats = mapValues bindings in
    match mapAccumL (getPatStringCode indent) env pats with (env, pats) then
      let strs = mapi (lam i. lam p. join [get labels i, " = ", p]) pats in
      (env, join ["{", strJoin ";" strs, "}"])
    else never
  | OPatTuple {pats = pats} ->
    match mapAccumL (getPatStringCode indent) env pats with (env, pats) then
      (env, join ["(", strJoin ", " pats, ")"])
    else never
  | OPatCon {ident = ident, args = []} -> pprintConName env ident
  | OPatCon {ident = ident, args = [arg]} ->
    match pprintConName env ident with (env, ident) then
      match printPatParen indent 3 env arg with (env, arg) then
        (env, join [ident, " ", arg])
      else never
    else never
  | OPatCon {ident = ident, args = args} ->
    match pprintConName env ident with (env, ident) then
      match mapAccumL (getPatStringCode indent) env args with (env, args) then
        (env, join [ident, " (", strJoin ", " args, ")"])
      else never
    else never
  | OPatConExt {ident = ident, args = []} -> (env, ident)
  | OPatConExt {ident = ident, args = [arg]} ->
    match printPatParen indent 3 env arg with (env, arg) then
      (env, join [ident, " ", arg])
    else never
  | OPatConExt {ident = ident, args = args} ->
    match mapAccumL (getPatStringCode indent) env args with (env, args) then
      (env, join [ident, " (", strJoin ", " args, ")"])
    else never
end

lang TestLang = OCamlPrettyPrint + OCamlSym
end

mexpr
use TestLang in

let debugPrint = false in

let pprintProg = lam ast.
  if debugPrint then
    print "\n\n";
    print (expr2str (symbolize ast))
  else ()
in

let testAddInt1 = addi_ (int_ 1) (int_ 2) in

let testAddInt2 = addi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in

let testMulInt = muli_ (int_ 2) (int_ 3) in

let testModInt = modi_ (int_ 2) (int_ 3) in

let testDivInt = divi_ (int_ 2) (int_ 3) in

let testNegInt = negi_ (int_ 2) in

let testAddFloat1 = addf_ (float_ 1.) (float_ 2.) in

let testAddFloat2 = addf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in

let testNegFloat = negf_ (float_ 1.) in

let testCompareInt1 = eqi_ (int_ 1) (int_ 2) in

let testCompareInt2 = lti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in

let testCompareFloat1 = eqf_ (float_ 1.) (float_ 2.) in

let testCompareFloat2 =
  lti_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.)
in

let testCharLiteral = char_ 'c' in

let testFun = ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))) in

let testLet =
  bindall_ [ulet_ "x" (int_ 1), addi_ (var_ "x") (int_ 2)]
in

let testRec =
  bind_
    (ureclets_add "foo" (ulam_ "x" (app_ (var_ "foo") (var_ "x")))
      reclets_empty)
    (app_ (var_ "foo") (int_ 1))
in

let testMutRec =
  bind_
    (ureclets_add "foo" (ulam_ "x" (app_ (var_ "bar") (var_ "x")))
      (ureclets_add "bar" (ulam_ "x" (app_ (var_ "foo") (var_ "x")))
         reclets_empty))
    (app_ (var_ "foo") (int_ 1))
in

-- Test identifier escapingvar

-- Abstractions
let testLamEscape = (ulam_ "ABC123" (ulam_ "'a/b/c" (app_ (var_ "ABC123")
                                                          (var_ "'a/b/c"))))
in

-- Lets
let testLetEscape = bind_ (ulet_ "abcABC/:@_'" (int_ 1)) (var_ "abcABC/:@_'") in

let testRecEscape =
  bind_
    (ureclets_add "abcABC/:@_'" (ulam_ "ABC123"
                               (app_ (var_ "abcABC/:@_'")
                                     (var_ "ABC123")))
      reclets_empty)
    (app_ (var_ "abcABC/:@_'") (int_ 1))
in

let testMutRecEscape =
  bind_
    (ureclets_add "'a/b/c" (ulam_ "" (app_ (var_ "123") (var_ "")))
      (ureclets_add "123" (ulam_ "" (app_ (var_ "'a/b/c") (var_ "")))
         reclets_empty))
    (app_ (var_ "'a/b/c") (int_ 1))
in

let testMatchSimple =
  let armA = (pvar_ "a", var_ "a") in
  let armB = (pvarw_, int_ 3) in
  OTmMatch {target = true_, arms = [armA, armB]}
in

let testMatchNested =
  let armA = (pvar_ "a", var_ "a") in
  let armB = (pvarw_, var_ "b") in
  let inner = OTmMatch {target = true_, arms = [armA]} in
  let armB = (pvar_ "b", inner) in
  let armC = (pvar_ "c", false_) in
  OTmMatch {target = true_, arms = [armB, armC]}
in

let testIf =
  OTmMatch {target = true_, arms = [(ptrue_, true_), (pfalse_, false_)]}
in

let testIfNested =
  let t = lam v. OTmMatch {target = true_, arms = [(ptrue_, v true_), (pfalse_, v false_)]} in
  OTmMatch {target = true_, arms = [(pfalse_, t (lam x. addi_ false_ x)), (ptrue_, t (lam x. addi_ true_ x))]}
in

let testPatLet =
  OTmMatch {target = true_, arms = [(pvar_ "a", var_ "a")]}
in

let testTuple =
  OTmMatch
  { target = OTmTuple {values = [true_, false_]}
  , arms = [(OPatTuple {pats = [pvar_ "a", pvar_ "b"]}, OTmTuple {values = [var_ "b", var_ "a"]})]}
in

let testLabel =
  OTmLabel { label = "label", arg = int_ 0}
in

let testRecord =
  OTmRecord {
    bindings = [("a", int_ 1), ("b", float_ 2.)],
    tyident = otyvarext_ "rec" []
  }
in

let testProject =
  OTmProject { field = "a", tm = OTmVarExt { ident = "r" } }
in

let asts = [
  testAddInt1,
  testAddInt2,
  testMulInt,
  testModInt,
  testDivInt,
  testNegInt,
  testAddFloat1,
  testAddFloat2,
  testNegFloat,
  testCompareInt1,
  testCompareInt2,
  testCompareFloat1,
  testCompareFloat2,
  testCharLiteral,
  testFun,
  testLet,
  testRec,
  testMutRec,
  testLamEscape,
  testLetEscape,
  testRecEscape,
  testMutRecEscape,
  testMatchSimple,
  testMatchNested,
  testIf,
  testIfNested,
  testPatLet,
  testTuple,
  testLabel,
  testRecord,
  testProject
] in

map pprintProg asts;

()
