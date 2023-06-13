/-

NOTE(vipa, 2023-07-03): Known sharp edges in the current
implementation:

- Operation declarations must be written in an `.mc` file, as a `let`
  with a non-`Unknown` type annotation, and a body that is exactly
  `never`.
  - Operation implementations must be written in an `.imc` file, and
    will be inserted in the mexpr AST each time an operation
    declaration is encountered with the same string identifier.
- Repr declarations must be written in an `.imc` file. *All* repr
  declarations are inserted right before the first operation
  declaration encountered in the mexpr AST.

These things roughly mean two things:

- Everything referred to by an op implementation or repr declaration
  must be declared before the first op declaration.
- References from op impls to other operations are limited: they must
  follow the order the operations are declared in the mexpr AST;
  operations may only reference operations declared strictly *before*
  themselves.

-/

include "ast.mc"
include "cmp.mc"
include "keyword-maker.mc"
include "type-check.mc"
include "type.mc"
include "universal-implementation.mc"
include "const-transformer.mc"
include "builtin.mc"
include "eval.mc"
include "cp/high-level.mc"
include "mexpr/annotate.mc"

lang AnnotateSimple = HtmlAnnotator + AnnotateSources
end

lang UCTKeywordMaker = KeywordMakerBase + CollTypeAst + TyWildAst + OpDeclAst
  sem matchTypeKeywordString info =
  | "_" ->
    let mk = lam. TyWild {info = info} in
    Some (0, mk)
  | "Coll" ->
    let mk = lam args. match args with [filter, permutation, element] in TyColl
      { info = info
      , filter = filter
      , permutation = permutation
      , element = element
      , repr = ref (UninitRepr ())
      , explicitSubst = None ()
      } in
    Some (3, mk)

  sem isTypeKeyword =
  | TyColl _ -> true

  -- TODO(vipa, 2022-09-26): This is a bit hacky, but is probably a
  -- reasonable first version
  sem makeExprKeywords args =
  -- TODO(vipa, 2022-09-26): Make a more thorough check that the
  -- annotated signature is reasonable?
  | TmLet (x & {body = TmNever _, tyAnnot = !TyUnknown _}) -> TmOpDecl
    { info = x.info
    , ident = x.ident
    , tyAnnot = makeTypeKeywords [] x.tyAnnot
    , ty = x.ty
    , inexpr = makeExprKeywords [] x.inexpr
    }
end

lang TyWildPrettyPrint = PrettyPrint + TyWildAst
  sem typePrecedence =
  | TyWild _ -> 0

  sem getTypeStringCode indent env =
  | TyWild _ -> (env, "_")
end

lang CollTypePrettyPrint = PrettyPrint + CollTypeAst + UCTHelpers
  sem typePrecedence =
  | TyColl _ -> 1

  sem getTypeStringCode indent env =
  | TyColl x ->
    let repr = switch deref (botRepr x.repr)
      case BotRepr repr then join [int2string repr.scope, ", ", int2string (sym2hash repr.sym)]
      case UninitRepr _ then "uninit"
      case _ then "impossible"
      end in
    match
      match x.explicitSubst with Some n then
        match pprintEnvGetStr env n with (env, n) in
        (env, cons '!' n)
      else (env, "")
    with (env, subst) in
    match printTypeParen indent 2 env x.filter with (env, filter) in
    match printTypeParen indent 2 env x.permutation with (env, permutation) in
    match printTypeParen indent 2 env x.element with (env, element) in
    (env, join ["Coll[", repr, "]", subst, " ", filter, " ", permutation, " ", element])
end

lang OpDeclPrettyPrint = PrettyPrint + OpDeclAst
  sem isAtomic =
  | TmOpDecl _ -> false

  sem pprintCode indent env =
  | TmOpDecl x ->
    match pprintEnvGetStr env x.ident with (env, ident) in
    match pprintCode indent env x.inexpr with (env, inexpr) in
    match getTypeStringCode indent env x.tyAnnot with (env, ty) in
    (env,
     join ["opdecl ", pprintVarString ident, " : ", ty, " in",
           pprintNewline indent, inexpr])
end

lang OpVarPrettyPrint = PrettyPrint + OpVarAst
  sem isAtomic =
  | TmOpVar _ -> true

  sem pprintCode indent env =
  | TmOpVar x ->
    match pprintEnvGetStr env x.ident with (env, ident) in
    (env, join ["<Op>", ident])
end

lang OpImplPrettyPrint = PrettyPrint + OpImplAst
  sem isAtomic =
  | TmOpImpl _ -> false

  sem pprintCode indent env =
  | TmOpImpl x ->
    let newIndent = pprintIncr indent in
    let pprintAlt = lam env. lam alt.
      match getTypeStringCode newIndent env alt.specType with (env, specType) in
      match pprintCode newIndent env alt.body with (env, body) in
      (env, join [specType, pprintNewline newIndent, body]) in
    match pprintEnvGetStr env x.ident with (env, ident) in
    match mapAccumL pprintAlt env x.alternatives with (env, alternatives) in
    match pprintCode indent env x.inexpr with (env, inexpr) in
    let start = concat (pprintNewline indent) "* " in
    let str = join
      [ "impl[", int2string x.reprScope, "] ", ident, " ="
      , join (map (lam alt. concat start alt) alternatives)
      , pprintNewline indent, "in"
      , pprintNewline indent, inexpr
      ] in
    (env, str)
end

lang ReprDeclPrettyPrint = PrettyPrint + ReprDeclAst
  sem isAtomic =
  | TmReprDecl _ -> false

  sem pprintCode indent env =
  | TmReprDecl x ->
    match pprintEnvGetStr env x.ident with (env, ident) in
    match getTypeStringCode indent env x.pat with (env, pat) in
    match getTypeStringCode indent env x.repr with (env, repr) in
    match pprintCode indent env x.inexpr with (env, inexpr) in
    let str = join
      [ "repr ", ident, " {", pat, " = ", repr, "} in"
      , pprintNewline indent, inexpr
      ] in
    (env, str)
end

lang ConvertToMExpr = Ast + UniversalImplementationBaseAst
  sem convertToMExpr : Merged -> Expr
  sem convertToMExpr =
  | m -> errorSingle [get_Merged_info m] "This syntax isn't valid in an expression context"
  sem convertToMExprTy : Merged -> Type
  sem convertToMExprTy =
  | m -> errorSingle [get_Merged_info m] "This syntax isn't valid in a type context"
  sem convertToMExprPat : Merged -> Pat
  sem convertToMExprPat =
  | m -> errorSingle [get_Merged_info m] "This syntax isn't valid in a pattern context"
end

lang ConvertLam = ConvertToMExpr + LamMergedAst + LamAst
  sem convertToMExpr =
  | LamMerged x -> TmLam
    { info = x.info
    , ident = optionMapOr (nameNoSym "") (lam x. x.v) x.v
    , tyAnnot = optionMapOr tyunknown_ convertToMExprTy x.ty
    , tyParam = tyunknown_
    , body = convertToMExpr x.right
    , ty = tyunknown_
    }
end

lang ConvertIf = ConvertToMExpr + IfMergedAst + MatchAst + BoolPat
 sem convertToMExpr =
 | IfMerged x -> TmMatch
   { target = convertToMExpr x.c
   , pat = PatBool {info = get_Merged_info x.c, val = true, ty = tyunknown_}
   , thn = convertToMExpr x.t
   , els = convertToMExpr x.e
   , ty = tyunknown_
   , info = x.info
   }
end

lang ConvertBoolCon = ConvertToMExpr + BoolConMergedAst + BoolTypeAst
  sem convertToMExprTy =
  | BoolConMerged x -> TyBool {info = x.info}
end

lang ConvertIntCon = ConvertToMExpr + IntConMergedAst + IntTypeAst
  sem convertToMExprTy =
  | IntConMerged x -> TyInt {info = x.info}
end

lang ConvertCharCon = ConvertToMExpr + CharConMergedAst + CharTypeAst
  sem convertToMExprTy =
  | CharConMerged x -> TyChar {info = x.info}
end

lang ConvertFloatCon = ConvertToMExpr + FloatConMergedAst + FloatTypeAst
  sem convertToMExprTy =
  | FloatConMerged x -> TyFloat {info = x.info}
end

lang ConvertUnknownCon = ConvertToMExpr + UnknownConMergedAst + UnknownTypeAst
  sem convertToMExprTy =
  | UnknownConMerged x -> TyUnknown {info = x.info}
end

lang ConvertProj = ConvertToMExpr + ProjMergedAst + MatchAst + RecordPat
  sem convertToMExpr =
  | ProjMerged x ->
    let n = nameSym "x" in
    let pat = withInfoPat x.info
      (match x.label with Some l then
         prec_ [(l.v, npvar_ n)]
       else match x.idx with Some idx then
         prec_ [(int2string idx.v, npvar_ n)]
       else never) in
    TmMatch
    { target = convertToMExpr x.left
    , pat = pat
    , thn = withInfo x.info (nvar_ n)
    , els = withInfo x.info never_
    , ty = tyunknown_
    , info = x.info
    }
end

lang ConvertTuple = ConvertToMExpr + TupleMergedAst + RecordAst + RecordTypeAst + RecordPat
  sem convertToMExpr =
  | TupleMerged x -> TmRecord
    { info = x.info
    , ty = tyunknown_
    , bindings = mapFromSeq cmpSID
      (mapi (lam i. lam e. (stringToSid (int2string i), convertToMExpr e)) x.e)
    }

  sem convertToMExprTy =
  | TupleMerged x -> TyRecord
    { info = x.info
    , fields = mapFromSeq cmpSID
      (mapi (lam i. lam e. (stringToSid (int2string i), convertToMExprTy e)) x.e)
    }

  sem convertToMExprPat =
  | TupleMerged x -> PatRecord
    { info = x.info
    , bindings = mapFromSeq cmpSID
      (mapi (lam i. lam e. (stringToSid (int2string i), convertToMExprPat e)) x.e)
    , ty = tyunknown_
    }
end

lang ConvertArrow = ConvertToMExpr + ArrowMergedAst + FunTypeAst
  sem convertToMExprTy =
  | ArrowMerged x -> TyArrow
    { info = x.info
    , from = convertToMExprTy x.left
    , to = convertToMExprTy x.right
    }
end

lang ConvertSemi = ConvertToMExpr + SemiMergedAst
  sem convertToMExpr =
  | SemiMerged x ->
    withInfo x.info (semi_ (convertToMExpr x.left) (convertToMExpr x.right))
end

lang ConvertApp = ConvertToMExpr + AppMergedAst + AppAst + AppTypeAst
  sem convertToMExpr =
  | AppMerged x -> TmApp
    { lhs = convertToMExpr x.left
    , rhs = convertToMExpr x.right
    , ty = tyunknown_
    , info = x.info
    }

  sem convertToMExprTy =
  | AppMerged x -> TyApp
    { lhs = convertToMExprTy x.left
    , rhs = convertToMExprTy x.right
    , info = x.info
    }

  sem convertToMExprPat =
  | AppMerged x -> errorSingle [x.info] "Invalid application in pattern context"
end

lang ConvertTypeDef = ConvertToMExpr + TypeMergedAst + TypeAst + VariantTypeAst
  sem convertToMExpr =
  | TypeMerged x -> TmType
    { ident = x.v.v
    , params = map (lam x. x.v) x.args
    , tyIdent = match x.ty with Some ty
      then convertToMExprTy ty
      else TyVariant {info = x.info, constrs = mapEmpty nameCmp}
    , info = x.info
    , ty = tyunknown_
    , inexpr = convertToMExpr x.right
    }
end

lang ConvertConDef = ConvertToMExpr + ConDefMergedAst + DataAst
  sem convertToMExpr =
  | ConDefMerged x -> TmConDef
    { ident = x.v.v
    , tyIdent = convertToMExprTy x.ty
    , inexpr = convertToMExpr x.right
    , ty = tyunknown_
    , info = x.info
    }
end

lang ConvertCon = ConvertToMExpr + ConMergedAst + AppMergedAst + DataAst + ConTypeAst + DataPat
  sem convertToMExpr =
  | AppMerged (x & {left = ConMerged c}) ->
    TmConApp { ident = c.c.v, body = convertToMExpr x.right, ty = tyunknown_, info = x.info }
  | ConMerged c -> errorSingle [c.info] "Unapplied constructor"

  sem convertToMExprTy =
  | ConMerged c -> TyCon
    { ident = c.c.v
    , info = c.info
    }

  sem convertToMExprPat =
  | AppMerged (x & {left = ConMerged c}) -> PatCon
    { ident = c.c.v
    , subpat = convertToMExprPat x.right
    , ty = tyunknown_
    , info = x.info
    }
  | ConMerged c -> errorSingle [c.info] "Unapplied constructor"
end

lang ConvertWild = ConvertToMExpr + WildMergedAst + TyWildAst + NamedPat
  sem convertToMExprTy =
  | WildMerged x -> TyWild {info = x.info}

  sem convertToMExprPat =
  | WildMerged x -> PatNamed {ident = PWildcard (), info = x.info, ty = tyunknown_}
end

lang ConvertColl = ConvertToMExpr + CollTypeAst + CollMergedAst + NotMergedAst + AppMergedAst + ConMergedAst
  sem convertToMExprTy =
  | AppMerged
    { left = AppMerged
      { left = AppMerged
        { left = CollMerged x
        , right = pred
        }
      , right = perm
      }
    , right = elem
    , info = overallInfo
    } ->
    TyColl
    { info = overallInfo
    , filter = convertToMExprTy pred
    , permutation = convertToMExprTy perm
    , element = convertToMExprTy elem
    , repr = ref (UninitRepr ())
    , explicitSubst = None ()
    }
  | AppMerged
    { left = AppMerged
      { left = AppMerged
        { left = AppMerged
          { left = CollMerged x
          , right = NotMerged {right = ConMerged {c = {v = subst}}}
          }
        , right = pred
        }
      , right = perm
      }
    , right = elem
    , info = overallInfo
    } ->
    TyColl
    { info = overallInfo
    , filter = convertToMExprTy pred
    , permutation = convertToMExprTy perm
    , element = convertToMExprTy elem
    , repr = ref (UninitRepr ())
    , explicitSubst = Some subst
    }
  | CollMerged x -> errorSingle [x.info] "A Coll takes an optional substitution and three type arguments."
end

lang ConvertVar = ConvertToMExpr + VarMergedAst + VarAst + VarTypeAst + NamedPat
  sem convertToMExpr =
  | VarMerged x -> TmVar {ident = x.v.v, ty = tyunknown_, info = x.info, frozen = false}
  sem convertToMExprTy =
  | VarMerged x -> TyVar {ident = x.v.v, info = x.info}
  sem convertToMExprPat =
  | VarMerged x -> PatNamed {ident = PName x.v.v, info = x.info, ty = tyunknown_}
end

lang ConvertFrozenVar = ConvertToMExpr + FrozenVarMergedAst + VarAst
  sem convertToMExpr =
  | FrozenVarMerged x -> TmVar {ident = x.v.v, ty = tyunknown_, info = x.info, frozen = true}
end

lang ConvertChar = ConvertToMExpr + CharMergedAst + CharAst + CharPat
  sem convertToMExpr =
  | CharMerged x -> TmConst {val = CChar {val = x.v.v}, ty = tyunknown_, info = x.info}
  sem convertToMExprPat =
  | CharMerged x -> PatChar {val = x.v.v, ty = tyunknown_, info = x.info}
end

lang ConvertInt = ConvertToMExpr + IntMergedAst + IntAst + IntPat
  sem convertToMExpr =
  | IntMerged x -> TmConst {val = CInt {val = x.v.v}, ty = tyunknown_, info = x.info}
  sem convertToMExprPat =
  | IntMerged x -> PatInt {val = x.v.v, ty = tyunknown_, info = x.info}
end

lang ConvertFloat = ConvertToMExpr + FloatMergedAst + FloatAst
  sem convertToMExpr =
  | FloatMerged x -> TmConst {info = x.info, val = CFloat {val = x.v.v}, ty = tyunknown_}
end

lang ConvertTrue = ConvertToMExpr + TrueMergedAst + BoolAst + BoolPat
  sem convertToMExpr =
  | TrueMerged x -> TmConst {info = x.info, val = CBool {val = true}, ty = tyunknown_}
  sem convertToMExprPat =
  | TrueMerged x -> PatBool {val = true, ty = tyunknown_, info = x.info}
end

lang ConvertFalse = ConvertToMExpr + FalseMergedAst + BoolAst + BoolPat
  sem convertToMExpr =
  | FalseMerged x -> TmConst {info = x.info, val = CBool {val = false}, ty = tyunknown_}
  sem convertToMExprPat =
  | FalseMerged x -> PatBool {val = false, ty = tyunknown_, info = x.info}
end

lang ConvertNever = ConvertToMExpr + NeverMergedAst + NeverAst
  sem convertToMExpr =
  | NeverMerged x -> TmNever {info = x.info, ty = tyunknown_}
end

lang ConvertString = ConvertToMExpr + StringMergedAst + SeqAst + CharAst
  sem convertToMExpr =
  | StringMerged x -> errorSingle [x.info] "Conversion not supported yet"
end

lang ConvertSequence = ConvertToMExpr + SequenceMergedAst + SeqAst
  sem convertToMExpr =
  | SequenceMerged x -> errorSingle [x.info] "Conversion not supported yet"
end

lang ConvertRecord = ConvertToMExpr + RecordMergedAst + RecordAst
  sem convertToMExpr =
  | RecordMerged x -> errorSingle [x.info] "Conversion not supported yet"
end

lang ConvertNotPat = ConvertToMExpr + NotMergedAst + NotPat
  sem convertToMExprPat =
  | NotMerged x -> errorSingle [x.info] "Conversion not supported yet"
end

lang ConvertOrPat = ConvertToMExpr + OrMergedAst + OrPat
  sem convertToMExprPat =
  | OrMerged x -> errorSingle [x.info] "Conversion not supported yet"
end

lang ConvertAndPat = ConvertToMExpr + AndMergedAst + AndPat
  sem convertToMExprPat =
  | AndMerged x -> errorSingle [x.info] "Conversion not supported yet"
end

lang ConvertConcatPat = ConvertToMExpr + ConcatMergedAst + SeqEdgePat
  sem convertToMExprPat =
  | ConcatMerged x -> errorSingle [x.info] "Conversion not supported yet"
end

lang MExprConvertImpl = ConvertConcatPat + ConvertAndPat + ConvertOrPat + ConvertNotPat + ConvertRecord + ConvertSequence + ConvertString + ConvertNever + ConvertFalse + ConvertTrue + ConvertFloat + ConvertInt + ConvertChar + ConvertFrozenVar + ConvertVar + ConvertCon + ConvertConDef + ConvertTypeDef + ConvertApp + ConvertSemi + ConvertProj + ConvertWild + ConvertColl + ConvertArrow + ConvertTuple + ConvertUnknownCon + ConvertFloatCon + ConvertCharCon + ConvertIntCon + ConvertBoolCon + ConvertLam + ConvertIf
end

lang UCTPrettyPrint = TyWildPrettyPrint + CollTypePrettyPrint + OpDeclPrettyPrint + OpVarPrettyPrint + OpImplPrettyPrint + ReprDeclPrettyPrint
end

lang EvalCost = ConstTransformer + IntAst + FloatAst + Eval + ConvertToMExpr
  sem _evalCost : Merged -> OpCost
  sem _evalCost = | tm ->
    let tm = convertToMExpr tm in
    let tm = constTransform builtin tm in
    let ctx = evalCtxEmpty () in
    -- TODO(vipa, 2023-05-02): Name hygiene, symbolize over all of an imc file in general
    let ctx = {ctx with env = evalEnvInsert (nameNoSym "n") (float_ 100.0) ctx.env} in
    switch eval ctx tm
    case TmConst {val = CFloat f} then f.val
    case TmConst {val = CInt i} then int2float i.val
    case _ then errorSingle [infoTm tm] "This expression did not evaluate to a number."
    end
end

lang CollectImpls = ConvertToMExpr + UniversalImplementationAst + EvalCost + OpVarAst
  sem collectImpls : String -> ImplData
  sem collectImpls = | filename ->
    match parseUniversalImplementationExn filename (readFile filename) with TopsUFile {tops=tops} in
    let f = lam acc. lam top.
      switch top
      case ImplDeclUTop x then
        let selfCost = _evalCost x.cost in
        let body = convertToMExpr x.body in
        let specType = optionMapOr tyunknown_ convertToMExprTy x.tyAnnot in
        let impl =
          { selfCost = selfCost
          , body = body
          , specType = specType
          } in
        { acc with impls = mapInsertWith concat (stringToSid (nameGetStr x.name.v))
          [impl]
          acc.impls
        }
      case ReprDeclUTop x then
        recursive let replaceMetaVars = lam acc. lam m.
          match m with MetaVarMerged x then
            match
              match mapLookup (nameGetStr x.var.v) acc with Some name then (acc, name) else
              let name = nameSetNewSym x.var.v in
              (mapInsert (nameGetStr name) name acc, name)
            with (acc, name) in
            (acc, VarMerged {info = x.info, v = {v = name, i = x.var.i}})
          else
            smapAccumL_Merged_Merged replaceMetaVars acc m in
        match replaceMetaVars (mapEmpty cmpString) x.pat with (vars, pat) in
        match replaceMetaVars vars x.repr with (vars, repr) in
        let repr =
          { vars = mapValues vars
          , pat = convertToMExprTy pat
          , repr = convertToMExprTy repr
          } in
        { acc with reprs = mapInsert x.name.v repr acc.reprs }
      end
    in foldl f emptyImplData tops
end

lang LamUCTAnalysis = TypeCheck + LamAst + SubstituteNewReprs
  sem typeCheckExpr env =
  | TmLam t ->
    let tyParam = substituteNewReprs env t.tyParam in
    let body = typeCheckExpr (_insertVar t.ident tyParam env) t.body in
    let tyLam = ityarrow_ t.info tyParam (tyTm body) in
    TmLam {t with body = body, tyParam = tyParam, ty = tyLam}
end

lang LetUCTAnalysis = TypeCheck + LetAst + SubstituteNewReprs + OpImplAst + OpDeclAst + IsValue + MetaVarDisableGeneralize
  sem typeCheckExpr env =
  | TmLet t ->
    let newLvl = addi 1 env.currentLvl in
    let isValue = isValue (GVal ()) t.body in
    let shouldBeOp = if isValue then containsColl t.tyBody else false in
    if shouldBeOp then
      -- Replace with an OpDecl and OpImpl
      match withNewReprScope env (lam env.
        let tyBody = substituteNewReprs env t.tyBody in
        match stripTyAll tyBody with (vars, stripped) in
        let newTyVars = foldr (lam v. mapInsert v.0 newLvl) env.tyVarEnv vars in
        let env = {env with currentLvl = newLvl, tyVarEnv = newTyVars} in
        let body = typeCheckExpr env t.body in
        unify env [infoTm body] stripped (tyTm body);
        (body, tyBody))
      with ((body, tyBody), reprScope, delayedReprUnifications) in
      (if env.disableRecordPolymorphism then
        disableRecordGeneralize env.currentLvl tyBody else ());
      match gen env.currentLvl (mapEmpty nameCmp) tyBody with (tyBody, _) in
      let env = _insertVar t.ident tyBody env in
      let env = {env with uct = {env.uct with opNamesInScope = mapInsert t.ident (None ()) env.uct.opNamesInScope}} in
      let inexpr = typeCheckExpr env t.inexpr in
      let ty = tyTm inexpr in
      TmOpDecl
      { info = t.info
      , ident = t.ident
      , tyAnnot = tyBody
      , ty = ty
      , inexpr = TmOpImpl
        { ident = t.ident
        , alternatives =
          [ { selfCost = 1.0
            , body = body
            , specType = tyBody
            , delayedReprUnifications = delayedReprUnifications  -- TODO(vipa, 2023-06-15): see if these can be simplified (transitivity, duplicates)
            }
          ]
        , inexpr = inexpr
        , ty = ty
        , reprScope = reprScope
        , info = t.info
        }
      }
    else
      -- Keep it as a Let in the current reprScope, use normal inference
      let tyBody = substituteNewReprs env t.tyBody in
      -- NOTE(vipa, 2023-06-26): this is slightly changed from actual
      -- normal inference, because it uses the type set in `tyBody`
      -- and does not touch `tyAnnot`.
      match
        if isValue then
          match stripTyAll tyBody with (vars, stripped) in
          let newTyVars = foldr (lam v. mapInsert v.0 newLvl) env.tyVarEnv vars in
          let newEnv = {env with currentLvl = newLvl, tyVarEnv = newTyVars} in
          let body = typeCheckExpr newEnv t.body in
          -- Unify the annotated type with the inferred one and generalize
          unify newEnv [infoTy t.tyAnnot, infoTm body] stripped (tyTm body);
          (if env.disableRecordPolymorphism then
            disableRecordGeneralize env.currentLvl tyBody else ());
          match gen env.currentLvl (mapEmpty nameCmp) tyBody with (tyBody, _) in
          (body, tyBody)
        else
          let body = typeCheckExpr {env with currentLvl = newLvl} t.body in
          unify env [infoTm body] tyBody (tyTm body);
          -- TODO(aathn, 2023-05-07): Relax value restriction
          weakenMetaVars env.currentLvl tyBody;
          (body, tyBody)
        with (body, tyBody) in
      let inexpr = typeCheckExpr (_insertVar t.ident tyBody env) t.inexpr in
      TmLet {t with body = body,
                    tyBody = tyBody,
                    inexpr = inexpr,
                    ty = tyTm inexpr}
end

lang RecLetsUCTAnalysis = TypeCheck + RecLetsAst + MetaVarDisableGeneralize + RecordAst + OpImplAst + OpDeclAst + UCTHelpers + IsValue + SubstituteNewReprs
  sem typeCheckExpr env =
  | TmRecLets t ->
    let typeCheckRecLets = lam env. lam t.
      let newLvl = addi 1 env.currentLvl in
      -- Build env with the recursive bindings
      let recLetEnvIteratee = lam acc. lam b: RecLetBinding.
        let tyBody = substituteNewReprs env b.tyBody in
        let vars = if isValue (GVal ()) b.body then (stripTyAll tyBody).0 else [] in
        let newEnv = _insertVar b.ident tyBody acc.0 in
        let newTyVars = foldr (uncurry mapInsert) acc.1 vars in
        ((newEnv, newTyVars), {b with tyBody = tyBody}) in
      match mapAccumL recLetEnvIteratee (env, mapEmpty nameCmp) t.bindings
        with ((recLetEnv, tyVars), bindings) in
      let newTyVarEnv = mapFoldWithKey
        (lam vs. lam v. lam. mapInsert v newLvl vs)
        recLetEnv.tyVarEnv
        tyVars in

      -- Type check each body
      let typeCheckBinding = lam b: RecLetBinding.
        let body =
          if isValue (GVal ()) b.body then
            let newEnv = {recLetEnv with currentLvl = newLvl, tyVarEnv = newTyVarEnv} in
            match stripTyAll b.tyBody with (_, stripped) in
            let body = typeCheckExpr newEnv b.body in
            -- Unify the inferred type of the body with the annotated one
            unify newEnv [infoTy b.tyAnnot, infoTm body] stripped (tyTm body);
            body
          else
            let body = typeCheckExpr {recLetEnv with currentLvl = newLvl} b.body in
            unify recLetEnv [infoTy b.tyAnnot, infoTm body] b.tyBody (tyTm body);
            body
        in {b with body = body} in
      let bindings = map typeCheckBinding bindings in

      -- Build env with generalized types
      let envIteratee = lam acc. lam b : RecLetBinding.
        match
          if isValue (GVal ()) b.body then
            (if env.disableRecordPolymorphism then
              disableRecordGeneralize env.currentLvl b.tyBody else ());
            gen env.currentLvl acc.1 b.tyBody
          else
            weakenMetaVars env.currentLvl b.tyBody;
            (b.tyBody, [])
          with (tyBody, vars) in
        let newEnv = _insertVar b.ident tyBody acc.0 in
        let newTyVars = foldr (uncurry mapInsert) acc.1 vars in
        ((newEnv, newTyVars), {b with tyBody = tyBody}) in
      match mapAccumL envIteratee (env, tyVars) bindings
        with ((env, _), bindings) in

      let inexpr = typeCheckExpr env t.inexpr in
      { t with bindings = bindings
             , inexpr = inexpr
             , ty = tyTm inexpr
      }
    in

    let shouldBeOp =
      if forAll (lam b. isValue (GVal ()) b.body) t.bindings
      then any (lam b. containsColl b.tyBody) t.bindings
      else false in
    if not shouldBeOp then TmRecLets (typeCheckRecLets env t) else
    let bindingToBindingPair = lam b.
      ( stringToSid (nameGetStr b.ident)
      , TmVar
        { ident = b.ident
        , ty = tyunknown_
        , info = t.info
        , frozen = true
        }
      ) in
    let opRecord = TmRecord
      { bindings = mapFromSeq cmpSID (map bindingToBindingPair t.bindings)
      , ty = tyunknown_
      , info = t.info
      } in
    match withNewReprScope env (lam env. typeCheckRecLets env {t with inexpr = opRecord})
      with (newT, reprScope, delayedReprUnifications) in
    let recordName =
      let ident = (head newT.bindings).ident in
      nameSym (concat (nameGetStr ident) "_etc") in
    let inexpr =
      let opNamesInScope = foldl
        (lam acc. lam b. mapInsert b.ident (Some (recordName, stringToSid (nameGetStr b.ident))) acc)
        env.uct.opNamesInScope
        newT.bindings in
      let opNamesInScope = mapInsert recordName (None ()) opNamesInScope in
      let env = _insertVar recordName newT.ty env in
      let env = {env with uct = {env.uct with opNamesInScope = opNamesInScope}} in
      typeCheckExpr env t.inexpr in
    let ty = tyTm inexpr in
    TmOpDecl
    { info = t.info
    , ident = recordName
    , tyAnnot = newT.ty
    , ty = ty
    , inexpr = TmOpImpl
      { ident = recordName
      , alternatives =
        [ { selfCost = 1.0
          , body = TmRecLets newT
          , specType = newT.ty
          , delayedReprUnifications = delayedReprUnifications
          }
        ]
      , inexpr = inexpr
      , ty = ty
      , reprScope = reprScope
      , info = t.info
      }
    }
end

lang VarUCTAnalysis = TypeCheck + VarAst + OpVarAst + UCTHelpers + SubstituteNewReprs + NeverAst + MatchAst + NamedPat + RecordPat
  sem typeCheckExpr env =
  | TmVar t ->
    let opInfo = mapLookup t.ident env.uct.opNamesInScope in
    match opInfo with Some (Some (rName, label)) then
      -- NOTE(vipa, 2023-06-16): "Desugar" the variable to an access
      -- of the record it was changed into
      let tmp = nameSym "tmp" in
      let newTm = TmMatch
        { target = TmVar {ident = rName, ty = tyunknown_, frozen = false, info = t.info}
        , pat = PatRecord
          { info = t.info
          , ty = tyunknown_
          , bindings = mapInsert label (PatNamed {ident = PName tmp, info = t.info, ty = tyunknown_})
            (mapEmpty cmpSID)
          }
          -- TODO(vipa, 2023-06-16): I believe this handles frozen
          -- variables correctly, but it should probably be checked
          -- more closely
        , thn = TmVar {ident = tmp, ty = tyunknown_, frozen = t.frozen, info = t.info}
        , els = TmNever {info = t.info, ty = tyunknown_}
        , ty = tyunknown_
        , info = t.info
        } in
      typeCheckExpr env newTm
    else
    match mapLookup t.ident env.varEnv with Some ty then
      let ty =
        if t.frozen then ty
        else inst t.info env.currentLvl ty
      in
      if optionIsSome opInfo then
        -- NOTE(vipa, 2023-06-16): We're looking at an operator,
        -- insert new reprs and record this fact
        let ty = substituteNewReprs env ty in
        let reprs = findReprs [] ty in
        TmOpVar
          { ident = t.ident
          , ty = ty
          , info = t.info
          , frozen = t.frozen
          , reprs = reprs
          , scaling = 1.0
          }
      else TmVar {t with ty = ty}
    else
      let msg = join [
        "* Encountered an unbound variable: ",
        nameGetStr t.ident, "\n",
        "* When type checking the expression\n"
      ] in
      errorSingle [t.info] msg
end

-- NOTE(vipa, 2023-06-26): The UCT analysis is essentially
-- type-checking, except we want actual /type-checking/, not
-- inference; we want to have precise type annotations to start. We
-- thus replace the type-checking of AST nodes with a tyAnnot field
-- with a version that uses the inferred field instead (TmLam, TmLet,
-- TmRecLets).
--
-- Additionally, we find TmLets and TmRecLets that are values and
-- mention collections and replace them with an TmOpDecl and TmOpImpl
-- each, to make it easier to swap representations, as well as get
-- smaller individual problems to solve.
--
-- Finally, we replace the TmVars that reference TmOpDecls with
-- TmOpVars.
lang UCTAnalysis = LamUCTAnalysis + LetUCTAnalysis + RecLetsUCTAnalysis + VarUCTAnalysis
end

lang MExprUCTAnalysis = MExprTypeCheckMost + UCTAnalysis + MExprPrettyPrint
end

lang UCTFragments = CollTypeAst + CollTypeUnify + OpDeclAst + OpDeclSym + OpDeclTypeCheck + TyWildAst + TyWildUnify + UCTPrettyPrint + UCTKeywordMaker + MExprConvertImpl
end

lang UCTSolverInterface = OpVarAst
  -- NOTE(vipa, 2023-07-05): Potential global state shared between
  -- individual solving processes
  syn SolverState =
  sem initSolverState : () -> SolverState
  -- NOTE(vipa, 2023-07-05): A set of solutions for a single
  -- TmOpImpl. Most likely the implementation will want to be either
  -- asyncronous or lazy in producing these solutions.
  syn OpImplSolutionSet a =
  syn OpImplSolution a =
  type OpVarInfo a = { app : TmOpVarRec, solutionSet : OpImplSolutionSet a }
  type UCTProblemAlt a =
    { opUses : [OpVarInfo a]
    , delayedReprUnifications : [(Repr, Repr)]
    , selfCost : OpCost
    , specType : Type
    -- NOTE(vipa, 2023-07-06): A token used by the surrounding system
    -- to carry data required to reconstruct a solved AST.
    , token : a
    }
  sem solveOne : all a. SolverState -> [UCTProblemAlt a] -> OpImplSolutionSet a

  -- NOTE(vipa, 2023-07-05): The returned list should have one picked
  -- solution per element in `opUses`
  sem concretizeSolution : all a. OpImplSolution a -> (a, [OpImplSolution a])
  -- NOTE(vipa, 2023-07-06): This is the only time the surrounding
  -- system will ask for a solution from a solution set. Every other
  -- solution will be acquired through concretizeSolution.
  sem cheapestSolution : all a. OpImplSolutionSet a -> OpImplSolution a

  -- NOTE(vipa, 2023-07-06): An arbitrary comparison between two
  -- solutions. Will only ever be called on two solutions from the
  -- same solution set. Should be equal iff both represent the same
  -- solution, using the same UCTProblemAlt as the base.
  sem cmpSolution : all a. OpImplSolution a -> OpImplSolution a -> Int
end

lang UCTDummySolver = UCTSolverInterface
  syn SolverState =
  | DummyState ()
  sem initSolverState = | _ -> DummyState ()

  syn OpImplSolutionSet a =
  | DummySet ([OpImplSolution a], a)

  syn OpImplSolution a =
  | DummySolution ([OpImplSolution a], a)

  sem solveOne st = | [alt] ++ _ -> DummySet
    ( map (lam info. cheapestSolution info.solutionSet) alt.opUses
    , alt.token
    )

  sem concretizeSolution =
  | DummySolution (solutions, token) ->
    (token, solutions)

  sem cheapestSolution =
  | DummySet x -> DummySolution x

  sem cmpSolution a = | b -> 0
end

lang UCTSolveAndReconstruct = UCTSolverInterface + OpImplAst + VarAst + LetAst + OpDeclAst + ReprDeclAst + CollTypeAst
  sem uctSolve : SolverState -> Expr -> Expr
  sem uctSolve st = | tm ->
    let opUses = workAltBody st (mapEmpty nameCmp) [] tm in
    let alt =
      { opUses = opUses
      , delayedReprUnifications = []
      , selfCost = 1.0
      , token = tm
      , specType = tyTm tm
      } in
    let topSolutionSet = solveOne st [alt] in
    match concretizeSolution (cheapestSolution topSolutionSet) with (tm, pickedSolutions) in
    match concretizeAlt (mapEmpty nameCmp) pickedSolutions tm with ([], tm) in
    tm

  sem workAltBody
    : SolverState
    -> Map Name (OpImplSolutionSet Expr)
    -> [OpVarInfo Expr] -> Expr -> [OpVarInfo Expr]
  sem workAltBody st env opUses =
  | tm -> sfold_Expr_Expr (workAltBody st env) opUses tm
  | TmOpVar x ->
    match mapLookup x.ident env with Some solutionSet then
      snoc opUses {app = x, solutionSet = solutionSet}
    else
      let msg = join [
        "* Encountered an operation without preceeding impl: ",
        nameGetStr x.ident, "\n",
        "* When collecting op uses for\n"
      ] in
      errorSingle [x.info] msg
  | TmOpImpl x ->
    let mkAlt = lam alt.
      { opUses = workAltBody st env [] alt.body
      , delayedReprUnifications = alt.delayedReprUnifications
      , selfCost = alt.selfCost
      , specType = alt.specType
      , token = alt.body
      } in
    let solutionSet = solveOne st (map mkAlt x.alternatives) in
    let env = mapInsert x.ident solutionSet env in
    workAltBody st env opUses x.inexpr

  type Concretizations = Map (OpImplSolution Expr) {ident : Name, concretization : Expr}
  syn ConcrRef =
  | ConcrRef {env : ConcretizationEnv, ref : Ref Concretizations}
  -- TODO(vipa, 2023-07-06): We should rename *all* bindings here (not
  -- just op impls), to ensure the symbolize invariant holds even when
  -- we duplicate alt bodies
  type ConcretizationEnv = Map Name ConcrRef

  sem lookupConcreteName : ConcrRef -> Name -> OpImplSolution Expr -> Name
  sem lookupConcreteName ref opName = | solution ->
    match ref with ConcrRef ref in
    match mapLookup solution (deref ref.ref) with Some x then x.ident else
    match concretizeSolution solution with (tm, pickedSolutions) in
    match concretizeAlt ref.env pickedSolutions tm with ([], tm) in
    let conc = {ident = nameSetNewSym opName, concretization = tm} in
    modref ref.ref (mapInsert solution conc (deref ref.ref));
    conc.ident

  -- TODO(vipa, 2023-07-07): This swaps all `TyColl`s with
  -- `TyUnknown`. This *should* be good enough for the OCaml backend,
  -- but isn't as good as it could be; we should be able to insert
  -- precise types according to what reprs were chosen. I leave that
  -- for later.
  sem removeCollTypes : Type -> Type
  sem removeCollTypes =
  | ty -> smap_Type_Type removeCollTypes ty
  | TyColl x -> TyUnknown {info = x.info}

  sem concretizeAlt : ConcretizationEnv -> [OpImplSolution Expr] -> Expr -> ([OpImplSolution Expr], Expr)
  sem concretizeAlt env pickedSolutions =
  | tm ->
    let tm = smap_Expr_Type removeCollTypes tm in
    let tm = smap_Expr_TypeLabel removeCollTypes tm in
    smapAccumL_Expr_Expr (concretizeAlt env) pickedSolutions tm
  | TmOpDecl {inexpr = inexpr} | TmReprDecl {inexpr = inexpr} ->
    concretizeAlt env pickedSolutions inexpr
  | TmOpVar x ->
    match mapLookup x.ident env with Some ref then
      match pickedSolutions with [solution] ++ pickedSolutions in
      let newIdent = lookupConcreteName ref x.ident solution in
      let var = TmVar
        { ident = newIdent
        , ty = removeCollTypes x.ty
        , info = x.info
        , frozen = x.frozen
        } in
      (pickedSolutions, var)
    else
      let msg = join [
        "* Encountered an operation without a preceeding op impl: ",
        nameGetStr x.ident, "\n",
        "* When concretizing this expression\n"
      ] in
      errorSingle [x.info] msg
  | TmOpImpl x ->
    let concretizations = ref (mapEmpty cmpSolution) in
    let env = mapInsert x.ident (ConcrRef {env = env, ref = concretizations}) env in
    match concretizeAlt env pickedSolutions x.inexpr with (pickedSolutions, inexpr) in
    let mkLet = lam inexpr. lam. lam x. TmLet
      { ident = x.ident
      , tyAnnot = tyunknown_
      , tyBody = tyTm x.concretization
      , body = x.concretization
      , inexpr = inexpr
      , ty = tyTm inexpr
      , info = infoTm inexpr
      } in
    (pickedSolutions, mapFoldWithKey mkLet inexpr (deref concretizations))
end

lang DumpUCTProblem = UCTFragments
  sem dumpUCTProblem : Int -> Expr -> ()
  sem dumpUCTProblem reprScope = | tm ->
    let apps = dumpUCTProblemWork [] tm in
    let reprToJson = lam repr. switch deref (botRepr repr)
      case BotRepr x then JsonArray [JsonInt x.scope, JsonInt (sym2hash x.sym)]
      case UninitRepr _ then JsonString "uninit"
      case LinkRepr _ then JsonString "link"  -- This should be impossible, but eh
      end in
    let appToLine = lam i. lam app.
      match clearAndCollectReprs [] app.1 with (reprs, ty) in
      let json = JsonObject (mapFromSeq cmpString
        [ ("opId", JsonInt i)
        , ("reprScope", JsonInt reprScope)
        , ("op", JsonString (nameGetStr app.0))
        , ("ty", JsonString (type2str ty))
        , ("reprs", JsonArray (map reprToJson reprs))
        ]) in
      printLn (json2string json) in
    iteri appToLine apps

  sem dumpUCTProblemWork : [(Name, Type)] -> Expr -> [(Name, Type)]
  sem dumpUCTProblemWork acc =
  | TmOpVar x -> snoc acc (x.ident, x.ty)
  | TmOpImpl x ->
    for_ x.alternatives (lam alt. dumpUCTProblem x.reprScope alt.body);
    dumpUCTProblemWork acc x.inexpr
  | tm -> sfold_Expr_Expr dumpUCTProblemWork acc tm

  sem clearAndCollectReprs : [Repr] -> Type -> ([Repr], Type)
  sem clearAndCollectReprs reprs =
  | TyColl x ->
    let reprs = snoc reprs x.repr in
    match clearAndCollectReprs reprs x.filter with (reprs, filter) in
    match clearAndCollectReprs reprs x.permutation with (reprs, permutation) in
    match clearAndCollectReprs reprs x.element with (reprs, element) in
    (reprs, TyColl {x with repr = ref (UninitRepr ()), filter = filter, permutation = permutation, element = element})
  | ty -> smapAccumL_Type_Type clearAndCollectReprs reprs ty
end

lang PrintMostFrequentRepr = UCTFragments + MExprAst
  sem findMostCommonRepr : Expr -> Option Symbol
  sem findMostCommonRepr = | tm ->
    let counts = findMostCommonRepr_ (mapEmpty (lam a. lam b. subi (sym2hash a) (sym2hash b))) tm in
    optionMap (lam x. x.0) (max (lam a. lam b. subi a.1 b.1) (mapBindings counts))

  sem findMostCommonRepr_ : Map Symbol Int -> Expr -> Map Symbol Int
  sem findMostCommonRepr_ acc =
  | TmOpVar x ->
    let symFromRepr = lam x. match deref (botRepr x) with BotRepr x in x.sym in
    let reprs = setOfSeq (lam a. lam b. subi (sym2hash a) (sym2hash b)) (map symFromRepr x.reprs) in
    setFold (lam acc. lam repr. mapInsertWith addi repr 1 acc) acc reprs
  | tm -> sfold_Expr_Expr findMostCommonRepr_ acc tm

  sem printIfExprHasRepr : Symbol -> Expr -> ()
  sem printIfExprHasRepr reprSymbol =
  | TmOpDecl x -> printIfExprHasRepr reprSymbol x.inexpr
  | TmOpImpl x -> printIfExprHasRepr reprSymbol x.inexpr
  | tm ->
    -- (if hasInExpr tm
    --  then ()
    --  else printIfTypeIsRepr reprSymbol (infoTm tm) (tyTm tm));
    sfold_Expr_Type (lam. lam ty. printIfTypeHasRepr reprSymbol [infoTm tm] ty) () tm;
    sfold_Expr_Expr (lam. lam tm. printIfExprHasRepr reprSymbol tm) () tm

  sem printIfTypeIsRepr : Symbol -> [Info] -> Type -> ()
  sem printIfTypeIsRepr reprSymbol infos = | ty ->
    match unwrapType ty with TyColl c then
      match deref (botRepr c.repr) with BotRepr x then
        if eqsym x.sym reprSymbol then
          let mkSection = lam info. {errorDefault with info = info} in
          let msg = errorMsg (map mkSection infos) {single = "", multi = ""} in
          printError (join ["\n", infoWarningString msg.0 msg.1, "\n"]);
          flushStderr ();
          ()
        else ()
      else ()
     else ()

  sem printIfTypeHasRepr : Symbol -> [Info] -> Type -> ()
  sem printIfTypeHasRepr reprSymbol infos =
  | ty & TyAlias x ->
    let infos = snoc infos (infoTy ty) in
    printIfTypeIsRepr reprSymbol infos ty;
    printIfTypeHasRepr reprSymbol infos x.display
  | ty ->
    let infos = snoc infos (infoTy ty) in
    printIfTypeIsRepr reprSymbol infos ty;
    sfold_Type_Type (lam. lam ty. printIfTypeHasRepr reprSymbol infos ty) () ty

  sem hasInExpr : Expr -> Bool
  sem hasInExpr =
  | TmLet _ | TmRecLets _ | TmExt _ | TmType _ | TmConDef _ | TmOpDecl _ | TmOpImpl _ -> true
  | _ -> false
end

lang PprintTyAnnot = PrettyPrint + Annotator + Ast + AliasTypeAst
  syn Expr = | FakeExpr {id : Int, result : Ref String, real : Expr}
  syn Type = | FakeType {id : Int, result : Ref String, real : Type}
  syn Pat  = | FakePat  {id : Int, result : Ref String, real : Pat}

  sem isAtomic =
  | FakeExpr x -> isAtomic x.real
  sem patIsAtomic =
  | FakePat x -> patIsAtomic x.real
  sem typePrecedence =
  | FakeType x -> typePrecedence x.real

  sem pprintCode indent env =
  | FakeExpr x ->
    match pprintAnnotExpr indent env x.real with (env, real) in
    modref x.result real;
    (env, cons '!' (cons '!' (int2string x.id)))
  sem getPatStringCode indent env =
  | FakePat x ->
    match pprintAnnotPat indent env x.real with (env, real) in
    modref x.result real;
    (env, cons '!' (cons '!' (int2string x.id)))
  sem getTypeStringCode indent env =
  | FakeType x ->
    match pprintAnnotType indent env x.real with (env, real) in
    modref x.result real;
    (env, cons '!' (cons '!' (int2string x.id)))

  sem subSwap
  : all a. (a -> Int -> (Ref String, a))
  -> [Ref String]
  -> a
  -> ([Ref String], a)
  sem subSwap mkPlaceholder acc = | a ->
    match mkPlaceholder a (length acc) with (newRef, fake) in
    (snoc acc newRef, fake)
  sem mkFakeExpr real = | id ->
    let r = ref "" in
    (r, FakeExpr {id = id, result = r, real = real})
  sem mkFakeType real = | id ->
    let r = ref "" in
    (r, FakeType {id = id, result = r, real = real})
  sem mkFakePat real = | id ->
    let r = ref "" in
    (r, FakePat {id = id, result = r, real = real})

  sem pprintAst : Expr -> Output
  sem pprintAst = | tm ->
    match pprintAnnotExpr 0 pprintEnvEmpty tm with (_, output) in
    finalize output

  sem pprintAnnotExpr : Int -> PprintEnv -> Expr -> (PprintEnv, Output)
  sem pprintAnnotExpr indent env =
  | orig & x ->
    let subs = [] in
    match smapAccumL_Expr_Expr (subSwap mkFakeExpr) subs x with (subs, x) in
    match smapAccumL_Expr_Type (subSwap mkFakeType) subs x with (subs, x) in
    match smapAccumL_Expr_Pat (subSwap mkFakePat) subs x with (subs, x) in
    match pprintCode indent env x with (env, x) in
    match getTypeStringCode 0 env (_removeAliases (tyTm orig)) with (env, ty) in
    (env, annotate ty (_fixOutput x subs))

  sem pprintAnnotPat : Int -> PprintEnv -> Pat -> (PprintEnv, Output)
  sem pprintAnnotPat indent env =
  | orig & x ->
    let subs = [] in
    match smapAccumL_Pat_Expr (subSwap mkFakeExpr) subs x with (subs, x) in
    match smapAccumL_Pat_Type (subSwap mkFakeType) subs x with (subs, x) in
    match smapAccumL_Pat_Pat (subSwap mkFakePat) subs x with (subs, x) in
    match getPatStringCode indent env x with (env, x) in
    match getTypeStringCode 0 env (_removeAliases (tyPat orig)) with (env, ty) in
    (env, annotate ty (_fixOutput x subs))

  sem pprintAnnotType : Int -> PprintEnv -> Type -> (PprintEnv, Output)
  sem pprintAnnotType indent env =
  | orig & x ->
    let subs = [] in
    match smapAccumL_Type_Type (subSwap mkFakeType) subs x with (subs, x) in
    match getTypeStringCode indent env x with (env, x) in
    match getTypeStringCode 0 env (_removeAliases orig) with (env, ty) in
    (env, annotate ty (_fixOutput x subs))

  sem _removeAliases : Type -> Type
  sem _removeAliases =
  | TyAlias x -> _removeAliases x.content
  | ty -> smap_Type_Type _removeAliases ty

  sem _fixOutput : String -> [Ref String] -> Output
  sem _fixOutput str = | subs ->
    recursive let splitWhile : all a. (a -> Bool) -> [a] -> ([a], [a]) = lam pred. lam seq.
      match seq with [x] ++ rest then
        if pred x then
          match splitWhile pred rest with (passing, rest) in
          (cons x passing, rest)
        else ([], seq)
      else ([], [])
    in
    recursive let work = lam acc. lam str.
      switch str
      case ['!', '!', c & ('0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9')] ++ str then
        match splitWhile isDigit (cons c str) with (number, str) in
        let acc = concat acc (deref (get subs (string2int number))) in
        work acc str
      case [c] ++ str then
        work (snoc acc c) str
      case [] then
        acc
      end
    in work "" (escapeContent str)
end
