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
include "const-transformer.mc"
include "builtin.mc"
include "eval.mc"
include "cp/high-level.mc"
include "mexpr/annotate.mc"
include "multicore/promise.mc"

lang AnnotateSimple = HtmlAnnotator + AnnotateSources
end

lang RepTypesKeywordMaker = KeywordMakerBase + ReprTypeAst + TyWildAst + OpDeclAst
  sem matchTypeKeywordString info =
  | "_" ->
    let mk = lam. TyWild {info = info} in
    Some (0, mk)
  | "Repr" ->
    let mk = lam args. match args with [arg] in TyRepr
      { info = info
      , arg = arg
      , repr = ref (UninitRepr ())
      } in
    Some (1, mk)

  sem isTypeKeyword =
  | TyRepr _ -> true

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

-- lang ConvertToMExpr = Ast + UniversalImplementationBaseAst
--   sem convertToMExpr : Merged -> Expr
--   sem convertToMExpr =
--   | m -> errorSingle [get_Merged_info m] "This syntax isn't valid in an expression context"
--   sem convertToMExprTy : Merged -> Type
--   sem convertToMExprTy =
--   | m -> errorSingle [get_Merged_info m] "This syntax isn't valid in a type context"
--   sem convertToMExprPat : Merged -> Pat
--   sem convertToMExprPat =
--   | m -> errorSingle [get_Merged_info m] "This syntax isn't valid in a pattern context"
-- end

-- lang EvalCost = ConstTransformer + IntAst + FloatAst + Eval + ConvertToMExpr
--   sem _evalCost : Merged -> OpCost
--   sem _evalCost = | tm ->
--     let tm = convertToMExpr tm in
--     let tm = constTransform builtin tm in
--     let ctx = evalCtxEmpty () in
--     -- TODO(vipa, 2023-05-02): Name hygiene, symbolize over all of an imc file in general
--     let ctx = {ctx with env = evalEnvInsert (nameNoSym "n") (float_ 100.0) ctx.env} in
--     switch eval ctx tm
--     case TmConst {val = CFloat f} then f.val
--     case TmConst {val = CInt i} then int2float i.val
--     case _ then errorSingle [infoTm tm] "This expression did not evaluate to a number."
--     end
-- end

-- lang ConvertLet = ConvertToMExpr + LetMergedAst + LetAst
--   sem convertToMExpr =
--   | LetMerged x -> TmLet
--     { info = x.info
--     , ident = x.v.v
--     , tyAnnot = optionMapOr tyunknown_ convertToMExprTy x.ty
--     , body = convertToMExpr x.e
--     , inexpr = convertToMExpr x.right
--     , tyBody = tyunknown_
--     , ty = tyunknown_
--     }
-- end

-- lang ConvertRecLet = ConvertToMExpr + RecLetMergedAst + RecLetsAst
--   sem convertToMExpr =
--   | RecLetMerged x ->
--     let mkBinding = lam binding.
--       { ident = binding.v.v
--       , tyAnnot = optionMapOr tyunknown_ convertToMExprTy binding.ty
--       , body = convertToMExpr binding.e
--       , tyBody = tyunknown_
--       , info = binding.v.i
--       }
--     in TmRecLets
--       -- TODO(vipa, 2023-10-22): for inconvenient syntactic reasons we
--       -- only allow one binding presently, so we're not mapping over
--       -- bindings
--       { bindings = [mkBinding x.bindings]
--       , ty = tyunknown_
--       , inexpr = convertToMExpr x.right
--       , info = x.info
--       }
-- end

-- lang ConvertLam = ConvertToMExpr + LamMergedAst + LamAst
--   sem convertToMExpr =
--   | LamMerged x -> TmLam
--     { info = x.info
--     , ident = optionMapOr (nameNoSym "") (lam x. x.v) x.v
--     , tyAnnot = optionMapOr tyunknown_ convertToMExprTy x.ty
--     , tyParam = tyunknown_
--     , body = convertToMExpr x.right
--     , ty = tyunknown_
--     }
-- end

-- lang ConvertIf = ConvertToMExpr + IfMergedAst + MatchAst + BoolPat
--  sem convertToMExpr =
--  | IfMerged x -> TmMatch
--    { target = convertToMExpr x.c
--    , pat = PatBool {info = get_Merged_info x.c, val = true, ty = tyunknown_}
--    , thn = convertToMExpr x.t
--    , els = convertToMExpr x.e
--    , ty = tyunknown_
--    , info = x.info
--    }
-- end

-- lang ConvertBoolCon = ConvertToMExpr + BoolConMergedAst + BoolTypeAst
--   sem convertToMExprTy =
--   | BoolConMerged x -> TyBool {info = x.info}
-- end

-- lang ConvertIntCon = ConvertToMExpr + IntConMergedAst + IntTypeAst
--   sem convertToMExprTy =
--   | IntConMerged x -> TyInt {info = x.info}
-- end

-- lang ConvertCharCon = ConvertToMExpr + CharConMergedAst + CharTypeAst
--   sem convertToMExprTy =
--   | CharConMerged x -> TyChar {info = x.info}
-- end

-- lang ConvertFloatCon = ConvertToMExpr + FloatConMergedAst + FloatTypeAst
--   sem convertToMExprTy =
--   | FloatConMerged x -> TyFloat {info = x.info}
-- end

-- lang ConvertUnknownCon = ConvertToMExpr + UnknownConMergedAst + UnknownTypeAst
--   sem convertToMExprTy =
--   | UnknownConMerged x -> TyUnknown {info = x.info}
-- end

-- lang ConvertProj = ConvertToMExpr + ProjMergedAst + MatchAst + RecordPat
--   sem convertToMExpr =
--   | ProjMerged x ->
--     let n = nameSym "x" in
--     let pat = withInfoPat x.info
--       (match x.label with Some l then
--          prec_ [(l.v, npvar_ n)]
--        else match x.idx with Some idx then
--          prec_ [(int2string idx.v, npvar_ n)]
--        else never) in
--     TmMatch
--     { target = convertToMExpr x.left
--     , pat = pat
--     , thn = withInfo x.info (nvar_ n)
--     , els = withInfo x.info never_
--     , ty = tyunknown_
--     , info = x.info
--     }
-- end

-- lang ConvertTuple = ConvertToMExpr + TupleMergedAst + RecordAst + RecordTypeAst + RecordPat
--   sem convertToMExpr =
--   | TupleMerged x -> TmRecord
--     { info = x.info
--     , ty = tyunknown_
--     , bindings = mapFromSeq cmpSID
--       (mapi (lam i. lam e. (stringToSid (int2string i), convertToMExpr e)) x.e)
--     }

--   sem convertToMExprTy =
--   | TupleMerged x -> TyRecord
--     { info = x.info
--     , fields = mapFromSeq cmpSID
--       (mapi (lam i. lam e. (stringToSid (int2string i), convertToMExprTy e)) x.e)
--     }

--   sem convertToMExprPat =
--   | TupleMerged x -> PatRecord
--     { info = x.info
--     , bindings = mapFromSeq cmpSID
--       (mapi (lam i. lam e. (stringToSid (int2string i), convertToMExprPat e)) x.e)
--     , ty = tyunknown_
--     }
-- end

-- lang ConvertArrow = ConvertToMExpr + ArrowMergedAst + FunTypeAst
--   sem convertToMExprTy =
--   | ArrowMerged x -> TyArrow
--     { info = x.info
--     , from = convertToMExprTy x.left
--     , to = convertToMExprTy x.right
--     }
-- end

-- lang ConvertSemi = ConvertToMExpr + SemiMergedAst
--   sem convertToMExpr =
--   | SemiMerged x ->
--     withInfo x.info (semi_ (convertToMExpr x.left) (convertToMExpr x.right))
-- end

-- lang ConvertApp = ConvertToMExpr + AppMergedAst + AppAst + AppTypeAst
--   sem convertToMExpr =
--   | AppMerged x -> TmApp
--     { lhs = convertToMExpr x.left
--     , rhs = convertToMExpr x.right
--     , ty = tyunknown_
--     , info = x.info
--     }

--   sem convertToMExprTy =
--   | AppMerged x -> TyApp
--     { lhs = convertToMExprTy x.left
--     , rhs = convertToMExprTy x.right
--     , info = x.info
--     }

--   sem convertToMExprPat =
--   | AppMerged x -> errorSingle [x.info] "Invalid application in pattern context"
-- end

-- lang ConvertOpApp = ConvertToMExpr + OperatorAppBaseMergedAst + AppMergedAst + EvalCost + OpVarAst + FrozenVarMergedAst + VarMergedAst
--   sem convertToMExpr =
--   | AppMerged
--     { left = AppMerged
--       { left = OperatorAppBaseMerged _
--       , right = scaling
--       }
--     , right = VarMerged x
--     , info = info
--     } -> TmOpVar
--       { ident = x.v.v
--       , ty = tyunknown_
--       , info = info
--       , frozen = false
--       , scaling = _evalCost scaling
--       }
--   | AppMerged
--     { left = AppMerged
--       { left = OperatorAppBaseMerged _
--       , right = scaling
--       }
--     , right = FrozenVarMerged x
--     , info = info
--     } -> TmOpVar
--       { ident = x.v.v
--       , ty = tyunknown_
--       , info = info
--       , frozen = true
--       , scaling = _evalCost scaling
--       }
-- end

-- lang ConvertTypeDef = ConvertToMExpr + TypeMergedAst + TypeAst + VariantTypeAst
--   sem convertToMExpr =
--   | TypeMerged x -> TmType
--     { ident = x.v.v
--     , params = map (lam x. x.v) x.args
--     , tyIdent = match x.ty with Some ty
--       then convertToMExprTy ty
--       else TyVariant {info = x.info, constrs = mapEmpty nameCmp}
--     , info = x.info
--     , ty = tyunknown_
--     , inexpr = convertToMExpr x.right
--     }
-- end

-- lang ConvertConDef = ConvertToMExpr + ConDefMergedAst + DataAst
--   sem convertToMExpr =
--   | ConDefMerged x -> TmConDef
--     { ident = x.v.v
--     , tyIdent = convertToMExprTy x.ty
--     , inexpr = convertToMExpr x.right
--     , ty = tyunknown_
--     , info = x.info
--     }
-- end

-- lang ConvertCon = ConvertToMExpr + ConMergedAst + AppMergedAst + DataAst + ConTypeAst + DataPat
--   sem convertToMExpr =
--   | AppMerged (x & {left = ConMerged c}) ->
--     TmConApp { ident = c.c.v, body = convertToMExpr x.right, ty = tyunknown_, info = x.info }
--   | ConMerged c -> errorSingle [c.info] "Unapplied constructor"

--   sem convertToMExprTy =
--   | ConMerged c -> TyCon
--     { ident = c.c.v
--     , info = c.info
--     }

--   sem convertToMExprPat =
--   | AppMerged (x & {left = ConMerged c}) -> PatCon
--     { ident = c.c.v
--     , subpat = convertToMExprPat x.right
--     , ty = tyunknown_
--     , info = x.info
--     }
--   | ConMerged c -> errorSingle [c.info] "Unapplied constructor"
-- end

-- lang ConvertWild = ConvertToMExpr + WildMergedAst + TyWildAst + NamedPat
--   sem convertToMExprTy =
--   | WildMerged x -> TyWild {info = x.info}

--   sem convertToMExprPat =
--   | WildMerged x -> PatNamed {ident = PWildcard (), info = x.info, ty = tyunknown_}
-- end

-- lang ConvertSubst = ConvertToMExpr + ConMergedAst + NotMergedAst + AppMergedAst + ReprSubstAst + TyWildAst + ReprTypeAst
--   sem convertToMExprTy =
--   | NotMerged
--     { right = ConMerged {c = {v = subst}}
--     , info = overallInfo
--     } ->
--     TySubst
--     { info = overallInfo
--     , arg = TyRepr { info = overallInfo, arg = TyWild {info = overallInfo}, repr = ref (UninitRepr ()) }
--     , subst = subst
--     }
--   | AppMerged
--     { left = NotMerged {right = ConMerged {c = {v = subst}}}
--     , right = reprTy
--     , info = overallInfo
--     } ->
--     TySubst
--     { info = overallInfo
--     , arg = convertToMExprTy reprTy
--     , subst = subst
--     }
-- end

-- lang ConvertRepr = ConvertToMExpr + ReprTypeAst + ConMergedAst + AppMergedAst
--   sem convertToMExprTy =
--   | AppMerged
--     { left = ConMerged {c = {v = ("Repr", _)}}
--     , right = arg
--     , info = overallInfo
--     } ->
--     TyRepr
--     { info = overallInfo
--     , arg = convertToMExprTy arg
--     , repr = ref (UninitRepr ())
--     }
--   | ConMerged {c = {v = ("Repr", _)}, info = info} -> errorSingle [info] "Repr must be applied to a type argument"
-- end

-- lang ConvertVar = ConvertToMExpr + VarMergedAst + VarAst + VarTypeAst + NamedPat
--   sem convertToMExpr =
--   | VarMerged x -> TmVar {ident = x.v.v, ty = tyunknown_, info = x.info, frozen = false}
--   sem convertToMExprTy =
--   | VarMerged x -> TyVar {ident = x.v.v, info = x.info}
--   sem convertToMExprPat =
--   | VarMerged x -> PatNamed {ident = PName x.v.v, info = x.info, ty = tyunknown_}
-- end

-- lang ConvertAll = ConvertToMExpr + AllMergedAst + AllTypeAst
--   sem convertToMExprTy =
--   | AllMerged x -> TyAll
--     { info = x.info
--     , ident = x.v.v
--     , kind = Poly ()
--     , ty = convertToMExprTy x.right
--     }
-- end

-- lang ConvertFrozenVar = ConvertToMExpr + FrozenVarMergedAst + VarAst
--   sem convertToMExpr =
--   | FrozenVarMerged x -> TmVar {ident = x.v.v, ty = tyunknown_, info = x.info, frozen = true}
-- end

-- lang ConvertChar = ConvertToMExpr + CharMergedAst + CharAst + CharPat
--   sem convertToMExpr =
--   | CharMerged x -> TmConst {val = CChar {val = x.v.v}, ty = tyunknown_, info = x.info}
--   sem convertToMExprPat =
--   | CharMerged x -> PatChar {val = x.v.v, ty = tyunknown_, info = x.info}
-- end

-- lang ConvertInt = ConvertToMExpr + IntMergedAst + IntAst + IntPat
--   sem convertToMExpr =
--   | IntMerged x -> TmConst {val = CInt {val = x.v.v}, ty = tyunknown_, info = x.info}
--   sem convertToMExprPat =
--   | IntMerged x -> PatInt {val = x.v.v, ty = tyunknown_, info = x.info}
-- end

-- lang ConvertFloat = ConvertToMExpr + FloatMergedAst + FloatAst
--   sem convertToMExpr =
--   | FloatMerged x -> TmConst {info = x.info, val = CFloat {val = x.v.v}, ty = tyunknown_}
-- end

-- lang ConvertTrue = ConvertToMExpr + TrueMergedAst + BoolAst + BoolPat
--   sem convertToMExpr =
--   | TrueMerged x -> TmConst {info = x.info, val = CBool {val = true}, ty = tyunknown_}
--   sem convertToMExprPat =
--   | TrueMerged x -> PatBool {val = true, ty = tyunknown_, info = x.info}
-- end

-- lang ConvertFalse = ConvertToMExpr + FalseMergedAst + BoolAst + BoolPat
--   sem convertToMExpr =
--   | FalseMerged x -> TmConst {info = x.info, val = CBool {val = false}, ty = tyunknown_}
--   sem convertToMExprPat =
--   | FalseMerged x -> PatBool {val = false, ty = tyunknown_, info = x.info}
-- end

-- lang ConvertNever = ConvertToMExpr + NeverMergedAst + NeverAst
--   sem convertToMExpr =
--   | NeverMerged x -> TmNever {info = x.info, ty = tyunknown_}
-- end

-- lang ConvertString = ConvertToMExpr + StringMergedAst + SeqAst + CharAst
--   sem convertToMExpr =
--   | StringMerged x -> errorSingle [x.info] "Conversion not supported yet"
-- end

-- lang ConvertSequence = ConvertToMExpr + SequenceMergedAst + SeqAst
--   sem convertToMExpr =
--   | SequenceMerged x -> errorSingle [x.info] "Conversion not supported yet"
-- end

-- lang ConvertRecord = ConvertToMExpr + RecordMergedAst + RecordAst
--   sem convertToMExpr =
--   | RecordMerged x ->
--     let addField = lam acc. lam field.
--       optionMap (lam ty. warnSingle [get_Merged_info ty] "Type annotations on records are ignored right now.") field.ty;
--       match field.e with Some e then
--         mapInsert (stringToSid field.label.v) (convertToMExpr e) acc
--       else errorSingle [field.label.i] "Field without a right-hand side."
--     in TmRecord
--       { bindings = foldl addField (mapEmpty cmpSID) x.fields
--       , ty = tyunknown_
--       , info = x.info
--       }
-- end

-- lang ConvertNotPat = ConvertToMExpr + NotMergedAst + NotPat
--   sem convertToMExprPat =
--   | NotMerged x -> errorSingle [x.info] "Conversion not supported yet"
-- end

-- lang ConvertOrPat = ConvertToMExpr + OrMergedAst + OrPat
--   sem convertToMExprPat =
--   | OrMerged x -> errorSingle [x.info] "Conversion not supported yet"
-- end

-- lang ConvertAndPat = ConvertToMExpr + AndMergedAst + AndPat
--   sem convertToMExprPat =
--   | AndMerged x -> errorSingle [x.info] "Conversion not supported yet"
-- end

-- lang ConvertConcatPat = ConvertToMExpr + ConcatMergedAst + SeqEdgePat
--   sem convertToMExprPat =
--   | ConcatMerged x -> errorSingle [x.info] "Conversion not supported yet"
-- end

-- lang MExprConvertImpl = ConvertConcatPat + ConvertAndPat + ConvertOrPat + ConvertNotPat + ConvertRecord + ConvertSequence + ConvertString + ConvertNever + ConvertFalse + ConvertTrue + ConvertFloat + ConvertInt + ConvertChar + ConvertFrozenVar + ConvertVar + ConvertCon + ConvertConDef + ConvertTypeDef + ConvertApp + ConvertSemi + ConvertProj + ConvertWild + ConvertRepr + ConvertSubst + ConvertArrow + ConvertTuple + ConvertUnknownCon + ConvertFloatCon + ConvertCharCon + ConvertIntCon + ConvertBoolCon + ConvertLam + ConvertIf + ConvertOpApp + ConvertAll + ConvertLet + ConvertRecLet
-- end

-- lang CollectImpls = ConvertToMExpr + UniversalImplementationAst + EvalCost + OpVarAst
--   sem collectImpls : String -> ImplData
--   sem collectImpls = | filename ->
--     match parseUniversalImplementationExn filename (readFile filename) with TopsUFile {tops=tops} in
--     let f = lam acc. lam top.
--       switch top
--       case ImplDeclUTop x then
--         let selfCost = _evalCost x.cost in
--         let body = convertToMExpr x.body in
--         let specType = optionMapOr tyunknown_ convertToMExprTy x.tyAnnot in
--         let impl =
--           { selfCost = selfCost
--           , body = body
--           , specType = specType
--           , info = x.info
--           } in
--         { acc with impls = mapInsertWith concat (stringToSid (nameGetStr x.name.v))
--           [impl]
--           acc.impls
--         }
--       case ReprDeclUTop x then
--         recursive let replaceMetaVars = lam acc. lam m.
--           match m with MetaVarMerged x then
--             match
--               match mapLookup (nameGetStr x.var.v) acc with Some name then (acc, name) else
--               let name = nameSetNewSym x.var.v in
--               (mapInsert (nameGetStr name) name acc, name)
--             with (acc, name) in
--             (acc, VarMerged {info = x.info, v = {v = name, i = x.var.i}})
--           else
--             smapAccumL_Merged_Merged replaceMetaVars acc m in
--         match replaceMetaVars (mapEmpty cmpString) x.pat with (vars, pat) in
--         match replaceMetaVars vars x.repr with (vars, repr) in
--         let repr =
--           { vars = mapValues vars
--           , pat = convertToMExprTy pat
--           , repr = convertToMExprTy repr
--           } in
--         { acc with reprs = mapInsert x.name.v repr acc.reprs }
--       end
--     in foldl f emptyImplData tops
-- end

lang LamRepTypesAnalysis = TypeCheck + LamAst + SubstituteNewReprs
  sem typeCheckExpr env =
  | TmLam t ->
    let tyParam = substituteNewReprs env t.tyParam in
    let body = typeCheckExpr (_insertVar t.ident tyParam env) t.body in
    let tyLam = ityarrow_ t.info tyParam (tyTm body) in
    TmLam {t with body = body, tyParam = tyParam, ty = tyLam}
end

lang LetRepTypesAnalysis = TypeCheck + LetAst + SubstituteNewReprs + OpImplAst + OpDeclAst + IsValue + MetaVarDisableGeneralize
  sem typeCheckExpr env =
  | TmLet t ->
    let newLvl = addi 1 env.currentLvl in
    let isValue = isValue (GVal ()) t.body in
    let shouldBeOp = if isValue then containsRepr t.tyBody else false in
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
      let env = {env with reptypes = {env.reptypes with opNamesInScope = mapInsert t.ident (None ()) env.reptypes.opNamesInScope}} in
      let inexpr = typeCheckExpr env t.inexpr in
      let ty = tyTm inexpr in
      TmOpDecl
      { info = t.info
      , ident = t.ident
      , tyAnnot = tyBody
      , ty = ty
      , inexpr = TmOpImpl
        { ident = t.ident
        , implId = negi 1
        , selfCost = 1.0
        , body = body
        , specType = tyBody
        , delayedReprUnifications = delayedReprUnifications
        , inexpr = inexpr
        , ty = ty
        , reprScope = reprScope
        , metaLevel = env.currentLvl
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

lang RecLetsRepTypesAnalysis = TypeCheck + RecLetsAst + MetaVarDisableGeneralize + RecordAst + OpImplAst + OpDeclAst + RepTypesHelpers + IsValue + SubstituteNewReprs
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
      then any (lam b. containsRepr b.tyBody) t.bindings
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
        env.reptypes.opNamesInScope
        newT.bindings in
      let opNamesInScope = mapInsert recordName (None ()) opNamesInScope in
      let env = _insertVar recordName newT.ty env in
      let env = {env with reptypes = {env.reptypes with opNamesInScope = opNamesInScope}} in
      typeCheckExpr env t.inexpr in
    let ty = tyTm inexpr in
    TmOpDecl
    { info = t.info
    , ident = recordName
    , tyAnnot = newT.ty
    , ty = ty
    , inexpr = TmOpImpl
      { ident = recordName
      , implId = negi 1
      , selfCost = 1.0
      , body = TmRecLets newT
      , specType = newT.ty
      , delayedReprUnifications = delayedReprUnifications
      , inexpr = inexpr
      , ty = ty
      , reprScope = reprScope
      , metaLevel = env.currentLvl
      , info = t.info
      }
    }
end

lang VarRepTypesAnalysis = TypeCheck + VarAst + OpVarAst + RepTypesHelpers + SubstituteNewReprs + NeverAst + MatchAst + NamedPat + RecordPat
  sem typeCheckExpr env =
  | TmVar t ->
    let opInfo = mapLookup t.ident env.reptypes.opNamesInScope in
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
        TmOpVar
          { ident = t.ident
          , ty = ty
          , info = t.info
          , frozen = t.frozen
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

lang OpImplRepTypesAnalysis = TypeCheck + OpImplAst + ResolveType + SubstituteNewReprs + RepTypesHelpers + ApplyReprSubsts
  sem typeCheckExpr env =
  | TmOpImpl x ->
    let typeCheckBody = lam env.
      let newLvl = addi 1 env.currentLvl in
      let specType = substituteNewReprs env x.specType in
      let newEnv = {env with currentLvl = newLvl} in
      let reprType = applyReprSubsts newEnv specType in
      match stripTyAll reprType with (vars, reprType) in
      let newTyVars = foldr (lam v. mapInsert v.0 newLvl) newEnv.tyVarEnv vars in
      let newEnv = {newEnv with tyVarEnv = newTyVars} in
      match captureDelayedReprUnifications newEnv
        (lam. typeCheckExpr newEnv x.body)
        with (body, delayedReprUnifications) in
      unify newEnv [infoTy reprType, infoTm body] reprType (tyTm body);
      {x with body = body, delayedReprUnifications = delayedReprUnifications, specType = specType}
    in
    match withNewReprScope env (lam env. typeCheckBody env)
      with (x, reprScope, []) in
    let inexpr = typeCheckExpr env x.inexpr in
    TmOpImpl
    { x with reprScope = reprScope
    , metaLevel = env.currentLvl
    , inexpr = inexpr
    , ty = tyTm inexpr
    }
end

-- NOTE(vipa, 2023-06-26): The RepTypes analysis is essentially
-- type-checking, except we want actual type-/checking/, not
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
lang RepTypesAnalysis = LamRepTypesAnalysis + LetRepTypesAnalysis + RecLetsRepTypesAnalysis + VarRepTypesAnalysis + OpImplRepTypesAnalysis
end

lang MExprRepTypesAnalysis = MExprTypeCheckMost + RepTypesAnalysis + MExprPrettyPrint + RepTypesPrettyPrint
end

lang RepTypesFragments = ReprTypeAst + ReprSubstAst + ReprTypeUnify + OpDeclAst + OpDeclSym + OpDeclTypeCheck + TyWildAst + TyWildUnify + RepTypesPrettyPrint + RepTypesKeywordMaker
end

lang RepTypesShallowSolverInterface = OpVarAst + OpImplAst + UnifyPure
  -- NOTE(vipa, 2023-07-05): Potential global state shared between
  -- individual solving processes
  syn SolverGlobal a =
  sem initSolverGlobal : all a. () -> SolverGlobal a

  -- NOTE(vipa, 2023-10-25): Solver state passed along each branch of
  -- the AST.
  syn SolverBranch a =
  sem initSolverBranch : all a. SolverGlobal a -> SolverBranch a

  -- NOTE(vipa, 2023-10-25): A solution to some particular op
  syn SolverSolution a =

  type OpImpl a =
    { implId: ImplId
    , op : Name
    , opUses : [TmOpVarRec]
    , selfCost : OpCost
    , uni : Unification
    , specType : Type
    , reprScope : Int
    , metaLevel : Int
    , info : Info
    -- NOTE(vipa, 2023-07-06): A token used by the surrounding system
    -- to carry data required to reconstruct a solved AST.
    , token : a
    }

  type SolProps a =
    { sol : SolverSolution a
    , cost : OpCost
    , uni : Unification
    }

  -- NOTE(vipa, 2023-10-25): There's a new `OpImpl` in scope
  sem addImpl : all a. SolverGlobal a -> SolverBranch a -> OpImpl a -> SolverBranch a

  -- NOTE(vipa, 2023-07-06): This is the only time the surrounding
  -- system will ask for a solution from a solution set. Every other
  -- solution will be acquired through concretizeSolution.
  sem allSolutions : all a. SolverGlobal a -> SolverBranch a -> Name -> Type -> (SolverBranch a, [SolProps a])

  -- NOTE(vipa, 2023-10-25): Solve the top-level, where we just get a
  -- sequence of solutions that are available for each opUse, and
  -- we're to find the cheapest solution (i.e., pick one
  -- `SolverSolution` per element in the input list).
  sem topSolve : all a. SolverGlobal a -> [[SolProps a]] -> [SolverSolution a]

  -- NOTE(vipa, 2023-07-05): The returned list should have one picked
  -- solution per element in `opUses`. The returned `ImplId` should be
  -- the greatest `ImplId` in use in this solution.
  sem concretizeSolution : all a. SolverGlobal a -> SolverSolution a -> (a, ImplId, [SolverSolution a])

  -- NOTE(vipa, 2023-10-25): An arbitrary ordering over solutions
  sem cmpSolution : all a. SolverSolution a -> SolverSolution a -> Int
end

lang RepTypesSolveAndReconstruct = RepTypesShallowSolverInterface + OpImplAst + VarAst + LetAst + OpDeclAst + ReprDeclAst + ReprTypeAst + UnifyPure + AliasTypeAst
  -- Top interface, meant to be used outside --
  sem reprSolve : Expr -> Expr
  sem reprSolve = | tm ->
    let global = initSolverGlobal () in
    -- NOTE(vipa, 2023-10-25): Right now we do not handle nested impls
    -- in the collection phase
    let initState =
      { branch = initSolverBranch global
      , opUses = []
      , nextId = 0
      } in
    match collectForReprSolve global initState tm with (state, tm) in
    let pickedSolutions = topSolve global state.opUses in
    -- NOTE(vipa, 2023-10-25): The concretization phase *does* handle
    -- nested impls, so it shouldn't have to be updated if the
    -- collection phase is improved later on
    let initState =
      { remainingSolutions = pickedSolutions
      , requests = mapEmpty subi
      , requestsByOpAndSol = mapEmpty (lam a. lam b.
        let res = nameCmp a.0 b.0 in
        if neqi res 0 then res else
        cmpSolution a.1 b.1)
      , global = global
      } in
    match concretizeAlt initState tm with (state, tm) in
    mapFoldWithKey (lam. lam id. lam deps. printLn (join ["Left-over dep, id: ", int2string id, ", num deps: ", int2string (length deps)])) () state.requests;
    removeReprExpr tm

  -- Collecting and solving sub-problems --
  type CollectState =
    { branch : SolverBranch Expr
    , opUses : [[SolProps Expr]]
    , nextId : Int
    }

  sem collectForReprSolve
    : SolverGlobal Expr
    -> CollectState
    -> Expr
    -> (CollectState, Expr)
  sem collectForReprSolve global state =
  | tm -> smapAccumL_Expr_Expr (collectForReprSolve global) state tm
  | tm & TmOpVar x ->
    match allSolutions global state.branch x.ident x.ty with (branch, sols) in
    if null sols then
      errorSingle [x.info] "There were no valid implementations here."
    else
      let sols = map (lam sol. {sol with cost = mulf x.scaling sol.cost}) sols in
      ({state with branch = branch, opUses = snoc state.opUses sols}, tm)
  | TmOpImpl x ->
    let implId = state.nextId in
    let state = {state with nextId = addi state.nextId 1} in
    let opImpl =
      { implId = implId
      , op = x.ident
      , opUses = findOpUses [] x.body
      , selfCost = x.selfCost
      , uni = optionGetOrElse (lam. error "Compiler error in reptype solver")
        (optionFoldlM
          (lam acc. lam pair. unifyReprPure acc pair.0 pair.1)
          (emptyUnification ())
          x.delayedReprUnifications)
      , specType = x.specType
      , reprScope = x.reprScope
      , metaLevel = x.metaLevel
      , info = x.info
      , token = x.body
      } in
    let newBranch = addImpl global state.branch opImpl in
    match collectForReprSolve global {state with branch = newBranch} x.inexpr
      with (newState, inexpr) in
    -- NOTE(vipa, 2023-10-25): Here we restore the old branch, since
    -- any new solutions attained along the new branch might use this
    -- new impl, which isn't in scope in whatever we're returning to
    ( {newState with branch = state.branch}
    , TmOpImpl
      { x with implId = implId
      , inexpr = inexpr
      }
    )

  sem findOpUses : [TmOpVarRec] -> Expr -> [TmOpVarRec]
  sem findOpUses acc =
  | tm -> sfold_Expr_Expr findOpUses acc tm
  | TmOpVar x -> snoc acc x
  | TmOpImpl x -> errorSingle [x.info]
    "This impl is nested within another impl, which the current solver doesn't handle."

  -- Insert selected solutions --
  type ConcreteState =
    { remainingSolutions : [SolverSolution Expr]
    -- NOTE(vipa, 2023-10-25): ImplId is set up in such a way that the
    -- most recent impl to be added is the largest, i.e., we can find
    -- the insertion point of a concrete solution by inserting it by
    -- the greatest `ImplId` used in the solution
    , requests : Map ImplId [{op : Name, solName : Name, token : Expr, sols : [SolverSolution Expr]}]
    , requestsByOpAndSol : Map (Name, SolverSolution Expr) Name
    , global : SolverGlobal Expr
    }

  sem lookupSolName : Name -> SolverSolution Expr -> ConcreteState -> (ConcreteState, Name)
  sem lookupSolName op sol = | state ->
    match mapLookup (op, sol) state.requestsByOpAndSol
    with Some name then (state, name) else
      let name = nameSetNewSym op in
      match concretizeSolution state.global sol with (token, implId, sols) in
      let requestsByOpAndSol = mapInsert (op, sol) name state.requestsByOpAndSol in
      let requests = mapInsertWith concat
        implId
        [{op = op, solName = name, token = token, sols = sols}]
        state.requests in
      ({ state with requestsByOpAndSol = requestsByOpAndSol, requests = requests }, name)

  sem concretizeAlt : ConcreteState -> Expr -> (ConcreteState, Expr)
  sem concretizeAlt state =
  | tm -> smapAccumL_Expr_Expr concretizeAlt state tm
  | TmOpDecl {inexpr = inexpr} | TmReprDecl {inexpr = inexpr} ->
    concretizeAlt state inexpr
  | TmOpVar x ->
    match state.remainingSolutions with [sol] ++ remainingSolutions in
    match lookupSolName x.ident sol state with (state, name) in
    let state = {state with remainingSolutions = remainingSolutions} in
    ( {state with remainingSolutions = remainingSolutions}
    , TmVar {ident = name, ty = x.ty, info = x.info, frozen = x.frozen}
    )
  | TmOpImpl x ->
    match concretizeAlt state x.inexpr with (state, inexpr) in
    recursive let work = lam acc.
      match mapLookup x.implId acc.state.requests with Some reqs then
        let acc = {acc with state = {acc.state with requests = mapRemove x.implId acc.state.requests}} in
        let f = lam acc. lam req.
          match concretizeAlt {acc.state with remainingSolutions = req.sols} req.token
          with (state, body) in
          let inexpr = TmLet
            { ident = req.solName
            , tyAnnot = tyTm body
            , tyBody = tyTm body
            , body = body
            , inexpr = inexpr
            , ty = tyTm inexpr
            , info = x.info
            } in
          {state = state, inexpr = inexpr}
        in work (foldl f acc reqs)
      else acc in
    match work {state = state, inexpr = inexpr}
    with {state = newState, inexpr = tm} in
    ({newState with remainingSolutions = state.remainingSolutions}, tm)

  -- TODO(vipa, 2023-07-07): This swaps all `TyRepr`s with
  -- `TyUnknown`. This *should* be good enough for the OCaml backend,
  -- but isn't as good as it could be; we should be able to insert
  -- precise types according to what reprs were chosen. I leave that
  -- for later.
  sem removeReprExpr : Expr -> Expr
  sem removeReprExpr = | tm ->
    let tm = smap_Expr_Expr removeReprExpr tm in
    let tm = smap_Expr_Type removeReprTypes tm in
    let tm = smap_Expr_TypeLabel removeReprTypes tm in
    tm

  sem removeReprTypes : Type -> Type
  sem removeReprTypes =
  | ty -> smap_Type_Type removeReprTypes ty
  -- NOTE(vipa, 2023-10-26): Aliases can contain TyRepr in `content`
  -- without showing them in `display`, at which point it gets
  -- confusing if we keep the same alias, even though the content is
  -- different from the type alias definition suggests it is.
  | TyAlias x -> removeReprTypes x.content
  | TyRepr x -> TyUnknown {info = x.info}
end

lang EagerRepSolver = RepTypesShallowSolverInterface + UnifyPure + RepTypesHelpers + Generalize
  type SolId = Int
  type SolContent a =
    { token : a
    , cost : OpCost
    , uni : Unification
    , specType : Type
    , highestImpl : ImplId
    , subSols : [SolId]
    }
  type SBContent a =
    { implsPerOp : Map Name (Set (OpImpl a))
    , nextSolId : SolId
    , solsById : Map SolId (SolContent a)
    , solsByOp : Map Name (Set SolId)
    }
  syn SolverGlobal a = | SGContent ()
  syn SolverBranch a = | SBContent (SBContent a)
  syn SolverSolution a = | SSContent (SBContent a, SolId)

  sem initSolverGlobal = | _ -> SGContent ()
  sem initSolverBranch = | global -> SBContent
    { implsPerOp = mapEmpty nameCmp
    , nextSolId = 0
    , solsById = mapEmpty subi
    , solsByOp = mapEmpty nameCmp
    }

  sem topSolve global = | opUses ->
    -- TODO(vipa, 2023-10-26): Port solveViaModel and use it here if we have a large problem
    let mergeOpt = lam prev. lam sol.
      match mergeUnifications prev.uni sol.uni with Some uni then Some
        { uni = uni
        , cost = addf prev.cost sol.cost
        , sols = snoc prev.sols sol.sol
        }
      else None () in
    let f = lam prev. lam sols.
      filterOption (seqLiftA2 mergeOpt prev sols) in
    let sols = foldl f [{uni = emptyUnification (), cost = 0.0, sols = []}] opUses in
    match sols with [sol] ++ sols then
      (foldl (lam sol. lam sol2. if ltf sol2.cost sol.cost then sol2 else sol) sol sols).sols
    else errorSingle [] "Could not pick implementations for all operations."

  sem allSolutions global branch name = | ty ->
    match branch with SBContent branch in
    let solIds = mapLookupOr (setEmpty subi) name branch.solsByOp in
    let checkAndAddSolution = lam acc. lam solId.
      let content = mapFindExn solId branch.solsById in
      match unifyPure content.uni ty (inst (NoInfo ()) 0 (removeReprSubsts content.specType))
      with Some uni then snoc acc
        { sol = SSContent (branch, solId)
        , cost = content.cost
        , uni = uni
        }
      else acc in
    (SBContent branch, setFold checkAndAddSolution [] solIds)

  sem concretizeSolution global =
  | SSContent (branch, solId) ->
    let content = mapFindExn solId branch.solsById in
    (content.token, content.highestImpl, map (lam solId. SSContent (branch, solId)) content.subSols)

  sem cmpSolution a = | b -> match (a, b) with (SSContent a, SSContent b) in subi a.1 b.1

  -- NOTE(vipa, 2023-10-26): This is the real work of this solver;
  -- here we record all impls available, and compute and store all
  -- optimal solutions for distinct `uni`s. Think of it like a datalog
  -- store, one table per `op`, one row per solution, where each
  -- `impl` is a rule for creating new solutions from previous ones.

  sem addImpl global branch = | opImpl ->
    let start = wallTimeMs () in
    match branch with SBContent branch in
    let branch = {branch with implsPerOp = mapInsertWith setUnion
      opImpl.op
      (setEmpty (lam a. lam b. subi a.implId b.implId))
      branch.implsPerOp} in

    -- NOTE(vipa, 2023-10-26): Find new solutions directly due to the
    -- new impl
    let getPossibleSolutions = lam opUse. lam.
      let solIds = optionMapOr [] setToSeq (mapLookup opUse.ident branch.solsByOp) in
      (map (lam solId. (solId, mapFindExn solId branch.solsById)) solIds, ()) in
    let newSols = mkSols opImpl getPossibleSolutions () in
    let branch = foldl (addSol opImpl.op) branch newSols in

    let duration = subf (wallTimeMs ()) start in
    printError (join ["INFO", info2str opImpl.info, ": updated reptype solution closure, took ", float2string duration, "ms\n"]);
    flushStderr ();

    SBContent branch

  sem mkSols : all a. all x. OpImpl a -> (TmOpVarRec -> x -> ([(SolId, SolContent a)], x)) -> x -> [SolContent a]
  sem mkSols opImpl getAlts = | x ->
    let emptySol =
      { token = opImpl.token
      , cost = opImpl.selfCost
      , uni = opImpl.uni
      , specType = opImpl.specType
      , highestImpl = opImpl.implId
      , maxInnerCost = negf 1.0
      , subSols = []
      } in
    let mergeOpt = lam opUse. lam prev. lam pair.
      match pair with (solId, candidate) in
      let oUni = optionBind
        (unifyPure prev.uni opUse.ty (inst (NoInfo ()) opImpl.metaLevel (removeReprSubsts candidate.specType)))
        (mergeUnifications candidate.uni) in
      let mkNext = lam uni.
        { prev with uni = uni
        , highestImpl = maxi prev.highestImpl candidate.highestImpl
        , cost = addf prev.cost (mulf opUse.scaling candidate.cost)
        , maxInnerCost = maxf prev.maxInnerCost candidate.cost
        , subSols = snoc prev.subSols solId
        } in
      optionMap mkNext oUni
    in
    let f = lam acc. lam opUse.
      if null acc.0 then acc else
      match getAlts opUse acc.1 with (solOptions, newX) in
      let sols = filterOption (seqLiftA2 (mergeOpt opUse) acc.0 solOptions) in
      (sols, newX) in
    let sols = (foldl f ([emptySol], x) opImpl.opUses).0 in
    let checkCostIncrease = lam sol.
      if leqf sol.cost sol.maxInnerCost then
        errorSingle [opImpl.info] "The final cost of an implementation must be greater than the cost of each of its constituent operations."
      else
        { token = sol.token
        , cost = sol.cost
        , uni = sol.uni
        , specType = sol.specType
        , highestImpl = sol.highestImpl
        , subSols = sol.subSols
        } in
    map checkCostIncrease sols

  sem addSol : all a. Name -> SBContent a -> SolContent a -> SBContent a
  sem addSol op branch = | sol ->
    -- NOTE(vipa, 2023-10-26): Ensure that we have a minimal-ish set
    -- of solutions; no solution may be worse than another (more
    -- restrictive `uni` and higher cost).
    let solIds = mapLookupOr (setEmpty subi) op branch.solsByOp in
    let check = lam acc : Option (Set SolId). lam solId.
      match acc with Some toPrune then
        let oldSol = mapFindExn solId branch.solsById in
        let newIsCheaper = gtf oldSol.cost sol.cost in
        let oldFitsWhereNewCouldBe = uniImplies sol.uni oldSol.uni in
        let existenceDenied = and (not newIsCheaper) oldFitsWhereNewCouldBe in
        -- NOTE(vipa, 2023-10-26): It *should* be the case that
        -- `existenceDenied` implies `setIsEmpty toPrune`
        if existenceDenied then None () else
        let newFitsWhereOldCouldBe = uniImplies oldSol.uni sol.uni in
        let oldShouldBePruned = and newIsCheaper newFitsWhereOldCouldBe in
        Some (if oldShouldBePruned then setInsert solId toPrune else toPrune)
      else acc in
    match setFold check (Some (setEmpty subi)) solIds with Some toPrune then
      let newSolId = branch.nextSolId in
      let branch =
        { branch with nextSolId = addi branch.nextSolId 1
        , solsByOp = mapInsert op (setInsert newSolId (setSubtract solIds toPrune)) branch.solsByOp
        , solsById = mapInsert newSolId sol (mapDifference branch.solsById toPrune)
        } in
      -- NOTE(vipa, 2023-10-26): At this point there may be `subSols`
      -- referencing solutions not present in `solsById`. These will
      -- be replaced by some of the solutions we produce now, since
      -- `sol` is strictly better than whatever they were referencing
      -- before
      let foldImpls : all acc. (acc -> OpImpl a -> acc) -> acc -> acc = lam f. lam acc. mapFoldWithKey
        (lam acc. lam. lam impls. setFold f acc impls)
        acc
        branch.implsPerOp in
      let addSolsFromImpl = lam branch. lam impl.
        let newPatterns = tail
          -- NOTE(vipa, 2023-10-26): The first sequence in the list is
          -- the one with all false, i.e., "use only old solutions",
          -- which won't come up with anything new
          (seqMapM (lam opUse. if nameEq opUse.ident op then [false, true] else [false]) impl.opUses) in
        let processPattern = lam branch. lam pattern.
          let getPossibleSolutions = lam opUse. lam pattern.
            match pattern with [useNew] ++ pattern in
            if useNew then ([(newSolId, sol)], pattern) else
            let solIds = optionMapOr [] setToSeq (mapLookup opUse.ident branch.solsByOp) in
            let pairs = map (lam solId. (solId, mapFindExn solId branch.solsById)) solIds in
            (pairs, pattern) in
          let newSols = mkSols impl getPossibleSolutions pattern in
          foldl (addSol impl.op) branch newSols in
        foldl processPattern branch newPatterns
      in
      foldImpls addSolsFromImpl branch
    else branch
end

-- lang RepTypesSolveWithExhaustiveCP = RepTypesSolverInterface + UnifyPure + COPHighLevel + ReprSubstAst + RepTypesHelpers + Generalize
--   syn SolverState =
--   | CPState ()
--   sem initSolverState = | _ -> CPState ()

--   type CPSol a =
--     { cost : OpCost
--     , specType : Type
--     , uni : Unification
--     , innerSolutions : [OpImplSolution a]
--     , idx : Int
--     , token : a
--     }

--   syn OpImplSolutionSet a =
--   | CPSolutionSet (Promise [CPSol a])

--   syn OpImplSolution a =
--   | CPSolution (CPSol a)

--   sem cmpSolution a = | b ->
--     match (a, b) with (CPSolution a, CPSolution b) in
--     subi a.idx b.idx

--   sem solveOne st prev = | alts ->
--     match prev with Some _ then
--       errorSingle [] "[panic] The cp-based RepTypes solver currently assumes all opimpls are merged into one op-impl"
--     else
--     let promise = promiseMkThread_ (lam.
--       let f = lam alt.
--         -- NOTE(vipa, 2023-08-11): Move delayedReprUnifications to
--         -- the root unification
--         let uni = optionFoldlM
--           (lam acc. lam pair. unifyReprPure acc pair.0 pair.1)
--           (emptyUnification ())
--           alt.delayedReprUnifications in

--         -- NOTE(vipa, 2023-08-11): Pull substitutions from the
--         -- type-signature and add to uni
--         recursive let applySubsts = lam oUni. lam ty.
--           let oUni =
--             match ty with TySubst {arg = arg, subst = subst, info = info} then
--               match unwrapType arg with TyRepr {repr = r} then
--                 optionBind oUni (lam uni. unifySetReprPure uni r subst)
--               else errorSingle [info] "This substitution seems to be applied to a non-repr type"
--             else oUni in
--           match ty with TyAlias x then applySubsts oUni x.content else
--           sfold_Type_Type applySubsts oUni ty in
--         let uni = match applySubsts uni alt.specType
--           with Some x then x
--           else errorSingle [alt.info] (strJoin "\n"
--             [ "This impl makes conflicting substitutions of a repr"
--             , "and is thus never valid, regardless of what other"
--             , "implementations are available."
--             ]) in

--         -- NOTE(vipa, 2023-08-11): Collect ReprVar's and MetaVar's
--         -- that are in the type signature of the alt, which are thus
--         -- externally visible even though their reprScope might be in
--         -- the current alt or further down.
--         let uniFilter =
--           let signatureReprs : Set Symbol = foldl
--             (lam acc. lam repr. setInsert (match deref (botRepr repr) with BotRepr x in x.sym) acc)
--             (setEmpty (lam a. lam b. subi (sym2hash a) (sym2hash b)))
--             (findReprs [] alt.specType) in
--           let signatureMetas : Set Name =
--             recursive let work = lam acc. lam ty.
--               let ty = unwrapType ty in
--               match ty with TyMetaVar x then
--                 match deref x.contents with Unbound x in
--                 setInsert x.ident acc
--               else sfold_Type_Type work acc ty
--             in work (setEmpty nameCmp) alt.specType in
--           { reprs =
--             { scope = alt.reprScope
--             , syms = signatureReprs
--             }
--           , types =
--             { level = alt.metaLevel
--             , names = signatureMetas
--             }
--           } in

--         -- NOTE(vipa, 2023-08-11): Go through the opUses and filter
--         -- out alternatives that cannot be relevant for this impl
--         let f = lam idx. lam opUse.
--           let f = lam sol.
--             let solUni = unifyPure sol.uni opUse.app.ty (inst alt.info alt.metaLevel (removeReprSubsts sol.specType)) in
--             let solUni = optionAnd
--               solUni
--               (optionBind solUni (mergeUnifications uni)) in
--             optionMap
--               (lam uni. {sol with uni = uni})
--               solUni
--           in
--           let solutionSet = match opUse.solutionSet with CPSolutionSet prom in promiseForce prom in
--           { app = opUse.app
--           , solutionSet = mapOption f solutionSet
--           , idxes = setInsert idx (setEmpty subi)
--           }
--         in
--         let opUses = mapi f alt.opUses in
--         if any (lam opUse. null opUse.solutionSet) opUses then
--           -- TODO(vipa, 2023-10-10): For now we print an error/warning
--           -- when this happens, because it's likely to be unintended,
--           -- but later it might be a result of business as usual, so
--           -- that might change
--           printError (join [info2str alt.info, ": an op-use has no viable alternatives, thus this alt is dead.\n"]);
--           flushStderr ();
--           []
--         else

--         -- TODO(vipa, 2023-08-11): This is the place to insert
--         -- deduplication of opUses, by merging them and doing
--         -- `setUnion` on the `idxes` field. ReprVars that are merged
--         -- during deduplication should be unified via `uni`

--         let solutions =
--           let problem = {alt = alt, uni = uni, uniFilter = uniFilter, opUses = opUses} in
--           let size = foldl (lam acc. lam opUse. muli acc (length opUse.solutionSet)) 1 opUses in

--           -- NOTE(vipa, 2023-10-23): Always run enum, which tends to
--           -- be (much) faster, but behaves much worse in the worst
--           -- case
--           -- let startT = wallTimeMs () in
--           -- let res = solveViaEnumeration problem in
--           -- let time = subf (wallTimeMs ()) startT in
--           -- printError (join ["Alt solve complete, size, took: ", float2string time, "ms\n"]);
--           -- flushStderr ();

--           -- NOTE(vipa, 2023-10-23): Run one depending on the maximum size of the problem
--           let startT = wallTimeMs () in
--           let res = if lti size 400
--             then solveViaEnumeration problem
--             else solveViaModel problem in
--           let time = subf (wallTimeMs ()) startT in
--           printError (join ["Alt solve complete, size, took: ", float2string time, "ms\n"]);
--           flushStderr ();

--           -- NOTE(vipa, 2023-10-23): Run both, for profiling/timing information
--           -- let startT = wallTimeMs () in
--           -- let res = solveViaEnumeration problem in
--           -- let enumTime = subf (wallTimeMs ()) startT in
--           -- let startT = wallTimeMs () in
--           -- let res = solveViaModel problem in
--           -- let modelTime = subf (wallTimeMs ()) startT in
--           -- printError (join ["Alt solve complete, size: ", int2string size, ", enum took: ", float2string enumTime, "ms, model took: ", float2string modelTime, "\n"]);
--           -- flushStderr ();

--           res
--         in solutions
--       in mapi (lam idx. lam sol. {sol with idx = idx}) (join (map f alts))
--     ) in CPSolutionSet promise

--   type ReprProblem a =
--     { alt : RepTypesProblemAlt a
--     , uni : Unification
--     , uniFilter : {reprs : {scope : Int, syms : Set Symbol}, types : {level : Int, names : Set Name}}
--     , opUses : [{app: TmOpVarRec, idxes: Set Int, solutionSet: [CPSol a]}]
--     }

--   sem solveViaEnumeration : all a. ReprProblem a -> [CPSol a]
--   sem solveViaEnumeration = | problem ->
--     match problem with {alt = alt, uni = uni, uniFilter = uniFilter, opUses = opUses} in
--     printError (join ["Starting to solve exhaustively, size: ", strJoin "*" (map (lam opUse. int2string (length opUse.solutionSet)) opUses), "\n"]);
--     flushStderr ();
--     type Sol = {uni : Unification, cost : OpCost, innerSolutions : Map Int (OpImplSolution a)} in
--     let applySol : TmOpVarRec -> Set Int -> Sol -> CPSol a -> Option Sol = lam app. lam idxes. lam sol. lam new.
--       match mergeUnifications sol.uni new.uni with Some uni then Some
--         { uni = uni
--         , cost = addf sol.cost (mulf (int2float (setSize idxes)) (mulf app.scaling new.cost))
--         , innerSolutions = mapUnion sol.innerSolutions (mapMap (lam. CPSolution new) idxes)
--         }
--       else None ()
--     in
--     let sols = foldl
--       (lam acc. lam opUse. filterOption (seqLiftA2 (applySol opUse.app opUse.idxes) acc opUse.solutionSet))
--       [{uni = uni, innerSolutions = mapEmpty subi, cost = 0.0}]
--       opUses in
--     let mkCPSol = lam sol.
--       { cost = sol.cost
--       , specType = alt.specType
--       , uni = filterUnification uniFilter sol.uni
--       , innerSolutions = mapValues sol.innerSolutions
--       , idx = 0  -- NOTE(vipa, 2023-10-19): Updated later, to be unique across all alts
--       , token = alt.token
--       } in
--     let solutions = map mkCPSol sols in
--     -- TODO(vipa, 2023-10-19): Definitely want to filter out solutions
--     -- that are covered (they look the same from the outside as some
--     -- other solution, and the cost is higher)
--     (if null solutions
--      then warnSingle [alt.info] "Found no solutions for alt (exhaustive solve)."
--      else ());
--     mapi (lam i. lam sol. {sol with idx = i}) solutions

--   sem solveViaModel : all a. ReprProblem a -> [CPSol a]
--   sem solveViaModel = | problem ->
--     match problem with {alt = alt, uni = uni, uniFilter = uniFilter, opUses = opUses} in
--     printError (join ["Starting to construct model, size: ", strJoin "*" (map (lam opUse. int2string (length opUse.solutionSet)) opUses), "\n"]);
--     flushStderr ();
--     let m = newModel () in
--     let cmpSol = lam a. lam b. subi a.idx b.idx in
--     let reprTy = m.newEnumType nameCmp in
--     let getReprSymVar : Symbol -> COPExpr =
--       let reprMap : Ref (Map Symbol COPExpr) = ref (mapEmpty (lam a. lam b. subi (sym2hash a) (sym2hash b))) in
--       let newReprVar = lam sym.
--         let expr = m.var (m.newVar reprTy "repr") in
--         modref reprMap (mapInsert sym expr (deref reprMap));
--         expr in
--       lam sym. mapLookupOrElse (lam. newReprVar sym) sym (deref reprMap) in
--     let uniToPredicate = lam localUni.
--       let localReprs = localUni.reprs in
--       let reprs = uni.reprs in
--       let mkEq = lam repr.
--         let l = eitherMapRight (lam x. x.0)
--           (pufUnwrap reprs (repr, negi 1)) in
--         let r = eitherMapRight (lam x. x.0)
--           (eitherBindRight (pufUnwrap localReprs (repr, negi 1)) (pufUnwrap reprs)) in
--         if eitherEq nameEq eqsym l r then None () else
--         let toCOPExpr = eitherEither (m.enum reprTy) getReprSymVar in
--         Some (m.eq (toCOPExpr l) (toCOPExpr r)) in
--       m.andMany (mapOption mkEq (mapKeys localReprs))
--     in
--     let cost : Ref [COPExpr] = ref [m.float alt.selfCost] in
--     let addCost : COPExpr -> () = lam c. modref cost (snoc (deref cost) c) in
--     let useToVar = lam opUse.
--       let ident = opUse.app.ident in
--       let opTy = m.newEnumType cmpSol in
--       m.registerValues opTy (setOfSeq cmpSol opUse.solutionSet);
--       let var = m.newVar opTy (nameGetStr ident) in
--       -- NOTE(vipa, 2023-08-16): `uniMapToPredicate` may create
--       -- new repr-vars as a side-effect, and since elimEnum is
--       -- lazy and might run too late we pre-run it here to
--       -- ensure the reprs are created.
--       iter (lam sol. uniToPredicate sol.uni; ()) opUse.solutionSet;
--       m.newConstraint (m.elimEnum opTy (m.var var) (lam sol. uniToPredicate sol.uni));
--       addCost (m.elimEnum opTy (m.var var) (lam sol. m.float (mulf opUse.app.scaling sol.cost)));
--       (opUse.idxes, var, opTy) in
--     let vars = map useToVar opUses in
--     -- NOTE(vipa, 2023-10-10): This undoes any deduplication
--     -- done previously, using the `idxes` set.
--     let orderedVars = mapValues (foldl
--       (lam acc. lam var. mapUnion acc (mapMap (lam. var.1) var.0))
--       (mapEmpty subi)
--       vars) in
--     let cost = m.addMany (deref cost) in
--     recursive let work = lam prevSolutions.
--       if gti (length prevSolutions) 20 then
--         errorSingle [alt.info] (join ["Found a surprising number of solutions for alt (more than 20, should be reasonable later on, but in early testing it's mostly been caused by bugs). Final model:\n", m.debugModel (), "\n"])
--       else
--       switch m.minimize cost
--       case COPSolution {objective = Some (COPFloat {val = cost})} then
--         -- NOTE(vipa, 2023-10-10): The translation to a
--         -- constraint model isn't perfect: we don't model type
--         -- constraints. By merging all the Unification's we
--         -- check that the combination actually type-checks,
--         -- i.e., it's a valid solution.
--         let combinedUni = optionFoldlM
--           (lam acc. lam var. mergeUnifications acc (m.readVar var.1).uni)
--           -- NOTE(vipa, 2023-10-10): We start from an empty
--           -- unification, not `uni`, since the latter might
--           -- introduce more variables to the model, which can
--           -- make us loop forever.
--           (emptyUnification ())
--           vars in
--         let combinedUni = optionMap (filterUnification uniFilter) combinedUni in
--         match (combinedUni, optionBind combinedUni (lam x. mergeUnifications x uni))
--         with (Some localExternallyVisibleUni, Some uni) then
--           printError ".";  -- TODO(vipa, 2023-10-22): Remove
--           flushStderr ();
--           -- NOTE(vipa, 2023-08-18): Assert that any later
--           -- solution must differ from this one in some externally
--           -- visible way
--           m.newConstraint (m.not (uniToPredicate localExternallyVisibleUni));
--           let sol =
--             { cost = cost
--             , specType = alt.specType
--             , uni = uni
--             , innerSolutions = map (lam v. CPSolution (m.readVar v)) orderedVars
--             , idx = 0  -- NOTE(vipa, 2023-10-10): Updated later, to be unique across all alts
--             , token = alt.token
--             }
--           in work (snoc prevSolutions sol)
--         else
--           printError "?";  -- TODO(vipa, 2023-10-22): Remove
--           flushStderr ();
--           -- NOTE(vipa, 2023-10-10): The chosen implementations
--           -- do not type-check together. We need to rule out
--           -- this particular combination, then find another
--           -- solution.

--           -- NOTE(vipa, 2023-10-10): Most likely it's just a
--           -- *subset* of the implementations that don't mesh. As
--           -- an approximation of this set, we merge the `uni`s
--           -- of the `vars` until we fail, then assert that at
--           -- least one of the seen `vars` must differ.
--           let vars =
--             recursive let work = lam checkedVars. lam uni. lam varPairs.
--               match varPairs with [(_, var, opTy)] ++ varPairs then
--                 let checkedVars = snoc checkedVars (m.eq (m.var var) (m.enum opTy (m.readVar var))) in
--                 match mergeUnifications uni (m.readVar var).uni with Some uni
--                 then work checkedVars uni varPairs
--                 else checkedVars
--               else error "Compiler error, there should be a unification failure somewhere"
--             in work [] uni vars in
--           m.newConstraint (m.not (m.andMany vars));
--           work prevSolutions
--       case COPUnsat _ then
--         printError "!";  -- TODO(vipa, 2023-10-22): Remove
--         flushStderr ();
--         (if null prevSolutions then
--            warnSingle [alt.info] (join ["Found no solutions for alt. Final model:\n", m.debugModel (), "\n"])
--          else
--            printError (join ["solutions: ", int2string (length prevSolutions), ", info: ", info2str alt.info, "\n"]);
--            flushStderr ());
--         prevSolutions
--       case COPError x then
--         errorSingle [alt.info] (concat "CP-solver error during RepTypes solving:\n" x.msg)
--       end
--     in work []

--   sem concretizeSolution =
--   | CPSolution sol -> (sol.token, sol.innerSolutions)

--   sem cheapestSolution =
--   | CPSolutionSet promise ->
--     let forced = promiseForce promise in
--     CPSolution (minOrElse (lam. errorSingle [] "Couldn't put together a complete program, see earlier warnings about possible reasons.") (lam a. lam b. cmpfApprox 1.0 a.cost b.cost) forced)
-- end

lang RepTypesComposedSolver = RepTypesSolveAndReconstruct + EagerRepSolver + MExprUnify
end

lang DumpRepTypesProblem = RepTypesFragments
  sem dumpRepTypesProblem : String -> Expr -> ()
  sem dumpRepTypesProblem path = | tm ->
    let lines = ref [] in
    dumpRepTypesProblemRoot (lam line. modref lines (snoc (deref lines) line)) 0 tm;
    writeFile path (strJoin "\n" (deref lines))

  sem dumpRepTypesProblemRoot : (String -> ()) -> Int -> Expr -> ()
  sem dumpRepTypesProblemRoot output reprScope = | tm ->
    let apps = dumpRepTypesProblemWork output [] tm in
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
      output (json2string json) in
    iteri appToLine apps

  sem dumpRepTypesProblemWork : (String -> ()) -> [(Name, Type)] -> Expr -> [(Name, Type)]
  sem dumpRepTypesProblemWork output acc =
  | TmOpVar x -> snoc acc (x.ident, x.ty)
  | TmOpImpl x ->
    dumpRepTypesProblemRoot output x.reprScope x.body;
    dumpRepTypesProblemWork output acc x.inexpr
  | tm -> sfold_Expr_Expr (dumpRepTypesProblemWork output) acc tm

  sem clearAndCollectReprs : [ReprVar] -> Type -> ([ReprVar], Type)
  sem clearAndCollectReprs reprs =
  | TyRepr x ->
    let reprs = snoc reprs x.repr in
    match clearAndCollectReprs reprs x.arg with (reprs, arg) in
    (reprs, TyRepr {x with repr = ref (UninitRepr ()), arg = arg})
  | ty -> smapAccumL_Type_Type clearAndCollectReprs reprs ty
end

lang PrintMostFrequentRepr = RepTypesFragments + MExprAst
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
    match unwrapType ty with TyRepr c then
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