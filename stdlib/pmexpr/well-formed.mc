-- Defines a well-formed relation on PMExpr expressions. A well-formed PMExpr
-- program can always be compiled into a valid Futhark program.

include "mexpr/ast.mc"
include "mexpr/type-annot.mc"
include "pmexpr/ast.mc"

lang WellFormed = MExprTypeAnnot
  sem wellFormed =
  | t -> wellFormedExpr 0 (mapEmpty nameCmp) t

  sem wellFormedExpr (accelerateFlag : Int) (typeEnv : Map Name Type) =
  | t -> infoErrorExit (infoTm t) "Term cannot be accelerated"
end

lang VarWellFormed = WellFormed + VarAst
  sem wellFormedExpr (accelerateFlag : Int) (typeEnv : Map Name Type) =
  | TmVar t ->
    match mapLookup t.ident typeEnv with Some ty then
      ty
    else infoErrorExit t.info "Variable not well-formed"
end

lang LamWellFormed = WellFormed + LamAst + FunTypeAst
  sem wellFormedExpr (accelerateFlag : Int) (typeEnv : Map Name Type) =
  | TmLam t ->
    let bodyTypeEnv = mapInsert t.ident t.tyIdent typeEnv in
    let tyBody = wellFormedExpr accelerateFlag bodyTypeEnv t.body in
    TyArrow {from = t.tyIdent, to = tyBody, info = infoTy t.ty}
end

lang LetWellFormed = WellFormed + LetAst
  sem wellFormedExpr (accelerateFlag : Int) (typeEnv : Map Name Type) =
  | TmLet t ->
    let tyBody = wellFormedExpr accelerateFlag typeEnv t.body in
    match compatibleType typeEnv tyBody t.tyBody with Some ty then
      let bodyTypeEnv = mapInsert t.ident ty typeEnv in
      wellFormedExpr accelerateFlag bodyTypeEnv t.inexpr
    else infoErrorExit t.info "Let-expression not well-formed"
end

lang AppWellFormed = WellFormed + AppAst
  sem wellFormedExpr (accelerateFlag : Int) (typeEnv : Map Name Type) =
  | TmApp t ->
    match wellFormedExpr accelerateFlag typeEnv t.lhs
    with TyArrow {from = t1, to = t2} then
      let rhsTy = wellFormedExpr accelerateFlag typeEnv t.rhs in
      match compatibleType typeEnv t1 rhsTy with Some _ then
        t2
      else never
    else never
end

lang RecordWellFormed = WellFormed + RecordAst + RecordTypeAst
  sem wellFormedExpr (accelerateFlag : Int) (typeEnv : Map Name Type) =
  | TmRecord t ->
    let bindTypes = mapMap (wellFormed typeEnv) t.bindings in
    let labels =
      match t.ty with TyRecord {labels = l} then l else mapKeys bindTypes
    in
    TyRecord {fields = bindTypes, labels = labels, info = infoTy t.ty}
end

lang SeqWellFormed = WellFormed + SeqAst
  -- NOTE(larshum, 2021-10-08): Can we have a known integer length here? For a
  -- sequence literal it works, but how can be compute the size of a sequence
  -- constructed at runtime?
  syn Type =
  | TySizedSeq {ty : Type, len : Int, info : Info}

  sem wellFormedExpr (accelerateFlag : Int) (typeEnv : Map Name Type) =
  | TmSeq t ->
    let elemTy =
      match optionFoldlM (compatibleType typeEnv) tyunknown_ t.tms with Some ty then
        ty
      else TyUnknown {info = infoTy t.ty}
    in
    match elemTy with TyArrow _ then
      infoErrorExit t.info "Sequences of functions cannot be accelerated"
    else
      let len = length t.tms in
      TySizedSeq {ty = elemTy, len = len, info = infoTy t.ty}
end

-- NOTE(larshum, 2021-10-08): This will not work, because at the point this
-- check runs, the accelerate terms have already been replaced. It is included
-- as an idea of what it would look like
lang AccelerateWellFormed = WellFormed + PMExprAst
  sem wellFormedExpr (accelerateFlag : Int) (typeEnv : Map Name Type) =
  | TmAccelerate t ->
    if eqi accelerateFlag 0 then
      let ty = wellFormedExpr 1 typeEnv t.e in
      match ty with TyRecord _ then
        infoErrorExit t.info "Accelerate expression cannot return a record"
      else
        -- NOTE(larshum, 2021-10-08): Here we would need to check that none of
        -- the free variables of 'e' have a record type, as these cannot be
        -- passed to the accelerated code.
        ty
    else
      infoErrorExit t.info "Nested accelerate terms are not supported"
end
