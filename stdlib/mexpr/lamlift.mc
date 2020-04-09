// Defines semantics for lambda lifting
// Based on the technique from the 1985 paper.
// (This will not handle partial application until a type-checker has been
// implemented.)

// This defines the lamlift semantics which, given a state tuple, propagates
// the entire AST and lifts out any internal lambda expressions to the top-
// level.

// This also defines the internal replace semantics which replaces all
// occurrences of an identifier with a specific expression. This is primarily
// used to replace the identifiers that are signalling a recursion.

// Algorithm for Let's (and anonymous lambdas):
// - Keep a track of all the arguments and variables (not defined functions)
// - When a Let expression has been fully scanned, check which variables that
//   where externally referenced. All the variables that were externally
//   referenced and are not part of the current lambda scope needs to be
//   generated as arguments for the current lambda as well. These arguments
//   will then be applied to the lifted lambda instead of the externally
//   referenced arguments.
// - For Let expressions in a recursive scope, identifiers will be replaced in
//   2 passes. After all the Let expressions have been scanned (just like in
//   the previous step), the generated identifiers potentionally need to be
//   replaced by a TmApp (..., ...) where the generated arguments are
//   pre-applied on the generated identifier for the Let expression.

// NOTE: Assumes that bound variables are limited to the following AST nodes:
//        - TmVar
//        - TmApp
//
// If an identifier is bound to a different node which itself contain
// identifiers, then this could lead to the lambda lifting returning an
// incorrect program even if the input program was correct.


include "ast.mc"
include "ast-builder.mc"
include "eval.mc"
include "pprint.mc"

include "option.mc"
include "seq.mc"
include "string.mc"


lang LamliftTypedVarAst = VarAst
    syn Expr =
    -- Only ever use for lookup, should never be used be part of the generated AST
    | TmLamliftTypedVar {ident : String,
                         tpe   : Option}
end

-- State for lambda lifting
--   id:         ID counter (used to assign globally unique names to
--               identifiers).
--   globaldefs: List of expressions that has been lifted out.
--   env:        The environment lookup of the current scope. Contains three
--               types of lookups: 1) env.evar for variables, 2) env.econ for
--               data constructs, and 3) env.etype for type names.
--   lambdarefs: Lookup of identifiers that are defined locally in the current
--               lambda expression (arguments and non-lambda let expressions).
--   externrefs: List of identifiers that have been referenced in the current
--               lambda scope, but are not locally part of the current lambda
--               scope.
--   genargs:    List of arguments that have been generated to take the place
--               of the externally referenced identifiers.
type LiftState = {id         : Int,
                  globaldefs : [Expr],
                  env        : {evar  : [{key   : String,
                                         value : Expr}],
                                econ  : [{key   : String,
                                          value : Expr}],
                                etype : [{key   : String,
                                          value : Expr}]},
                  conenv     : [{key   : String,
                                 value : Expr}],
                  lambdarefs : [{ident : String,
                                 body  : Expr}],
                  externrefs : [Expr],
                  genargs    : [{name   : String, -- original lookup name
                                 genarg : Expr}]}


-- LiftState update functions
let st_incrId: LiftState -> LiftState =
    lam st.
    {st with id = addi st.id 1}

let st_addGlobaldef: Expr -> LiftState -> LiftState =
    lam gd. lam st.
    {st with globaldefs = cons gd st.globaldefs}

let st_addVarToEnv: String -> Expr -> LiftState -> LiftState =
    lam key. lam value. lam st.
    {st with env = {st.env with evar = cons {key = key, value = value} st.env.evar}}

let st_addConToEnv: String -> Expr -> LiftState -> LiftState =
    lam key. lam value. lam st.
    {st with env = {st.env with econ = cons {key = key, value = value} st.env.econ}}

let st_addTypeToEnv: String -> Expr -> LiftState -> LiftState =
    lam key. lam value. lam st.
    {st with env = {st.env with etype = cons {key = key, value = value} st.env.etype}}

let st_addLambdaref: String -> Expr -> LiftState -> LiftState =
    lam ident. lam body. lam st.
    {st with lambdarefs = cons {ident = ident, body = body} st.lambdarefs}

let st_addExternref: Expr -> LiftState -> LiftState =
    lam er. lam st.
    {st with externrefs = cons er st.externrefs}

let st_addGenarg: String -> Expr -> LiftState -> LiftState =
    lam name. lam genarg. lam st.
    {st with genargs = cons {name = name, genarg = genarg} st.genargs}

-- Adds generated arguments that are not in current environment.
-- usage: st_addGenargsToEnv <state with genargs> <state without genargs> <state with environment to update>
let st_addGenargsToEnv: LiftState -> LiftState -> LiftState =
    use LamliftTypedVarAst in
    lam st_w_genargs. lam st_wo_genargs. lam st.
    let genarg_diff_count = subi (length st_w_genargs.genargs) (length st_wo_genargs.genargs) in
    if gti genarg_diff_count 0 then
      foldl (lam acc. lam e.
        match e.genarg with TmLamliftTypedVar x then
          st_addVarToEnv e.name (TmVar {ident = x.ident}) acc
        else
          let _ = dprint e in
          let _ = print "\n" in
          error "st_addGenargsToEnv: Generated argument above was expected to be TmLamliftTypedVar"
      ) st (slice st_w_genargs.genargs 0 genarg_diff_count)
    else
      st

-- Returns whether the string is available in the current lambda scope
let st_inLambdaScope: String -> LiftState -> Bool =
    lam s. lam st.
    any (lam e. eqstr s e.ident) st.lambdarefs

-- Strips away prefix of string if it exists
let strip_prefix = lam s.
    recursive
        let strip_prefix_helper = lam tailstr.
        if null tailstr
        then s -- String has no prefix
        else if eqchar '_' (head tailstr)
             then tail tailstr
             else strip_prefix_helper (tail tailstr)
    in
    strip_prefix_helper s

---//-------------\\---
--<<-- LANGUAGES -->>--
---\\-------------//---

lang VarLamlift = LamliftTypedVarAst + VarAst + AppAst + LetAst + RecLetsAst + DataAst
    sem lamlift (state : LiftState) =
    | TmVar x ->
      -- Returns whether the String is globally defined in the LiftState
      let st_isGloballyDefined: String -> LiftState -> Bool =
          lam s. lam st.
          let tdsm = lam td. -- tdsm: TopDefStringMatch
              match td with TmLet t then
                  eqstr t.ident s
              else match td with TmRecLets t then
                  any (lam rec. eqstr rec.ident s) t.bindings
              else match td with TmConDef t then
                  eqstr t.ident s
              else
                  error "Global define is not TmLet, TmRecLets, or TmConDef"
          in
          any tdsm st.globaldefs
      in
      let ret = find (lam e. eqstr (e.key) x.ident) state.env.evar in
      match ret with Some t then
        -- Function that for all variables in an expression, that they are in
        -- the current scope.
        recursive let check_scope = lam chkstate. lam e.
          match e with TmVar t1 then
            -- If the found variable is in the current lambda scope or in the
            -- global scope, then it is no need to generate an argument for it.
            if or (st_inLambdaScope t1.ident chkstate) (st_isGloballyDefined t1.ident chkstate) then
              (chkstate, e)
            else
              -- Referenced something outside of our scope, generate argument for it.
              let id = chkstate.id in
              -- All bound identifiers should have either "var", "fun", or "arg"
              -- as a prefix.
              let oldname = strip_prefix t1.ident in
              let newname = concat "arg" (concat (int2string id) (cons '_' oldname)) in
              let newvar = TmVar {ident = newname} in
              let newtypedvar = TmLamliftTypedVar {ident = newname, tpe = None ()} in
              let newstate = st_incrId (st_addVarToEnv oldname newtypedvar
                                       (st_addLambdaref newname newtypedvar
                                       (st_addExternref e
                                       (st_addGenarg oldname newtypedvar chkstate)))) in
              (newstate, newvar)
          else match e with TmLamliftTypedVar t2 then
            -- If the found variable is in the current lambda scope or in the
            -- global scope, then it is no need to generate an argument for it.
            if or (st_inLambdaScope t2.ident chkstate) (st_isGloballyDefined t2.ident chkstate) then
              (chkstate, TmVar {ident = t2.ident})
            else
              -- Referenced something outside of our scope, generate argument for it.
              let id = chkstate.id in
              -- All bound identifiers should have either "var", "fun", or "arg"
              -- as a prefix.
              let oldname = strip_prefix t2.ident in
              let newname = concat "arg" (concat (int2string id) (cons '_' oldname)) in
              let newvar = TmVar {ident = newname} in
              let newtypedvar = TmLamliftTypedVar {t2 with ident = newname} in
              let newstate = st_incrId (st_addVarToEnv oldname newtypedvar
                                       (st_addLambdaref newname newtypedvar
                                       (st_addExternref (TmVar {ident = t2.ident})
                                       (st_addGenarg oldname newtypedvar chkstate)))) in
              (newstate, newvar)
          else match e with TmApp t3 then
            -- Our bound identifier references to a chain of applications, make
            -- that all identifiers in that application are in the current scope.
            let lhsret = check_scope chkstate t3.lhs in
            let lhsstate = lhsret.0 in
            let rhsret = check_scope lhsstate t3.rhs in
            let rhsstate = rhsret.0 in
            (rhsstate, TmApp {{t3 with lhs = lhsret.1} with rhs = rhsret.1})
          else
            (chkstate, e)
        in
        check_scope state t.value
      else
        error (concat "Variable \"" (concat x.ident "\" not found."))

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmVar x ->
      recursive let find_replacement = lam l.
        if null l then
          TmVar x
        else
          let e = head l in -- e: (name, replacement)
          if eqstr x.ident e.ident then
            e.replacement
          else
            find_replacement (tail l)
      in
      find_replacement newnames
    -- Deliberately no check for TmLamliftTypedVar here as we expect it to not
    -- be part of the AST, making this act as a simple sanity check.
end

lang DataLamlift = VarAst + DataAst + ConstAst + UnitAst
    sem lamlift (state : LiftState) =
    | TmConDef t ->
      let newname = strJoin "" ["Con", int2string state.id, "_", t.ident] in

      let updatedstate = st_incrId (st_addConToEnv t.ident (TmConFun {ident = newname})
                                   (st_addGlobaldef (TmConDef {{t with ident = newname} with inexpr = TmConst {val = CUnit ()}}) state)) in

      lamlift updatedstate t.inexpr
    | TmConFun t ->
      let ret = find (lam e. eqstr (e.key) t.ident) state.env.econ in
      match ret with Some t1 then
        (state, t1.value)
      else
        (state, TmConFun t)

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmConDef t -> TmConDef {t with inexpr = lamliftReplaceIdentifiers newnames t.inexpr}
    | TmConFun t -> TmConFun t -- not necessary here as we should never have to replace identifiers
end

lang AppLamlift = AppAst
    sem lamlift (state : LiftState) =
    | TmApp t ->
      let lhsret = lamlift state t.lhs in
      let lhsstate = st_addGenargsToEnv lhsret.0 state {lhsret.0 with env = state.env} in
      let rhsret = lamlift lhsstate t.rhs in
      let rhsstate = st_addGenargsToEnv rhsret.0 state {rhsret.0 with env = state.env} in
      (rhsstate, TmApp {{t with lhs = lhsret.1} with rhs = rhsret.1})

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmApp t -> TmApp {{t with lhs = lamliftReplaceIdentifiers newnames t.lhs}
                           with rhs = lamliftReplaceIdentifiers newnames t.rhs}
end

lang FunLamlift = VarLamlift + FunAst + ConstAst + UnitAst
    syn Expr =
    | TmLamChain {body : Expr}

    sem lamlift (state : LiftState) =
    | TmLam t ->
      -- Encountered Lambda outside of a lambda chain, name this as fun#_anon
      let passed_state = {{{state with lambdarefs = []} with externrefs = []} with genargs = []} in
      let ret = lamlift passed_state (TmLamChain {body = TmLam t}) in

      let updatedstate = {{state with id = (ret.0).id} with globaldefs = (ret.0).globaldefs} in

      let id = updatedstate.id in
      let name = concat "fun" (concat (int2string id) "_anon") in

      -- The value to return: TmApp {... TmApp {lhs = TmVar {ident = "fun#_anon"}, rhs = Expr}, ...}
      let appargs = foldl (lam acc. lam e. TmApp {lhs = acc, rhs = e}) (TmVar {ident = name}) (ret.0).externrefs in

      -- The top level definition: TmLet {ident = "fun#_anon", tpe = ..., body = TmLam {ident = "arg#_%%", tpe = None (), ...}}
      let lambdagenerator = lam e. lam acc.
        match e.genarg with TmLamliftTypedVar t1 then
          TmLam {ident = t1.ident, tpe = t1.tpe, body = acc}
        else error "internal error (1)"
      in
      let topdefbody = foldr lambdagenerator ret.1 (ret.0).genargs in

      -- Increment the id counter and add the TopDef to globaldefs
      let newstate = st_incrId (st_addGlobaldef (TmLet {ident = name, tpe = None (), body = topdefbody, inexpr = TmConst {val = CUnit ()}}) updatedstate) in

      (newstate, appargs)

    | TmLamChain t ->
      match t.body with TmLam t1 then
        let newname = concat "arg" (concat (int2string state.id) (cons '_' (t1.ident))) in
        let arg = TmLamliftTypedVar {ident = newname, tpe = t1.tpe} in

        let newstate = st_incrId (st_addVarToEnv t1.ident arg (st_addLambdaref newname arg state)) in
        let ret = lamlift newstate (TmLamChain {body = t1.body}) in

        let retstate = {ret.0 with env = state.env} in
        let retbody = ret.1 in
        (retstate, TmLam {{t1 with ident = newname} with body = retbody})
      else
        lamlift state t.body

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmLam t -> TmLam {t with body = lamliftReplaceIdentifiers newnames t.body}
    -- Should never encounter a TmLamChain at this stage, so it is deliberately
    -- left out as a sanity check.
end

lang LetLamlift = VarLamlift + LetAst + FunLamlift + ConstAst + UnitAst
    sem lamlift (state : LiftState) =
    | TmLet t ->
      match t.body with TmLam t1 then
        -- Pass the current LiftState with cleared lambdarefs, externrefs, and
        -- generated args to the body expression.
        let passed_state = {{{state with lambdarefs = []} with externrefs = []} with genargs = []} in
        let ret = lamlift passed_state (TmLamChain {body = t.body}) in

        let updatedstate = {{state with id = (ret.0).id} with globaldefs = (ret.0).globaldefs} in

        -- Encountered a let-defined Lambda, name this as fun#_<name>
        let id = updatedstate.id in
        let newname = concat "fun" (concat (int2string id) (cons '_' t.ident)) in

        -- The value to bind: TmApp (... TmApp (TmVar "fun#_<name>", Expr), ...)
        let appargs = foldl (lam acc. lam e. TmApp {lhs = acc, rhs = e}) (TmVar {ident = newname}) (ret.0).externrefs in

        -- The top level definition: TmLet ("fun#_<name>", TmLam ("arg#_%%", None, ...))
        let lambdagenerator = lam e. lam acc.
          match e.genarg with TmLamliftTypedVar t2 then
            TmLam {ident = t2.ident, tpe = t2.tpe, body = acc}
          else error "internal error (2)"
        in
        let topdefbody = foldr lambdagenerator ret.1 (ret.0).genargs in
        let arrowgenerator = lam e. lam acc.
          match e.genarg with TmLamliftTypedVar t2 then
            match t2.tpe with Some t3 then
              match acc with Some t4 then
                Some (TyArrow {from = t3, to = t4})
              else None ()
            else None ()
          else error "LetLamlift: arrowgenerator: Generated argument is not TmLamliftTypedVar"
        in
        let topdeftype = foldr arrowgenerator t.tpe (ret.0).genargs in

        -- Increment the id counter, add the TopDefLamlift to globaldefs, and add the return type to scope
        let newstate = st_incrId (st_addGlobaldef (TmLet {{{{t with ident = newname}
                                                               with tpe = topdeftype}
                                                               with body = topdefbody}
                                                               with inexpr = TmConst {val = CUnit ()}})
                                 (st_addVarToEnv t.ident appargs updatedstate)) in

        -- LHS has been lifted out, evaluate RHS and return that
        lamlift newstate t.inexpr
      else
        -- Traverse the let body and extract everything from the returned state
        -- apart from the environment.
        let ret = lamlift state t.body in

        -- Since we are not going to lift this expression, include the generated arguments
        -- into the environment for the in-expression
        let updatedstate = st_addGenargsToEnv ret.0 state {ret.0 with env = state.env} in

        let id = updatedstate.id in
        let newname = concat "var" (concat (int2string id) (cons '_' t.ident)) in
        let newvar = TmLamliftTypedVar {ident = newname, tpe = t.tpe} in

        -- Increment ID counter, add the "original" variable t.ident to the
        -- environment, and mark this variable as referencable from the current
        -- lambda scope.
        let newstate = st_incrId (st_addVarToEnv t.ident newvar
                                 (st_addLambdaref newname newvar updatedstate)) in

        let inret = lamlift newstate t.inexpr in

        let inretstate = {inret.0 with env = state.env} in

        (inretstate, TmLet {{{t with ident = newname} with body = ret.1} with inexpr = inret.1})

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmLet t -> TmLet {{t with body = lamliftReplaceIdentifiers newnames t.body}
                           with inexpr = lamliftReplaceIdentifiers newnames t.inexpr}
end

-- Lambda lifting of mutually recursive functions
lang RecLetsLamlift = VarLamlift + RecLetsAst + FunLamlift + ConstAst + UnitAst
    sem lamlift (state : LiftState) =
    | TmRecLets t ->
      -- Check that all bound identifiers are unique
      let bound_names = map (lam e. e.ident) t.bindings in
      if any (lam s. neqi 1 (length (filter (eqstr s) bound_names))) bound_names
      then error "Name duplication in recursive expression"
      else -- continue

      -- Add all of the binding identifiers to the current scope
      --   acc.0: The state that is being updated.
      --   acc.1: The let-bindings with updated names.
      --   acc.2: Lambda-reference list that contains all mutually recursive identifiers.
      --   e: A let-binding in a mutually recursive scope.
      let replacenames = lam acc. lam e.
        let id = (acc.0).id in
        let prefix = match e.body with TmLam _ then "fun" else "var" in
        let newname = strJoin "" [prefix, int2string id, "_", e.ident] in
        let newref = TmLamliftTypedVar {ident = newname, tpe = e.tpe} in
        let newstate = st_incrId (st_addVarToEnv e.ident newref acc.0) in
        (newstate, concat (acc.1) [{e with ident = newname}], concat acc.2 [{ident = newname, body = newref}])
      in
      let replaceret = foldl replacenames (state, [], []) t.bindings in

      let repnames = replaceret.2 in --<-- [{ident : String, body : Expr}]: All mutually recursive identifiers

      -- Include the newly bound identifiers and clear any externally generated
      -- references.
      let repstate = {{{replaceret.0 with lambdarefs = repnames} with externrefs = []} with genargs = []} in
      let repbindings = replaceret.1 in

      -- Lift out each individual expression
      --   acc.0: The state that is being updated
      --   acc.1: The let-bindings with lifted bodies
      --   b: A let-binding in the mutually recursive scope
      let liftbindings = lam acc. lam b.
        let acc_state = acc.0 in
        let acc_bindings = acc.1 in

        let envaddfld = lam st. lam v.
          match v.genarg with TmLamliftTypedVar s then
            st_addVarToEnv (strip_prefix s.ident) v.genarg st
          else let _ = dprint v in error "envaddfld: Not a typed var."
        in
        let newstate = foldl envaddfld acc_state (acc_state.genargs) in

        let ret = lamlift newstate (TmLamChain {body = b.body}) in

        -- Update the state to get rid of any local variable declarations.
        -- (We still keep generated arguments and external references)
        ({ret.0 with env = acc_state.env}, concat acc_bindings [{b with body = ret.1}])
      in
      let liftedreclets = foldl liftbindings (repstate, []) repbindings in

      -- (Invariant: The liftedstate contains syncronized sequences of both
      --             external references and their generated arguments.)
      let liftedstate = liftedreclets.0 in
      let liftedbindings = liftedreclets.1 in

      -- Generate arguments that were externally referenced in the expressions.
      let arggen = lam b.
        -- The top level definition: TmRecLets [("fun#_<name>", Option, TmLam ("arg#_%%", None, ...))]
        let lambdagenerator = lam e. lam acc.
          match e.genarg with TmLamliftTypedVar t2 then
            TmLam {ident = t2.ident, tpe = t2.tpe, body = acc}
          else let _ = dprint e in error "internal error (3)"
        in
        let newbody = foldr lambdagenerator b.body liftedstate.genargs in
        let arrowgenerator = lam e. lam acc.
          match e.genarg with TmLamliftTypedVar t2 then
            match t2.tpe with Some t3 then
              match acc with Some t4 then
                Some (TyArrow {from = t3, to = t4})
              else None ()
            else None ()
          else error "RecLetsLamlift: arrowgenerator: Generated argument is not TmLamliftTypedVar"
        in
        let newtype = foldr arrowgenerator b.tpe liftedstate.genargs in
        {{b with tpe = newtype} with body = newbody}
      in
      let arggenbindings = map arggen liftedbindings in

      -- Add the new arguments to the old environment with proper arguments applied
      let envgen = lam accstate. lam b.
        let name = b.ident in
        let oldname = strip_prefix b.ident in

        -- The value to bind: TmApp (... TmApp (TmVar "fun#_<name>", Expr), ...)
        let binding = foldl (lam acc. lam e. TmApp {lhs = acc, rhs = e}) (TmVar {ident = name}) liftedstate.externrefs in

        st_addVarToEnv oldname binding accstate
      in
      let envstate = foldl envgen {{state with id = liftedstate.id} with globaldefs = liftedstate.globaldefs} liftedbindings in

      -- Replace all internal occurrences with the newly bound values
      let appgen = lam acc. lam b.
        let name = b.ident in

        -- The value to bind: TmApp (... TmApp (TmVar "fun#_<name>", Expr), ...)
        let binding = foldl (
          lam acc. lam e.
          match e.genarg with TmLamliftTypedVar t1 then
            TmApp {lhs = acc, rhs = TmVar {ident = t1.ident}}
          else error "generated argument is not typed var"
        ) (TmVar {ident = name}) liftedstate.genargs in

        concat acc [{ident = name, replacement = binding}]
      in
      let applist = foldl appgen [] liftedbindings in
      let appgenbindings = map (lam b. {b with body = lamliftReplaceIdentifiers applist b.body}) arggenbindings in

      -- Return a TmRecLets with the defines
      let finalstate = st_addGlobaldef (TmRecLets {{t with bindings = appgenbindings}
                                                      with inexpr = TmConst {val = CUnit ()}}) envstate in

      lamlift finalstate t.inexpr

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmRecLets t -> TmRecLets {{t with bindings = map (lam e. {e with body = lamliftReplaceIdentifiers newnames e.body}) t.bindings}
                                   with inexpr = lamliftReplaceIdentifiers newnames t.inexpr}
end

lang ConstLamlift = ConstAst
    sem lamlift (state : LiftState) =
    | TmConst c -> (state, TmConst c)

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmConst c -> TmConst c
end

lang UnitLamlift = UnitAst
    --sem lamlift (state : LiftState) =
    --| CUnit -> (state, CUnit)
end

lang IntLamlift = IntAst

lang ArithIntLamlift = ArithIntAst + ConstLamlift
    --sem lamlift (state : LiftState) =
    --| CAddi -> (state, CAddi)
end

lang BoolLamlift = BoolAst + ConstLamlift
    sem lamlift (state : LiftState) =
    --| CBool b -> (state, CBool b)
    --| CNot -> (state, CNot)
    --| CAnd -> (state, CAnd)
    --| COr -> (state, COr)
    | TmIf t ->
      let condret = lamlift state t.cond in
      let condstate = st_addGenargsToEnv condret.0 state {condret.0 with env = state.env} in

      let thnret = lamlift condstate t.thn in
      let thnstate = st_addGenargsToEnv thnret.0 state {thnret.0 with env = state.env} in

      let elsret = lamlift thnstate t.els in
      let elsstate = st_addGenargsToEnv elsret.0 state {elsret.0 with env = state.env} in

      (elsstate, TmIf {{{t with cond = condret.1} with thn = thnret.1} with els = elsret.1})

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmIf t -> TmIf {{{t with cond = lamliftReplaceIdentifiers newnames t.cond}
                          with thn = lamliftReplaceIdentifiers newnames t.thn}
                          with els = lamliftReplaceIdentifiers newnames t.els}
end

lang CmpLamlift = CmpAst + ConstLamlift
    --sem lamlift (state : LiftState) =
    --| CEqi -> (state, CEqi)
end

lang SeqLamlift = SeqAst + ConstLamlift
    sem lamlift (state : LiftState) =
    --| CSeq tms -> (state, CSeq tms)
    --| CGet -> (state, CGet)
    | TmSeq t ->
      let foldfun = lam acc. lam e.
        let accstate = acc.0 in
        let acclist = acc.1 in

        let eret = lamlift accstate e in

        let newstate = st_addGenargsToEnv eret.0 state {eret.0 with env = accstate.env} in
        let newlist = concat acclist [eret.1] in -- this is clumsy, perhaps use foldr?
        (newstate, newlist)
      in
      let foldret = foldl foldfun (state, []) t.tms in

      let foldstate = st_addGenargsToEnv foldret.0 state {foldret.0 with env = state.env} in
      let vs = foldret.1 in

      -- Returning a TmSeq since we do not know if the contained terms are
      -- constant or not.
      (foldstate, TmSeq {t with tms = vs})

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmSeq t -> TmSeq {t with tms = map (lam e. lamliftReplaceIdentifiers newnames e) t.tms}
end

lang TupleLamlift = TupleAst
    sem lamlift (state : LiftState) =
    | TmTuple t ->
      -- This works just like TmSeq at the moment, copied from there.
      let foldfun = lam acc. lam e.
        let accstate = acc.0 in
        let acclist = acc.1 in

        let eret = lamlift accstate e in

        let newstate = st_addGenargsToEnv eret.0 state {eret.0 with env = accstate.env} in
        let newlist = concat acclist [eret.1] in
        (newstate, newlist)
      in
      let foldret = foldl foldfun (state, []) t.tms in

      let foldstate = st_addGenargsToEnv foldret.0 state {foldret.0 with env = state.env} in
      let vs = foldret.1 in

      (foldstate, TmTuple {t with tms = vs})

    | TmProj t ->
      let tupret = lamlift state t.tup in
      let tupstate = st_addGenargsToEnv tupret.0 state {tupret.0 with env = state.env} in
      (tupstate, TmProj {t with tup = tupret.1})

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmTuple t -> TmTuple {t with tms = map (lam e. lamliftReplaceIdentifiers newnames e) t.tms}
    | TmProj t -> TmProj {t with tup = lamliftReplaceIdentifiers newnames t.tup}
end

lang MatchLamlift = MatchAst + VarPat + UnitPat + IntPat +
                    BoolPat + TuplePat + DataPat + VarAst
    sem lamlift (state : LiftState) =
    | TmMatch t ->
      let targetret = lamlift state t.target in
      let targetstate = st_addGenargsToEnv targetret.0 state {targetret.0 with env = state.env} in

      let patret = lamliftPat targetstate t.pat in
      let patstate = patret.0 in

      let thnret = lamlift patstate t.thn in
      let thnstate = st_addGenargsToEnv thnret.0 patstate {{thnret.0 with env = patstate.env} with lambdarefs = patstate.lambdarefs} in

      let elsret = lamlift thnstate t.els in
      let elsstate = st_addGenargsToEnv elsret.0 patstate {{elsret.0 with env = patstate.env} with lambdarefs = patstate.lambdarefs} in

      let retstate = {{elsret.0 with env = state.env} with lambdarefs = state.lambdarefs} in
      (retstate, TmMatch {{{{t with target = targetret.1} with pat = patret.1} with thn = thnret.1} with els = elsret.1})

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmMatch t -> TmMatch {{{t with target = lamliftReplaceIdentifiers newnames t.target}
                                with thn = lamliftReplaceIdentifiers newnames t.thn}
                                with els = lamliftReplaceIdentifiers newnames t.els}

    sem lamliftPat (state : LiftState) =
    | PVar t ->
      -- Bind the identifier in the current scope
      let newname = strJoin "" ["pvar", int2string state.id, "_", t.ident] in
      let updatedstate = st_incrId (st_addVarToEnv t.ident (TmVar {ident = newname})
                                   (st_addLambdaref newname (TmVar {ident = newname}) state)) in
      (updatedstate, PVar {t with ident = newname})
    | PUnit t -> (state, PUnit t)
    | PInt t -> (state, PInt t)
    | PBool t -> (state, PBool t)
    | PTuple t ->
      -- acc.0: state
      -- acc.1: list of patterns
      let liftpats = lam acc. lam e.
        let ret = lamliftPat acc.0 e in
        (ret.0, concat acc.1 [ret.1])
      in
      let foldret = foldl liftpats (state, []) t.pats in
      (foldret.0, PTuple {t with pats = foldret.1})
    | PCon t ->
      let newident = find (lam e. eqstr (e.key) t.ident) state.env.econ in
      let subret = lamliftPat state t.subpat in
      match newident with Some t1 then
        match t1.value with TmConFun t2 then
          (subret.0, PCon {{t with ident = t2.ident} with subpat = subret.1})
        else
          (subret.0, PCon {t with subpat = subret.1})
      else
        (subret.0, PCon {t with subpat = subret.1})
end

lang UtestLamlift = UtestAst
    sem lamlift (state : LiftState) =
    | TmUtest t ->
      let testret = lamlift state t.test in
      let teststate = st_addGenargsToEnv testret.0 state {testret.0 with env = state.env} in

      let expectedret = lamlift teststate t.expected in
      let expectedstate = st_addGenargsToEnv expectedret.0 state {expectedret.0 with env = state.env} in

      let nextret = lamlift expectedstate t.next in
      let nextstate = st_addGenargsToEnv nextret.0 state {nextret.0 with env = state.env} in

      (nextstate, TmUtest {{{t with test = testret.1} with expected = expectedret.1} with next = nextret.1})

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmUtest t -> TmUtest {{{t with test = lamliftReplaceIdentifiers newnames t.test}
                                with expected = lamliftReplaceIdentifiers newnames t.expected}
                                with next = lamliftReplaceIdentifiers newnames t.next}
end

lang MExprLamlift = VarLamlift + AppLamlift + FunLamlift +
                    LetLamlift + RecLetsLamlift + ConstLamlift +
                    UnitLamlift + IntLamlift + ArithIntLamlift +
                    BoolLamlift + CmpLamlift + SeqLamlift +
                    TupleLamlift + DataLamlift + MatchLamlift +
                    UtestLamlift + MExprAst

lang MExprLLandPPandEval = MExprLamlift + MExprPrettyPrint + MExprEval

mexpr
use MExprLLandPPandEval in

let builtin_env = [{key = "addi", value = const_ (CAddi ())},
                   {key = "subi", value = const_ (CSubi ())},
                   {key = "muli", value = const_ (CMuli ())},
                   {key = "and", value = const_ (CAnd ())},
                   {key = "or", value = const_ (COr ())},
                   {key = "not", value = const_ (CNot ())},
                   {key = "eqi", value = const_ (CEqi ())},
                   {key = "get", value = const_ (CGet ())}]
in

-- Lifts out the lambdas, returning a new AST with all lambdas on the top
-- level.
let lift_lambdas: Expr -> Expr = lam ast.

    let initstate: LiftState = {id = 0,
                                globaldefs = [],
                                env = {evar = builtin_env, econ = [], etype = []},
                                lambdarefs = [],
                                externrefs = [],
                                genargs = []}
    in

    let liftret = lamlift initstate ast in

    let mainexpr = liftret.1 in
    let liftedexprs = (liftret.0).globaldefs in

    -- liftedexprs is in reverse order, so the let-expression that should be
    -- first is at the end of the list
    let convert_from_globaldef = lam acc. lam gd.
        match gd with TmLet t then
            TmLet {t with inexpr = acc}
        else match gd with TmRecLets t then
            TmRecLets {t with inexpr = acc}
        else match gd with TmConDef t then
            TmConDef {t with inexpr = acc}
        else
            error "Global definition is not of TmLet, TmRecLets, or TmConDef"
    in
    foldl convert_from_globaldef mainexpr liftedexprs
in

let example_ast =
  bindall_ [
    let_ "foo" (None ()) (
      lam_ "a" (None ()) (lam_ "b" (None ()) (
        bindall_ [
          let_ "bar" (None ()) (
            lam_ "x" (None ()) (
              appf2_ (var_ "addi") (var_ "b") (var_ "x")
            )
          ),
          let_ "fun4_bar" (None ()) (int_ 3),
          appf2_ (var_ "addi")
                 (app_ (var_ "bar") (var_ "fun4_bar"))
                 (var_ "a")
        ]
      ))
    ),
    appf2_ (var_ "foo")
           (int_ 1)
           (int_ 11)
  ]
in

-- TEMPORARY: Debug print to check why include order messes with the MLang
--            uses, remove once fixed.
--let _ = print "\n" in
--let _ = dprint (let_ "foo" (None ()) unit_) in
--let _ = print "\n\n" in
--let _ = use MExprLLandPPandEval in
--  dprint (TmLet {ident = "foo",
--                 tpe = None (),
--                 body = unit_,
--                 inexpr = unit_})
--in
--let _ = print "\n" in

let example_anonlambda_ast =
  bindall_ [
    let_ "foo" (None ()) (
      lam_ "a" (None ()) (lam_ "b" (None ()) (
        bindall_ [
          let_ "fun4_bar" (None ()) (int_ 3),
          appf2_ (var_ "addi")
                 (appf1_ (lam_ "x" (None ()) (appf2_ (var_ "addi") (var_ "b") (var_ "x")))
                         (var_ "fun4_bar"))
                 (var_ "a")
        ]
      ))
    ),
    appf2_ (var_ "foo")
           (int_ 4)
           (int_ 311)
  ]
in

let example_nested_ast =
  bindall_ [
    let_ "foo" (None ()) (
      lam_ "a" (None ()) (lam_ "b" (None ()) (
        bindall_ [
          let_ "bar" (None ()) (
            lam_ "x" (None ()) (
              bindall_ [
                let_ "babar" (None ()) (
                  lam_ "x" (None ()) (
                    appf2_ (var_ "addi") (var_ "b") (var_ "x")
                  )
                ),
                appf1_ (var_ "babar") (var_ "x")
              ]
            )
          ),
          let_ "fun4_bar" (None ()) (int_ 3),
          appf2_ (var_ "addi")
                 (appf1_ (var_ "bar") (var_ "fun4_bar"))
                 (var_ "a")
        ]
      ))
    ),
    appf2_ (var_ "foo")
           (int_ 11)
           (int_ 3)
  ]
in

let example_recursive_ast =
  bindall_ [
    let_ "foo" (None ()) (
      lam_ "x" (None ()) (
        bindall_ [
          reclets_add "bar" (None ()) (
            lam_ "y" (None ()) (
              appf2_ (var_ "addi") (var_ "y") (var_ "x")
            )
          ) (reclets_add "babar" (None ()) (
            lam_ "a" (None ()) (
              appf1_ (var_ "bar") (var_ "a")
            )
          ) (reclets_empty)),
          app_ (var_ "babar") (int_ 6)
        ]
      )
    ),
    appf1_ (var_ "foo") (int_ 3)
  ]
in

let example_factorial =
  bindall_ [
    reclets_add "factorial" (None ()) (
      lam_ "n" (None ()) (
        if_ (appf2_ (var_ "eqi") (var_ "n") (int_ 0))
            (int_ 1)
            (appf2_ (var_ "muli")
                    (var_ "n")
                    (appf1_ (var_ "factorial")
                            (appf2_ (var_ "subi") (var_ "n") (int_ 1))))
      )
    ) (reclets_empty),
    appf1_ (var_ "factorial") (int_ 11)
  ]
in

let example_conmatch =
  bindall_ [
    let_ "foo" (None ()) (
      bindall_ [
        condef_ "MyCon" (None ()),
        let_ "bar" (None ()) (
          lam_ "x" (None ()) (
            match_ (var_ "x")
                   (pcon_ "MyCon" punit_)
                   (true_)
                   (false_)
          )
        ),
        appf1_ (var_ "bar") (app_ (confun_ "MyCon")
                                  (unit_))
      ]
    ),
    var_ "foo"
  ]
in

let example_conmatch_samename =
  bindall_ [
    let_ "foo" (None ()) (
      bindall_ [
        condef_ "x" (None ()),
        let_ "bar" (None ()) (
          lam_ "x" (None ()) (
            match_ (var_ "x")
                   (pcon_ "x" (pvar_ "x"))
                   (var_ "x")
                   (false_)
          )
        ),
        appf1_ (var_ "bar") (app_ (confun_ "x")
                                  (true_))
      ]
    ),
    var_ "foo"
  ]
in

let example_typed_ast =
  bindall_ [
    let_ "foo" (Some (tyarrows_ [tyint_, tyint_, tyint_])) (
      lam_ "a" (Some (tyint_)) (lam_ "b" (Some (tyint_)) (
        bindall_ [
          let_ "bar" (Some (tyarrow_ tyint_ tyint_)) (
            lam_ "x" (Some (tyint_)) (
              appf2_ (var_ "addi") (var_ "b") (var_ "x")
            )
          ),
          let_ "fun4_bar" (Some (tyint_)) (int_ 3),
          appf2_ (var_ "addi")
                 (appf1_ (var_ "bar") (var_ "fun4_bar"))
                 (var_ "a")
        ]
      ))
    ),
    appf2_ (var_ "foo")
           (int_ 1)
           (int_ 0)
  ]
in

let example_recursive_typed_ast =
  bindall_ [
    let_ "foo" (Some (tyarrow_ tyint_ tyint_)) (
      lam_ "x" (Some (tyint_)) (
        bindall_ [
          reclets_add "bar" (Some (tyarrow_ tyint_ tyint_)) (
            lam_ "y" (Some (tyint_)) (
              appf2_ (var_ "addi") (var_ "y") (var_ "x")
            )
          ) (reclets_add "babar" (Some (tyarrow_ tyint_ tyint_)) (
            lam_ "a" (Some (tyint_)) (
              appf1_ (var_ "bar") (var_ "a")
            )
          ) (reclets_empty)),
          (app_ (var_ "babar") (int_ 7))
        ]
      )
    ),
    appf1_ (var_ "foo") (int_ 2)
  ]
in

let example_conmatch_typed =
  bindall_ [
    let_ "foo" (Some (tybool_)) (
      bindall_ [
        condef_ "MyCon" (Some (tyunit_)),
        let_ "bar" (Some (tyarrow_ (tycon_ "MyConType") tybool_)) (
          lam_ "x" (Some (tycon_ "MyConType")) (
            match_ (var_ "x")
                   (pcon_ "MyCon" punit_)
                   (true_)
                   (false_)
          )
        ),
        appf1_ (var_ "bar") (app_ (confun_ "MyCon")
                                  (unit_))
      ]
    ),
    var_ "foo"
  ]
in

let example_ifexpr_ast =
  bindall_ [
    let_ "foo" (None ()) (
      lam_ "a" (None ()) (lam_ "b" (None ()) (
        bindall_ [
          reclets_add "bar" (None ()) (
            lam_ "x" (None ()) (
              if_ (appf2_ (var_ "eqi") (var_ "x") (int_ 3))
                  (appf2_ (var_ "addi") (var_ "b") (int_ 10000))
                  (appf2_ (var_ "addi") (var_ "b") (var_ "x"))
            )
          ) (reclets_empty),
          let_ "fun4_bar" (None()) (int_ 3),
          appf2_ (var_ "addi")
                 (appf1_ (var_ "bar") (var_ "fun4_bar"))
                 (var_ "a")
        ]
      ))
    ),
    appf2_ (var_ "foo")
           (int_ 1)
           (int_ 11)
  ]
in

let example_multiuse =
  bindall_ [
    let_ "foo" (None ()) (
      lam_ "x" (None ()) (
        bindall_ [
          let_ "bar" (None ()) (
            lam_ "y" (None ()) (
              bindall_ [
                let_ "xp1" (None ()) (appf2_ (var_ "addi")
                                             (var_ "x")
                                             (int_ 1)),
                if_ (appf2_ (var_ "eqi") (var_ "x") (var_ "y"))
                    (appf2_ (var_ "subi") (var_ "xp1") (var_ "x"))
                    (appf2_ (var_ "addi")
                            (appf2_ (var_ "addi") (var_ "x") (var_ "y"))
                            (appf2_ (var_ "subi") (var_ "x") (var_ "y")))
              ]
            )
          ),
          appf1_ (var_ "bar") (int_ 3)
        ]
      )
    ),
    appf1_ (var_ "foo") (int_ 11)
  ]
in

let example_let_in_reclet =
  bindall_ [
    let_ "foo" (None ()) (
      lam_ "x" (None ()) (
        bindall_ [
          reclets_add "bar" (None ()) (
            lam_ "y" (None ()) (
              bindall_ [
                let_ "babar" (None ()) (
                  lam_ "z" (None ()) (
                    appf2_ (var_ "muli") (var_ "z") (var_ "z")
                  )
                ),
                if_ (appf2_ (var_ "eqi") (var_ "y") (int_ 0))
                    (int_ 0)
                    (appf2_ (var_ "addi")
                            (appf1_ (var_ "babar") (var_ "y"))
                            (appf1_ (var_ "bar")
                                    (appf2_ (var_ "subi")
                                            (var_ "y")
                                            (int_ 1))))
              ]
            )
          ) (reclets_empty),
          appf1_ (var_ "bar")
                 (appf2_ (var_ "muli")
                         (var_ "x")
                         (int_ 2))
        ]
      )
    ),
    appf1_ (var_ "foo") (int_ 7)
  ]
in

-- Convert from a Lambda Lifting-style environment to an eval-style context
let ctx = {env = map (lam e. (e.key, e.value)) builtin_env} in

-- Test that the examples can run the lamlift semantics without errors and that
-- they evaluate to the same value after lambda lifting
utest eval ctx example_ast with eval ctx (lift_lambdas example_ast) in
utest eval ctx example_nested_ast with eval ctx (lift_lambdas example_nested_ast) in
utest eval ctx example_recursive_ast with eval ctx (lift_lambdas example_recursive_ast) in
utest eval ctx example_factorial with eval ctx (lift_lambdas example_factorial) in
utest eval ctx example_conmatch with eval ctx (lift_lambdas example_conmatch) in
utest eval ctx example_conmatch_samename with eval ctx (lift_lambdas example_conmatch_samename) in
utest eval ctx example_typed_ast with eval ctx (lift_lambdas example_typed_ast) in
utest eval ctx example_recursive_typed_ast with eval ctx (lift_lambdas example_recursive_typed_ast) in
utest eval ctx example_conmatch_typed with eval ctx (lift_lambdas example_conmatch_typed) in
utest eval ctx example_ifexpr_ast with eval ctx (lift_lambdas example_ifexpr_ast) in
utest eval ctx example_multiuse with eval ctx (lift_lambdas example_multiuse) in
utest eval ctx example_let_in_reclet with eval ctx (lift_lambdas example_let_in_reclet) in

let testllprint = lam name. lam ast.
  let bar = "------------------------" in
  let top = strJoin "" ["\n", bar, " ", name, " ", bar] in
  let _ = print top in
  let _ =
      let _ = print "\n[>>>>  Before  <<<<]\n" in
      let _ = print (pprintCode 0 ast) in
      let _ = print "\n" in
      ()
  in
  let _ =
      let _ = print "\n[>>>>  After  <<<<]\n" in
      let _ = print (pprintCode 0 (lift_lambdas ast)) in
      let _ = print "\n" in
      ()
  in
  let _ = print (makeSeq (length top) '-') in
  let _ = print "\n\n" in
  ()
in

--let _ = testllprint "example_ast" example_ast in
--let _ = testllprint "example_anonlambda_ast" example_anonlambda_ast in
--let _ = testllprint "example_nested_ast" example_nested_ast in
--let _ = testllprint "example_recursive_ast" example_recursive_ast in
--let _ = testllprint "example_factorial" example_factorial in
--let _ = testllprint "example_conmatch" example_conmatch in
--let _ = testllprint "example_conmatch_samename" example_conmatch_samename in
--let _ = testllprint "example_typed_ast" example_typed_ast in
--let _ = testllprint "example_recursive_typed_ast" example_recursive_typed_ast in
--let _ = testllprint "example_conmatch_typed" example_conmatch_typed in
--let _ = testllprint "example_ifexpr_ast" example_ifexpr_ast in
--let _ = testllprint "example_multiuse" example_multiuse in
--let _ = testllprint "example_let_in_reclet" example_let_in_reclet in

()
