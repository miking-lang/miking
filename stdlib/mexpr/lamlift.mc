// Defines semantics for lambda lifting
// Based on the technique from the 1985 paper.
// (This will not handle currying until a type-checker has been implemented.)

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
// - For Let expressions in a recursive scope, the identifiers need to be
//   given a temporary token. After all the Let expressions have been scanned
//   (just like in the previous step), the generated temporary tokens need to
//   be replaced by a TmApp (..., ...) where the generated arguments are
//   pre-applied and the identifier is replaced by the actual identifier for
//   the Let expression (not the temporary one).

// NOTE: Assumes that bound variables are limited to the following AST nodes:
//        - TmVar
//        - TmApp
//
// If an identifier is bound to a different node which itself contain
// identifiers, then this could lead to the lambda lifting returning an
// incorrect program even if the input program was correct.

include "ast.mc"
include "option.mc"
include "seq.mc"
include "string.mc"

-- Temporary introduced AST elements
lang TopDef
    syn Expr =
    | TmTopDef {ident : String,
                tpe   : Option,
                body  : Expr}
    | TmTopRecDef {bindings : [{ident : String,
                                tpe   : Option,
                                body  : Expr)}]}
end

-- State for lambda lifting
--   id:         ID counter (used to assign globally unique names to
--               identifiers).
--   globaldefs: List of expressions that has been lifted out.
--   env:        The environment lookup of the current scope.
--   lambdarefs: Lookup of identifiers that are defined locally in the current
--               lambda expression (arguments and non-lambda let expressions).
--   externrefs: List of identifiers that have been referenced in the current
--               lambda scope, but are not locally part of the current lambda
--               scope.
--   genargs:    List of arguments that have been generated to take the place
--               of the externally referenced identifiers.
type LiftState = {id         : Int,
                  globaldefs : [Expr],
                  env        : [{key   : String,
                                 value : Expr}],
                  lambdarefs : [{ident : String,
                                 body  : Expr}],
                  externrefs : [Expr],
                  genargs    : [Expr]}


-- LiftState update functions
let st_incrId: LiftState -> LiftState =
    lam st.
    {st with id = addi st.id 1}

let st_addGlobaldef: Expr -> LiftState -> LiftState =
    lam gd. lam st.
    {st with globaldefs = cons gd st.globaldefs}

let st_addToEnv: String -> Expr -> LiftState -> LiftState =
    lam key. lam value. lam st.
    {st with env = cons {key = key, value = value} st.env}

let st_addLambdaref: String -> Expr -> LiftState -> LiftState =
    lam ident. lam body. lam st.
    {st with lambdarefs = cons {ident = ident, body = body} st.lambdarefs}

let st_addExternref: Expr -> LiftState -> LiftState =
    lam er. lam st.
    {st with externrefs = cons er st.externrefs}

let st_addGenarg: Expr -> LiftState -> LiftState =
    lam genarg. lam st.
    {st with genargs = cons genarg st.genargs}

-- Returns whether the String is globally defined in the LiftState
-- (Not sure if I need this, keeping this here for the time being)
let st_isGloballyDefined: String -> LiftState -> Bool =
    lam s. lam st.
    use TopDef in
    let tdsm = lam td. -- tdsm: TopDefStringMatch
        match td with TmTopDef t then
            eqstr t.ident s
        else match td with TmTopRecDef t then
            any (lam rec. eqstr tup.ident s) t
        else
            error "Global define is not TmTopDef or TmTopRecDef"
    in
    any tdsm st.globaldefs

-- Returns whether the string is available in the current lambda scope
let st_inLambdaScope: String -> LiftState -> Bool =
    lam s. lam st.
    any (lam e. eqstr s e.ident) st.lamdarefs

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

lang VarLamlift = VarAst + TopDef -- TEMP: Remove TopDef when mlang-mangling is merged
    sem lamlift (state : LiftState) =
    | TmVar x ->
      -- TEMP: Put this here until mlang-mangling is merged...
      let st_isGloballyDefinedTMP: String -> LiftState -> Bool =
          lam s. lam st.
          use TopDef in
          let tdsm = lam td. -- tdsm: TopDefStringMatch
              match td with TmTopDef t then
                  eqstr t.ident s
              else match td with TmTopRecDef t then
                  any (lam rec. eqstr tup.ident s) t
              else
                  error "Global define is not TmTopDef or TmTopRecDef"
          in
          any tdsm st.globaldefs
      in
      let ret = find (lam e. eqstr (e.key) x) state.env in
      match ret with Some t then
        -- Function that for all variables in an expression, that they are in
        -- the current scope.
        recursive let check_scope = lam chkstate. lam e.
          match e with TmVar t1 then
            -- If the found variable is in the current lambda scope or in the
            -- global scope, then it is no need to generate an argument for it.
            if or (st_inLambdaScope t1.ident chkstate) (st_isGloballyDefinedTMP t1.ident chkstate) then
              (chkstate, e)
            else
              -- Referenced something outside of our scope, generate argument for it.
              let id = chkstate.id in
              -- All bound identifiers should have either "var", "fun", or "arg"
              -- as a prefix.
              let oldname = strip_prefix t1.ident in
              let newname = concat "arg" (concat (int2string id) (cons '_' oldname)) in
              let newvar = TmVar {t1 with ident = newname} in
              let newstate = st_incrId (st_addToEnv oldname newvar
                                       (st_addLambdaref newname newvar
                                       (st_addExternref e
                                       (st_addGenarg newvar chkstate)))) in
              (newstate, newvar)
          else match e with TmApp t2 then
            -- Our bound identifier references to a chain of applications, make
            -- that all identifiers in that application are in the current scope.
            let lhsret = check_scope chkstate t2.lhs in
            let lhsstate = lhsret.0 in
            let rhsret = check_scope lhsstate t2.rhs in
            let rhsstate = rhsret.0 in
            (rhsstate, TmApp {t2 with lhs = lhsret.1, rhs = rhsret.1})
          else
            (chkstate, e)
        in
        check_scope state t.value
      else
        error (concat "Variable \"" (concat x "\" not found."))

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmVar x ->
      recursive let find_replacement = lam l.
        if null l then
          TmVar x
        else
          let e = head l in -- e: (name, replacement)
          if eqstr x e.ident then
            e.replacement
          else
            find_replacement (tail l)
      in
      find_replacement newnames
end

lang AppLamlift = AppAst
    sem lamlift (state : LiftState) =
    | TmApp t ->
      let lhsret = lamlift state t.lhs in
      let lhsstate = {lhsret.0 with env = state.env} in
      let rhsret = lamlift lhsstate t.rhs in
      let rhsstate = {rhsret.0 with env = state.env} in
      (rhsstate, TmApp {t with lhs = lhsret.1, rhs = rhsret.1})

    sem lamliftReplaceIdentifiers (newnames : [{ident : String, replacement : Expr}]) =
    | TmApp t -> TmApp {t with lhs = lamliftReplaceIdentifiers newnames t.lhs,
                               rhs = lamliftReplaceIdentifiers newnames t.rhs}
end

lang FunLamlift = FunAst + TopDef
    syn Expr =
    | TmLamChain {body : Expr}

--------------------- CHECKPOINT ---------------------


    sem lamlift (state : StateTuple) =
    | TmLam t ->
      -- Encountered Lambda outside of a lambda chain, name this as fun#_anon
      let passed_state = st_setLambdarefs [] (st_setExternrefs [] (st_setGenargs [] state)) in
      let ret = lamlift passed_state (TmLamChain (TmLam t)) in

      let updatedstate = st_setId (st_id ret.0) (st_setGlobaldefs (st_globaldefs ret.0) state) in

      let id = (st_id updatedstate) in
      let name = concat "fun" (concat (int2string id) "_anon") in

      -- The value to return: TmApp (... TmApp (TmVar "fun#_anon", Expr), ...)
      let retval = foldl (lam acc. lam e. TmApp (acc, e)) (TmVar name) (st_externrefs (ret.0)) in

      -- The top level definition: TmTopDef ("fun#_anon", TmLam ("arg#_%%", None, ...))
      let lambdagenerator = lam e. lam acc. match e with TmVar t1 then (TmLam (t1, None, acc)) else error "internal error (1)" in
      let topdefbody = foldr lambdagenerator ret.1 (st_genargs (ret.0)) in

      -- Increment the id counter and add the TopDef to globaldefs
      let newstate = st_incrId (st_addGlobaldef (TmTopDef (name, None, topdefbody)) updatedstate) in

      (newstate, retval)

    | TmLamChain t ->
      match t with TmLam t1 then
        let newname = concat "arg" (concat (int2string (st_id state)) (cons '_' (t1.0))) in
        let arg = TmVar newname in

        let newstate = st_incrId (st_addToEnv (t1.0, arg) (st_addLambdaref (newname, arg) state)) in
        let ret = lamlift newstate (TmLamChain t1.2) in

        let retstate = st_setEnv (st_env state) ret.0 in
        let retbody = ret.1 in
        (retstate, TmLam (newname, t1.1, retbody))
      else
        lamlift state t

    sem lamliftReplaceIdentifiers (newnames : [(String, Expr)]) =
    | TmLam t -> TmLam (t.0, t.1,
                        lamliftReplaceIdentifiers newnames t.2)
    | TmLamChain t -> TmLamChain (lamliftReplaceIdentifiers newnames t)
end

lang LetLamlift = LetAst + FunLamlift + TopDef
    sem lamlift (state : StateTuple) =
    | TmLet t ->
      let name = t.0 in
      let tpe = t.1 in
      let bodyexpr = t.2 in
      let inexpr = t.3 in
      match bodyexpr with TmLam t1 then
        -- Pass the current StateTuple with cleared lambdarefs, externrefs, and
        -- generated args to the body expression.
        let passed_state = st_setLambdarefs [] (st_setExternrefs [] (st_setGenargs [] state)) in
        let ret = lamlift passed_state (TmLamChain bodyexpr) in

        let updatedstate = st_setId (st_id ret.0) (st_setGlobaldefs (st_globaldefs ret.0) state) in

        -- Encountered a let-defined Lambda, name this as fun#_<name>
        let id = (st_id updatedstate) in
        let newname = concat "fun" (concat (int2string id) (cons '_' name)) in

        -- The value to bind: TmApp (... TmApp (TmVar "fun#_<name>", Expr), ...)
        let retval = foldl (lam acc. lam e. TmApp (acc, e)) (TmVar newname) (st_externrefs (ret.0)) in

        -- The top level definition: TmTopDef ("fun#_<name>", TmLam ("arg#_%%", None, ...))
        let lambdagenerator = lam e. lam acc. match e with TmVar t2 then (TmLam (t2, None, acc)) else let _ = dprint e in error "\ninternal error (2)" in
        let topdefbody = foldr lambdagenerator ret.1 (st_genargs (ret.0)) in

        -- Increment the id counter, add the TopDef to globaldefs, and add the return type to scope
        let newstate = st_incrId (st_addGlobaldef (TmTopDef (newname, None, topdefbody))
                                 (st_addToEnv (name, retval) updatedstate)) in

        -- LHS has been lifted out, evaluate RHS and return that
        lamlift newstate inexpr
      else
        -- Traverse the let body and extract everything from the returned state
        -- apart from the environment.
        let ret = lamlift state bodyexpr in
        let updatedstate = st_setEnv (st_env state) ret.0 in

        let id = (st_id updatedstate) in
        let newname = concat "var" (concat (int2string id) (cons '_' name)) in

        -- Increment ID counter, add the "original" variable name to the
        -- environment, and mark this variable as referencable from the current
        -- lambda scope.
        let newstate = st_incrId (st_addToEnv (name, TmVar newname)
                                 (st_addLambdaref (newname, TmVar newname) updatedstate)) in

        let inret = lamlift newstate inexpr in

        let inretstate = st_setEnv (st_env state) inret.0 in

        (inretstate, TmLet (newname, tpe, ret.1, inret.1))

    sem lamliftReplaceIdentifiers (newnames : [(String, Expr)]) =
    | TmLet t -> TmLet (t.0, t.1,
                        lamliftReplaceIdentifiers newnames t.2,
                        lamliftReplaceIdentifiers newnames t.3)
end

-- Lambda lifting of mutually recursive functions
lang RecLetsLamlift = RecLetsAst + FunLamlift + TopDef
    sem lamlift (state : StateTuple) =
    | TmRecLets t ->
      let bindings = t.0 in
      let inexpr = t.1 in

      -- Check that all bound identifiers are unique
      let bound_names = map (lam e. e.0) bindings in
      if any (lam s. neqi 1 (length (filter (eqstr s) bound_names))) bound_names
      then error "Name duplication in recursive expression"
      else -- continue

      -- Add all of the binding identifiers to the current scope
      --   acc.0: The state that is being updated.
      --   acc.1: The let-bindings with updated names.
      --   acc.2: Lambda-reference list that contains all mutually recursive identifiers.
      --   e: A let-binding in a mutually recursive scope.
      let replacenames = lam acc. lam e.
        let id = st_id (acc.0) in
        let name = e.0 in
        let tpe = e.1 in
        let body = e.2 in
        let prefix = match body with TmLam _ then "fun" else "var" in
        let newname = strJoin "" [prefix, int2string id, "_", name] in
        let newstate = st_incrId (st_addToEnv (name, TmVar newname) acc.0) in
        (newstate, concat (acc.1) [(newname, tpe, body)], concat acc.2 [(newname, TmVar newname)])
      in
      let replaceret = foldl replacenames (state, [], []) bindings in

      let repnames = replaceret.2 in --<-- [(String, Expr)]: All mutually recursive identifiers

      -- Include the newly bound identifiers and clear any externally generated
      -- references.
      let repstate = st_setLambdarefs repnames (st_setExternrefs []
                                               (st_setGenargs [] replaceret.0)) in
      let repbindings = replaceret.1 in

      -- Lift out each individual expression
      --   acc.0: The state that is being updated
      --   acc.1: The let-bindings with lifted bodies
      --   b: A let-binding in the mutually recursive scope
      let liftbindings = lam acc. lam b.
        let name = b.0 in
        let tpe = b.1 in
        let body = b.2 in
        let acc_state = acc.0 in
        let acc_bindings = acc.1 in

        -- Extract the generated arguments and add them to the environment.
        -- (We do not want to generate 2 separate arguments for the same reference)
        let var2str = lam v. match v with TmVar s then s else error "Not a var" in

        let envaddfld = lam st. lam v. st_addToEnv (strip_prefix (var2str v), v) st in
        let newstate = foldl envaddfld acc_state (st_genargs acc_state) in

        let ret = lamlift newstate (TmLamChain body) in

        -- Update the state to get rid of any local variable declarations.
        -- (We still keep generated arguments and external references)
        (st_setEnv (st_env acc_state) ret.0, concat acc_bindings [(name, None, ret.1)])
      in
      let liftedreclets = foldl liftbindings (repstate, []) repbindings in

      -- (Invariant: The liftedstate contains syncronized sequences of both
      --             external references and their generated arguments.)
      let liftedstate = liftedreclets.0 in
      let liftedbindings = liftedreclets.1 in

      -- Generate arguments that were externally referenced in the expressions.
      let arggen = lam b.
        let name = b.0 in
        let body = b.2 in

        -- The top level definition: TmTopRecDef [("fun#_<name>", Option, TmLam ("arg#_%%", None, ...))]
        let lambdagenerator = lam e. lam acc. match e with TmVar t2 then (TmLam (t2, None, acc)) else let _ = dprint e in error "\ninternal error (3)" in
        let newbody = foldr lambdagenerator body (st_genargs liftedstate) in
        (name, None, newbody)
      in
      let arggenbindings = map arggen liftedbindings in

      -- Add the new arguments to the old environment with proper arguments applied
      let envgen = lam accstate. lam b.
        let name = b.0 in
        let oldname = strip_prefix name in

        -- The value to bind: TmApp (... TmApp (TmVar "fun#_<name>", Expr), ...)
        let binding = foldl (lam acc. lam e. TmApp (acc, e)) (TmVar name) (st_externrefs liftedstate) in

        st_addToEnv (oldname, binding) accstate
      in
      let envstate = foldl envgen (st_setId (st_id liftedstate) state) liftedbindings in

      -- Replace all internal occurrences with the newly bound values
      let appgen = lam acc. lam b.
        let name = b.0 in

        -- The value to bind: TmApp (... TmApp (TmVar "fun#_<name>", Expr), ...)
        let binding = foldl (lam acc. lam e. TmApp (acc, e)) (TmVar name) (st_genargs liftedstate) in

        concat acc [(name, binding)]
      in
      let applist = foldl appgen [] liftedbindings in
      let appgenbindings = map (lam b. (b.0, b.1, lamliftReplaceIdentifiers applist b.2)) arggenbindings in

      -- Return a TmRecLets with the defines
      let finalstate = st_addGlobaldef (TmTopRecDef appgenbindings) envstate in

      lamlift finalstate inexpr

    sem lamliftReplaceIdentifiers (newnames : [(String, Expr)]) =
    | TmRecLets t -> TmRecLets (
                       map (lam e. lamliftReplaceIdentifiers newnames e.2) t.0,
                       lamliftReplaceIdentifiers newnames t.1
                     )
end

lang ConstLamlift = ConstAst
    sem lamlift (state : StateTuple) =
    | TmConst c -> (state, TmConst c)

    sem lamliftReplaceIdentifiers (newnames : [(String, Expr)]) =
    | TmConst c -> TmConst c
end

lang UnitLamlift = UnitAst
    --sem lamlift (state : StateTuple) =
    --| CUnit -> (state, CUnit)
end

lang IntLamlift = IntAst

lang ArithIntLamlift = ArithIntAst + ConstLamlift
    --sem lamlift (state : StateTuple) =
    --| CAddi -> (state, CAddi)
end

lang BoolLamlift = BoolAst + ConstLamlift
    sem lamlift (state : StateTuple) =
    --| CBool b -> (state, CBool b)
    --| CNot -> (state, CNot)
    --| CAnd -> (state, CAnd)
    --| COr -> (state, COr)
    | TmIf t ->
      let cond = t.0 in
      let thn = t.1 in
      let els = t.2 in

      let condret = lamlift state cond in
      let condstate = st_setEnv (st_env state) condret.0 in

      let thnret = lamlift condstate thn in
      let thnstate = st_setEnv (st_env state) thnret.0 in

      let elsret = lamlift thnstate els in
      let elsstate = st_setEnv (st_env state) elsret.0 in

      (elsstate, TmIf (condret.1, thnret.1, elsret.1))

    sem lamliftReplaceIdentifiers (newnames : [(String, Expr)]) =
    | TmIf t -> TmIf (lamliftReplaceIdentifiers newnames t.0,
                      lamliftReplaceIdentifiers newnames t.1,
                      lamliftReplaceIdentifiers newnames t.2)
end

lang CmpLamlift = CmpAst + ConstLamlift
    --sem lamlift (state : StateTuple) =
    --| CEqi -> (state, CEqi)
end

lang SeqLamlift = SeqAst + ConstLamlift
    sem lamlift (state : StateTuple) =
    --| CSeq tms -> (state, CSeq tms)
    --| CNth -> (state, CNth)
    | TmSeq tms ->
      let foldfun = lam acc. lam e.
        let accstate = acc.0 in
        let acclist = acc.1 in

        let eret = lamlift accstate e in

        let newstate = st_setEnv (st_env accstate) eret.0 in
        let newlist = concat acclist [eret.1] in -- this is clumsy, perhaps use foldr?
        (newstate, newlist)
      in
      let foldret = foldl foldfun (state, []) tms in

      let foldstate = st_setEnv (st_env state) foldret.0 in
      let vs = foldret.1 in

      -- Returning a TmSeq since we do not know if the contained terms are
      -- constant or not.
      (foldstate, TmSeq vs)

    sem lamliftReplaceIdentifiers (newnames : [(String, Expr)]) =
    | TmSeq tms ->
      let res = map (lam e. lamliftReplaceIdentifiers newnames e) in
      TmSeq res
end

lang TupleLamlift = TupleAst
    sem lamlift (state : StateTuple) =
    | TmTuple tms ->
      -- This works just like TmSeq at the moment, copied from there.
      let foldfun = lam acc. lam e.
        let accstate = acc.0 in
        let acclist = acc.1 in

        let eret = lamlift accstate e in

        let newstate = st_setEnv (st_env accstate) eret.0 in
        let newlist = concat acclist [eret.1] in
        (newstate, newlist)
      in
      let foldret = foldl foldfun (state, []) tms in

      let foldstate = st_setEnv (st_env state) foldret.0 in
      let vs = foldret.1 in

      (foldstate, TmTuple vs)

    | TmProj t ->
      let tup = t.0 in
      let idx = t.1 in
      let tupret = lamlift state tup in
      let tupstate = st_setEnv (st_env state) tupret.0 in
      let idxret = lamlift tupstate idx in
      let idxstate = st_setEnv (st_env state) idxret.0 in
      (idxstate, TmProj (tupstate.1, idxstate.1))

    sem lamliftReplaceIdentifiers (newnames : [(String, Expr)]) =
    | TmTuple tms ->
      let res = map (lam e. lamliftReplaceIdentifiers newnames e) in
      TmTuple res
end

lang DataLamlift = VarAst + DataAst
    sem lamlift (state : StateTuple) =
    | TmConDef t ->
      let k = t.0 in
      let body = t.1 in

      -- TODO: Double check if this really is the correct environment mapping!
      let updatedstate = st_addToEnv (k, TmVar k) state in
      
      let bodyret = lamlift updatedstate body in
      let bodystate = st_setEnv (st_env state) bodyret.0 in

      (bodystate, TmConDef (k, bodyret.1))

    sem lamliftReplaceIdentifiers (newnames : [(String, Expr)]) =
    | TmConDef t -> TmConDef (t.0, lamliftReplaceIdentifiers newnames t.1)
end

lang MatchLamlift = MatchAst
    sem lamlift (state : StateTuple) =
    | TmMatch t ->
      let target = t.0 in
      let k2 = t.1 in
      let x = t.2 in
      let thn = t.3 in
      let els = t.4 in

      let targetret = lamlift state target in
      let targetstate = st_setEnv (st_env state) targetret.0 in

      let thnret = lamlift targetstate thn in
      let thnstate = st_setEnv (st_env state) thnret.0 in

      let elsret = lamlift thnstate els in
      let elsstate = st_setEnv (st_env state) elsret.0 in
      
      (elsstate, TmMatch (targetret.1, k2, x, thnret.1, elsret.1))

    sem lamliftReplaceIdentifiers (newnames : [(String, Expr)]) =
    | TmMatch t -> TmMatch (lamliftReplaceIdentifiers newnames t.0,
                            t.1, t.2,
                            lamliftReplaceIdentifiers newnames t.3,
                            lamliftReplaceIdentifiers newnames t.4)
end

lang UtestLamlift = UtestAst
    sem lamlift (state : StateTuple) =
    | TmUtest t ->
      let test = t.0 in
      let expected = t.1 in
      let next = t.2 in

      let testret = lamlift state test in
      let teststate = st_setEnv (st_env state) testret.0 in

      let expectedret = lamlift teststate expected in
      let expectedstate = st_setEnv (st_env state) expectedret.0 in

      let nextret = lamlift expectedstate next in
      let nextstate = st_setEnv (st_env state) nextret.0 in

      (nextstate, TmUtest (testret.1, expectedret.1, nextret.1))

    sem lamliftReplaceIdentifiers (newnames : [(String, Expr)]) =
    | TmUtest t -> TmUtest (lamliftReplaceIdentifiers newnames t.0,
                            lamliftReplaceIdentifiers newnames t.1,
                            lamliftReplaceIdentifiers newnames t.2)
end

lang MExprLamlift = TopDef + VarLamlift + AppLamlift + FunLamlift +
                    LetLamlift + RecLetsLamlift + ConstLamlift +
                    UnitLamlift + IntLamlift + ArithIntLamlift +
                    BoolLamlift + CmpLamlift + SeqLamlift +
                    TupleLamlift + DataLamlift + MatchLamlift +
                    UtestLamlift

lang MExprLamliftAndPP = MExprLamlift + MExprPrettyPrint

mexpr
use MExprLamliftAndPP in

-- Lifts out the lambdas, returning a new AST with all lambdas on the top
-- level.
let lift_lambdas: Expr -> Expr = lam ast.
    let builtin_env = [("addi", TmConst (CAddi ())), ("not", TmConst (CNot ())), ("and", TmConst (CAnd ())),
                       ("or", TmConst (COr ())), ("eqi", TmConst (CEqi ())), ("nth", TmConst (CNth ())),
                       ("subi", TmConst (CSubi ()))]
    in

    let initstate: StateTuple = (0, [], builtin_env, [], [], []) in

    let liftret = lamlift initstate ast in

    let mainexpr = liftret.1 in
    let liftedexprs = st_globaldefs (liftret.0) in

    -- liftedexprs is in reverse order, so the let-expression that should be
    -- first is at the end of the list
    let convert_from_globaldef = lam acc. lam gd.
        match gd with TmTopDef t then
            let ident = t.0 in
            let tpe = t.1 in
            let body = t.2 in
            TmLet (ident, tpe, body, acc)
        else match gd with TmTopRecDef t then
            TmRecLets (t, acc)
        else
            error "Global definition is not of TmTopDef"
    in
    foldl convert_from_globaldef mainexpr liftedexprs
in

let example_ast =
    TmLet ("foo", None,
      TmLam ("a", None, TmLam ("b", None,
        TmLet ("bar", None,
          TmLam ("x", None,
            TmApp (
              TmApp (
                TmVar "addi",
                TmVar "b"
              ),
              TmVar "x"
            )
          ),
          TmLet ("fun4_bar", None,
            TmConst (CInt 3),
            TmApp (
              TmApp (
                TmVar "addi",
                TmApp (
                  TmVar "bar",
                  TmVar "fun4_bar"
                )
              ),
              TmVar "a"
            )
          )
        )
      )),
      TmConst (CUnit ())
    )
in

let example_nested_ast =
    TmLet ("foo", None,
      TmLam ("a", None, TmLam ("b", None,
        TmLet ("bar", None,
          TmLam ("x", None,
            TmLet ("babar", None,
              TmLam ("x", None,
                TmApp (
                  TmApp (
                    TmVar "addi",
                    TmVar "b"
                  ),
                  TmVar "x"
                )
              ),
              TmApp (
                TmVar "babar",
                TmVar "x"
              )
            )
          ),
          TmLet ("fun4_bar", None,
            TmConst (CInt 3),
            TmApp (
              TmApp (
                TmVar "addi",
                TmApp (
                  TmVar "bar",
                  TmVar "fun4_bar"
                )
              ),
              TmVar "a"
            )
          )
        )
      )),
      TmConst (CUnit ())
    )
in

let example_recursive_ast =
  TmLet ("foo", None,
    TmLam ("x", None,
      TmRecLets ([
          ("bar", None,
            TmLam ("y", None,
              TmApp (TmApp (TmVar "addi", TmVar "y"), TmVar "x")
            )
          ),
          ("babar", None,
            TmLam ("a", None,
              TmApp (TmVar "bar", TmVar "a")
            )
          )
        ],
        TmApp (TmVar "babar", TmConst (CInt 36))
      )
    ),
    TmConst (CUnit ())
  )
in

let example_factorial =
  TmRecLets ([
      ("factorial", None,
        TmLam ("n", None,
          TmIf (
            TmApp (
              TmApp (
                TmVar "eqi",
                TmVar "n"
              ),
              TmConst (CInt 0)
            ),
            TmConst (CInt 1),
            TmApp (
              TmVar "factorial",
              TmApp (
                TmApp (
                  TmVar "subi",
                  TmVar "n"
                ),
                TmConst (CInt 1)
              )
            )
          )
        )
      )
    ],
    TmConst (CUnit ())
  )
in

--utest lift_lambdas (TmConst CUnit) with (TmConst (CUnit)) in
--utest lift_lambdas example_ast with TmConst (CUnit) in

let _ =
    --use MExprLamliftAndPP in
    let _ = print "\n[>>>>  Before  <<<<]\n" in
    --let _ = dprint example_recursive_ast in
    let _ = print (pprintCode 0 example_recursive_ast) in
    let _ = print "\n" in
    ()
in

let _ =
    --use MExprLamliftAndPP in
    let _ = print "\n[>>>>  After  <<<<]\n" in
    let _ = print (pprintCode 0 (lift_lambdas example_recursive_ast)) in
    let _ = print "\n" in
    ()
in

()
