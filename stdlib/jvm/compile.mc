include "mexpr/ast.mc"
include "string.mc"
include "jvm/ast.mc"
include "javascript/util.mc"
include "seq.mc"
include "pmexpr/utils.mc"
include "jvm/constants.mc"

lang MExprJVMCompile = MExprAst + JVMAst

    type JVMEnv = {
        bytecode : [Bytecode],
        vars : Map Name Int, 
        fieldVars : Map Name Field,
        localVars : Int, -- number of local vars on the JVM
        classes : [Class],
        name : String,
        nextClass : String
    }

    sem wrapPrimitive : String -> [Bytecode]
    sem wrapPrimitive =
    | "I" -> wrapInteger_
    | "F" -> wrapFloat_
    | a -> []

    sem unwrapPrimitive : String -> [Bytecode]
    sem unwrapPrimitive = 
    | "I" -> unwrapInteger_
    | "F" -> unwrapFloat_
    | a -> []

    -- callConstructor var?

    -- go through AST and translate to JVM bytecode

    sem toJSONExpr : JVMEnv -> Expr -> JVMEnv
    sem toJSONExpr env =
    | TmSeq { tms = tms } -> { env with bytecode = concat env.bytecode [ldcString_ (_charSeq2String tms)]} -- only for strings now
    | TmConst { val = val } -> 
        let bc = (match val with CInt { val = val } then 
            concat [ldcInt_ val] wrapInteger_
        else match val with CFloat { val = val } then
            concat [ldcFloat_ val] wrapFloat_ 
        else match val with CBool { val = val } then 
            match val with true then
                concat [ldcInt_ 1] wrapBoolean_
            else 
                concat [ldcInt_ 0] wrapBoolean_
        else never)
        in { env with bytecode = concat env.bytecode bc }
    | TmApp { lhs = lhs, rhs = rhs, ty = ty } ->
        let to = ty in 
        let arg = toJSONExpr { env with bytecode = [], classes = [] } rhs in
        match lhs with TmConst _ then 
            match lhs with TmConst { val = CPrint _ } then
                { env with 
                    bytecode = foldl concat env.bytecode 
                        [[getstatic_ "java/lang/System" "out" "Ljava/io/PrintStream;"], 
                        arg.bytecode, 
                        [invokevirtual_ "java/io/PrintStream" "print" "(Ljava/lang/String;)V"],
                        [ldcInt_ 1],
                        wrapInteger_], -- change this to () later 
                    classes = concat env.classes arg.classes }
            else match lhs with TmConst { val = CAddi _ } then 
                applyArithI_ "Addi" env arg.bytecode 
            else match lhs with TmConst { val = CSubi _ } then 
                applyArithI_ "Subi" env arg.bytecode
            else match lhs with TmConst { val = CMuli _ } then 
                applyArithI_ "Muli" env arg.bytecode
            else match lhs with TmConst { val = CDivi _ } then 
                applyArithI_ "Divi" env arg.bytecode
            else match lhs with TmConst { val = CModi _ } then 
                applyArithI_ "Modi" env arg.bytecode
            else match lhs with TmConst { val = CAddf _ } then 
                applyArithF_ "Addf" env arg.bytecode 
            else match lhs with TmConst { val = CSubf _ } then 
                applyArithF_ "Subf" env arg.bytecode
            else match lhs with TmConst { val = CMulf _ } then 
                applyArithF_ "Mulf" env arg.bytecode
            else match lhs with TmConst { val = CDivf _ } then 
                applyArithF_ "Divf" env arg.bytecode
            else match lhs with TmConst { val = CNegf _ } then
                { env with 
                    bytecode = foldl concat env.bytecode 
                        [arg.bytecode,
                        unwrapFloat_,
                        [fneg_],
                        wrapFloat_], 
                    classes = concat env.classes arg.classes }
            else match lhs with TmConst { val = CNegi _ } then
                { env with 
                    bytecode = foldl concat env.bytecode 
                        [arg.bytecode,
                        unwrapInteger_,
                        [ineg_],
                        wrapInteger_], 
                    classes = concat env.classes arg.classes }
            else 
                (print "Unknown Const!\n");
                env
        else
            let fun = toJSONExpr env lhs in 
            { fun with 
                bytecode = foldl concat fun.bytecode 
                    [arg.bytecode, 
                    [checkcast_ object_T],
                    [invokeinterface_ (concat pkg_ "Function") "apply" "(Ljava/lang/Object;)Ljava/lang/Object;"]], 
                    classes = concat fun.classes arg.classes }
    | TmLet { ident = ident, body = body, inexpr = inexpr, tyBody = tyBody } -> 
        let b = toJSONExpr { env with fieldVars = mapEmpty nameCmp } body in
        toJSONExpr { b with 
                        bytecode = snoc b.bytecode (astore_ env.localVars), 
                        fieldVars = mapEmpty nameCmp, 
                        localVars = addi 1 env.localVars, 
                        vars = mapInsert ident env.localVars env.vars } inexpr
    | TmLam { ident = ident, body = body } ->
        let className = env.nextClass in
        let newField = (createField (nameGetStr ident) object_LT) in
        let nextClass = createName_ "Func" in
        let bodyEnv = toJSONExpr { env with bytecode = [], name = className, nextClass = nextClass, localVars = 2, vars = mapInsert ident 1 (mapEmpty nameCmp), fieldVars = mapInsert ident newField env.fieldVars } body in 
        let fields = map (lam x. x.1) (mapToSeq env.fieldVars) in
        match body with TmLam _ then
            let putfields = join (mapi (lam i. lam x. [aload_ 0, getfield_ (concat pkg_ className) (getNameField x) object_LT, putfield_ (concat pkg_ nextClass) (getNameField x) object_LT]) fields) in
            let dups = map (lam x. dup_) fields in
            let apply = apply_ (foldl concat bodyEnv.bytecode [dups, [dup_, aload_ 1, putfield_ (concat pkg_ nextClass) (nameGetStr ident) object_LT], putfields]) in
            let funcClass = createClass className (concat pkg_ "Function") (snoc fields newField) defaultConstructor [apply] in
            { env with 
                classes = snoc bodyEnv.classes funcClass,
                bytecode = foldl concat env.bytecode [initClass_ className],
                nextClass = bodyEnv.nextClass }
        else 
            let apply = apply_ bodyEnv.bytecode in
            let funcClass = createClass className (concat pkg_ "Function") fields defaultConstructor [apply] in
            { env with 
                classes = snoc bodyEnv.classes funcClass,
                bytecode = foldl concat env.bytecode [initClass_ className],
                nextClass = bodyEnv.nextClass }
    | TmVar { ident = ident } -> 
        let store = (match mapLookup ident env.vars with Some i then
            [aload_ i]
        else match mapLookup ident env.fieldVars with Some field then 
            -- do fieldlookup
            [aload_ 0, getfield_ (concat pkg_ env.name) (getNameField field) "Ljava/lang/Object;"]
        else
            (print (join ["No identifier! ", nameGetStr ident, "\n"]));
            []) in
        { env with bytecode = concat env.bytecode store }
    | a -> 
        (print "unknown expr\n");
        env


    sem getJavaType : Type -> String
    sem getJavaType =
    | TyInt _ -> "I"
    | a -> ""

    sem toJSONConst : JVMEnv -> Const -> JVMEnv
    sem toJSONConst env =
    | a -> 
        (print "unknown const\n");
        env

end

let compileMCoreToJVM = lam ast. 
    use MExprJVMCompile in
    let objToObj = createInterface "Function" [] [createFunction "apply" "(Ljava/lang/Object;)Ljava/lang/Object;" []] in 
    let env = { bytecode = [], vars = mapEmpty nameCmp, localVars = 1, classes = [], fieldVars = mapEmpty nameCmp, name = "Main", nextClass = createName_ "Func" } in
    let compiledEnv = (toJSONExpr env ast) in
    --let bytecode = concat compiledEnv.bytecode [pop_, return_] in
    -- see result
    let bytecode = concat compiledEnv.bytecode [astore_ env.localVars, getstatic_ "java/lang/System" "out" "Ljava/io/PrintStream;", aload_ env.localVars, invokevirtual_ "java/io/PrintStream" "print" "(Ljava/lang/Object;)V", return_] in -- should not print out result!
    let mainFunc = createFunction "main" "([Ljava/lang/String;)V" bytecode in 
    let constClasses = [addiClass_, subiClass_, muliClass_, diviClass_, modiClass_] in
    let prog = createProg pkg_ (snoc (concat compiledEnv.classes constClasses) (createClass "Hello" "" [] defaultConstructor [mainFunc])) [objToObj] in

    (print (toStringProg prog));
    "aaa"
