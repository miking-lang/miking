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
        localVars : Int, -- number of local vars on the JVM
        classes : [Class]
    }

    sem wrapPrimitive : String -> [Bytecode]
    sem wrapPrimitive =
    | "I" -> [invokestatic_ "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;"]
    | a -> []

    sem unwrapPrimitive : String -> [Bytecode]
    sem unwrapPrimitive = 
    | "I" -> [checkcast_ "java/lang/Integer", invokevirtual_ "java/lang/Integer" "intValue" "()I"]
    | a -> []

    -- callConstructor var?

    -- go through AST and translate to JVM bytecode

    sem toJSONExpr : JVMEnv -> Expr -> JVMEnv
    sem toJSONExpr env =
    | TmSeq { tms = tms } -> { env with bytecode = concat env.bytecode [ldcString_ (_charSeq2String tms)]} -- only for strings now
    | TmConst { val = val } -> 
        let bc = (match val with CInt { val = val } then [ldcInt_ val, invokestatic_ "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;"]
        else never)
        in { env with bytecode = concat env.bytecode bc }
    | TmApp { lhs = lhs, rhs = rhs, ty = ty } ->
        let to = ty in 
        let arg = toJSONExpr { env with bytecode = [], classes = [] } rhs in
        match lhs with TmConst { val = CPrint _ } then
            { env with bytecode = foldl concat env.bytecode [[getstatic_ "java/lang/System" "out" "Ljava/io/PrintStream;"], arg.bytecode, [invokevirtual_ "java/io/PrintStream" "print" "(Ljava/lang/String;)V"]], classes = concat env.classes arg.classes }
        else match lhs with TmConst { val = CAddi _ } then 
            let className = createName_ "Func" in
            let freeVar = "var" in
            let varTy = "Ljava/lang/Integer;" in
            let add = createClass className "pkg/Function" [createField freeVar varTy] defaultConstructor [createFunction "apply" "(Ljava/lang/Object;)Ljava/lang/Object;" (foldl concat [aload_ 1] [unwrapPrimitive "I", [aload_ 0, getfield_ (concat "pkg/" className) freeVar varTy], unwrapPrimitive "I", [iadd_], wrapPrimitive "I", [areturn_]])] in
            let res = { env with classes = snoc (concat env.classes arg.classes) add, bytecode = foldl concat env.bytecode [[new_ (concat "pkg/" className), dup_, invokespecial_ (concat "pkg/" className) "<init>" "()V", dup_], arg.bytecode, [checkcast_ "java/lang/Integer", putfield_ (concat "pkg/" className) freeVar varTy]] } in
            res            
        else
            let fun = toJSONExpr env lhs in 
            { fun with bytecode = foldl concat fun.bytecode [arg.bytecode, [invokeinterface_ "pkg/Function" "apply" "(Ljava/lang/Object;)Ljava/lang/Object;"]], classes = concat fun.classes arg.classes }
    | TmLet { ident = ident, body = body, inexpr = inexpr, tyBody = tyBody } -> 
        let b = toJSONExpr env body in
        let bodyJSONExpr = { b with bytecode = snoc b.bytecode (astore_ env.localVars), localVars = addi 1 env.localVars, vars = mapInsert ident env.localVars env.vars } in
        toJSONExpr bodyJSONExpr inexpr 
    --| TmLam { ident = ident, body = body } ->
    | TmVar { ident = ident } -> 
        let store = (match mapLookup ident env.vars with Some i then
            [aload_ i]
        else
            (print "No identifier!\n");
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
    let env = { bytecode = [], vars = mapEmpty nameCmp, localVars = 1, classes = [] } in
    let compiledEnv = (toJSONExpr env ast) in
    --let bytecode = concat compiledEnv.bytecode [return_] in
    --let bytecode = concat compiledEnv.bytecode [pop_, return_] in
    -- see result
    let bytecode = concat compiledEnv.bytecode [astore_ env.localVars, getstatic_ "java/lang/System" "out" "Ljava/io/PrintStream;", aload_ env.localVars, invokevirtual_ "java/io/PrintStream" "print" "(Ljava/lang/Object;)V", return_] in -- should not print out result!
    let mainFunc = createFunction "main" "([Ljava/lang/String;)V" bytecode in 
    let prog = createProg "pkg/" (snoc compiledEnv.classes (createClass "Hello" "" [] defaultConstructor [mainFunc])) [objToObj] in

    (print (toStringProg prog));
    "aaa"
